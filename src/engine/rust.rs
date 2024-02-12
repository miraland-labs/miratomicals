// std
use std::{
	ops::Range,
	path::Path,
	str::FromStr,
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc, Mutex,
	},
	thread::{self, JoinHandle},
};
// crates.io
use bitcoin::{
	absolute::LockTime,
	consensus::encode,
	hashes::Hash,
	key::TapTweak,
	psbt::Input,
	secp256k1::{All, Keypair, Message, Secp256k1, XOnlyPublicKey},
	sighash::{Prevouts, SighashCache},
	taproot::{LeafVersion, Signature, TapLeafHash, TaprootBuilder, TaprootSpendInfo},
	transaction::Version,
	Address, Amount, Network, OutPoint, Psbt, ScriptBuf, Sequence, TapSighashType, Transaction,
	TxIn, TxOut, Witness,
};
use serde::Serialize;
use tokio::time;

// atomicalsir
use crate::{
	prelude::*,
	util::{self, FeeBound},
	wallet::Wallet as RawWallet,
};
use atomicals_electrumx::{r#type::Utxo, Api, ElectrumX, ElectrumXBuilder};

pub async fn run(
	num_threads: u16,
	network: Network,
	fee_bound: &FeeBound,
	electrumx: &str,
	wallet_dir: &Path,
	ticker: &str,
	current: bool,
) -> Result<()> {
	let m = MinerBuilder { num_threads, network, fee_bound, electrumx, wallet_dir, ticker, current }.build()?;

	#[allow(clippy::never_loop)]
	loop {
		for w in &m.wallets {
			m.mine(w).await?;

			// Test only.
			// return Ok(());
		}
	}
}

#[derive(Debug)]
struct Miner {
	num_threads: u16,
	network: Network,
	fee_bound: FeeBound,
	api: ElectrumX,
	wallets: Vec<Wallet>,
	ticker: String,
	current: bool,
}
impl Miner {
	const BASE_BYTES: f64 = 10.5;
	const INPUT_BYTES_BASE: f64 = 57.5;
	const LOCK_TIME: LockTime = LockTime::ZERO;
	// <8 bytes output amount value> + <1 byte len of following script> + <1 byte OP_RETURN(0x6a)>
	// + <1 byte len indicating the rest> + <10 byte unix_timestamp> + <1 byte for colon separator(:)>
	// + <8 bytes nonce, roughly estimation>
	// 8 + 1 + 1 + 1 + 10 + 1 + 8 = 30 bytes
	// actual op_return output size is determined precisely by final nonce
	const OP_RETURN_BYTES: f64 = 21. + 8. + 1.;
	const OUTPUT_BYTES_BASE: f64 = 43.;
	const REVEAL_INPUT_BYTES_BASE: f64 = 66.;
	const VERSION: Version = Version::ONE;

	async fn mine(&self, wallet: &Wallet) -> Result<()> {
		let d = self.prepare_data(wallet).await?;

		tracing::info!("attempt to find a solution based on {d:#?}");

		let Data {
			secp,
			satsbyte,
			bitworkc,
			bitworkr,
			additional_outputs,
			reveal_script,
			reveal_spend_info,
			fees,
			funding_utxo,
		} = d.clone();
		let reveal_spk = ScriptBuf::new_p2tr(
			&secp,
			reveal_spend_info.internal_key(),
			reveal_spend_info.merkle_root(),
		);
		let funding_spk = wallet.funding.address.script_pubkey();
		let commit_input = vec![TxIn {
			previous_output: OutPoint::new(funding_utxo.txid.parse()?, funding_utxo.vout),
			..Default::default()
		}];
		let commit_output = {
			let spend = TxOut {
				value: Amount::from_sat(fees.reveal_and_outputs),
				script_pubkey: reveal_spk.clone(),
			};
			let refund = {
				let r = funding_utxo.value.saturating_sub(fees.reveal_and_outputs).saturating_sub(
					fees.commit + (Self::OUTPUT_BYTES_BASE * satsbyte as f64).floor() as u64,
				);

				if r > 0 {
					Some(TxOut { value: Amount::from_sat(r), script_pubkey: funding_spk.clone() })
				} else {
					None
				}
			};

			if let Some(r) = refund {
				vec![spend, r]
			} else {
				vec![spend]
			}
		};
		let commit_prevouts = [TxOut {
			value: Amount::from_sat(funding_utxo.value),
			script_pubkey: funding_spk.clone(),
		}];
		let time = util::time();
		tracing::info!("Starting commit stage mining now...");
		tracing::info!("Concurrency set to: {}", self.num_threads);
		let commit_tx = WorkerPool::new("commit", bitworkc.unwrap(), self.num_threads)
			.activate(
				(
					secp.clone(),
					wallet.funding.pair.tap_tweak(&secp, None).to_inner(),
					wallet.funding.x_only_public_key,
					commit_input.clone(),
					commit_output.clone(),
					commit_prevouts.clone(),
				),
				time,
				|(secp, signer, signer_xpk, input, output, prevouts), _t, s| {
					let mut psbt = Psbt::from_unsigned_tx(Transaction {
						version: Self::VERSION,
						lock_time: Self::LOCK_TIME,
						input: {
							let mut i = input.to_owned();

							i[0].sequence = Sequence(s);

							i
						},
						output: output.to_owned(),
					})?;

					sign_commit_psbt(secp, signer, signer_xpk, &mut psbt, prevouts)?;

					Ok(psbt.extract_tx_unchecked_fee_rate())
				},
			)?
			.result();

		let commit_txid = commit_tx.txid();
		let commit_tx_hex = encode::serialize_hex(&commit_tx);
		tracing::info!("broadcasting commit transaction {commit_txid}");
		tracing::debug!("{commit_tx:#?}");
		tracing::info!("raw tx: {commit_tx_hex}");

		let mut sent_success = false;
		for _ in self.api.max_retries.clone() {
			match self.api.broadcast(commit_tx_hex.clone()).await {
				Ok(_) =>  {
					sent_success = true;
					tracing::info!("Successfully sent commit tx {commit_txid}");
					break;
				}
				Err(_) => {
					tracing::error!("Network error, will retry to broadcast commit transaction in {} seconds...", self.api.retry_period.as_secs());
					time::sleep(self.api.retry_period).await;
				}
			}
		}

		if !sent_success {
			tracing::error!("❌ Failed to send commit tx {commit_txid}");
			return Ok(());
		}
		// tracing::info!("Commit workers have completed their tasks for the commit transaction.");

		let commit_txid_ = self
			.api
			.wait_until_utxo(
				Address::from_script(&reveal_spk, self.network)?.to_string(),
				fees.reveal_and_outputs,
			)
			.await?
			.txid;

		assert_eq!(commit_txid, commit_txid_.parse()?);

		let mut reveal_psbt = Psbt::from_unsigned_tx(Transaction {
			version: Self::VERSION,
			lock_time: Self::LOCK_TIME,
			input: vec![TxIn {
				previous_output: OutPoint::new(commit_txid, 0),
				sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
				..Default::default()
			}],
			output: additional_outputs,
		})?;
		let reveal_lh = reveal_script.tapscript_leaf_hash();
		let reveal_tx = if let Some(bitworkr) = bitworkr {
			let time = util::time();

			tracing::info!("Starting reveal stage mining now...");
			tracing::info!("Concurrency set to: {}", self.num_threads);
			// TODO: Update time after attempting all sequences.
			WorkerPool::new("reveal", bitworkr, self.num_threads)
				.activate(
					(
						secp.clone(),
						wallet.funding.pair,
						reveal_script.clone(),
						reveal_spend_info.clone(),
						commit_output[0].clone(),
						reveal_psbt.clone(),
					),
					time,
					move |(secp, signer, script, spend_info, output, psbt), t, s| {
						let mut psbt = psbt.to_owned();

						psbt.unsigned_tx.output.push(TxOut {
							value: Amount::ZERO,
							script_pubkey: util::time_nonce_script(t, s),
						});
						psbt.outputs.push(Default::default());

						sign_reveal_psbt(
							secp, signer, &mut psbt, output, &reveal_lh, spend_info, script,
						)?;

						Ok(psbt.extract_tx_unchecked_fee_rate())
					},
				)?
				.result()
		} else {
			// Has no bitworkr
			sign_reveal_psbt(
				&secp,
				&wallet.funding.pair,
				&mut reveal_psbt,
				&commit_output[0],
				&reveal_lh,
				&reveal_spend_info,
				&reveal_script,
			)?;

			// Remove this clone if not needed in the future.
			reveal_psbt.clone().extract_tx_unchecked_fee_rate()
		};

		let reveal_txid = reveal_tx.txid();
		let reveal_tx_hex = encode::serialize_hex(&reveal_tx);

		tracing::info!("broadcasting reveal transaction {reveal_txid}");
		tracing::debug!("{reveal_tx:#?}");
		tracing::info!("raw tx: {reveal_tx_hex}");

		let mut sent_success = false;
		for _ in self.api.max_retries.clone() {
			match self.api.broadcast(reveal_tx_hex.clone()).await {
				Ok(_) =>  {
					sent_success = true;
					tracing::info!("✅ Successfully sent reveal tx {reveal_txid}");
					break;
				}
				Err(_) => {
					tracing::error!("Network error, will retry to broadcast reveal transaction in {} seconds...", self.api.retry_period.as_secs());
					time::sleep(self.api.retry_period).await;
				}
			}
		}

		if !sent_success {
			tracing::error!("❌ Failed to send reveal tx {reveal_txid}");
			tracing::info!("Store the reveal tx in cache for inspection later");

			util::cache(
				reveal_txid.to_string(),
				format!("{reveal_tx_hex}\n{reveal_psbt:?}\n{reveal_tx:?}"),
			)?;

			return Ok(());
		}
		// tracing::info!("Reveal workers have completed their tasks for the reveal transaction.");
		// tracing::info!("✅ Successfully sent reveal tx {reveal_txid}");
		tracing::info!("✨Congratulations! Mission completed.✨");

		Ok(())
	}

	async fn prepare_data(&self, wallet: &Wallet) -> Result<Data> {
		let id = self.api.get_by_ticker(&self.ticker).await?.atomical_id;
		let response = self.api.get_ft_info(id).await?;
		let global = response.global.unwrap();
		let ft = response.result;

		if ft.ticker != self.ticker {
			Err(anyhow::anyhow!("ticker mismatch"))?;
		}
		if ft.subtype != "decentralized" {
			Err(anyhow::anyhow!("not decentralized"))?;
		}
		if ft.mint_height > global.height + 1 {
			Err(anyhow::anyhow!("mint height mismatch"))?;
		}
		if ft.mint_amount == 0 || ft.mint_amount >= 100_000_000 {
			Err(anyhow::anyhow!("mint amount mismatch"))?;
		}
		// if ft.dft_info.mint_count >= ft.max_mints {
		// 	Err(anyhow::anyhow!("max mints reached"))?;
		// }
		if ft.dft_info.mint_count >= ft.max_mints {
			if ft.mint_mode == "fixed" {
			    Err(anyhow::anyhow!("max mints reached"))?;
			}
		}

		let secp = Secp256k1::new();
		let satsbyte = if self.network == Network::Bitcoin {
			self.fee_bound.apply(util::query_fee().await? + 5)
		} else {
			2
		};
		let additional_outputs = vec![TxOut {
			value: Amount::from_sat(ft.mint_amount),
			script_pubkey: wallet.stash.address.script_pubkey(),
		}];

		let bitworkc = if ft.mint_bitworkc.is_some() {
			ft.mint_bitworkc.clone()
		} else if self.current {
			ft.dft_info.mint_bitworkc_current.clone()
		} else {
			ft.dft_info.mint_bitworkc_next.clone()
		};

		let bitworkr = if ft.mint_bitworkr.is_some() {
			ft.mint_bitworkr.clone()
		} else if self.current {
			ft.dft_info.mint_bitworkr_current.clone()
		} else {
			ft.dft_info.mint_bitworkr_next.clone()
		};

		let payload = PayloadWrapper {
			args: {
				let (time, nonce) = util::time_nonce();
				tracing::info!("payload time: {time}, payload nonce: {nonce}");
				if ft.mint_mode == "perpetual" || ft.mint_mode == "infinite" {
					tracing::info!("Minting under perpetual/infinite mode, payload bitworkc: {}", bitworkc.clone().unwrap());
				}

				Payload {
					bitworkc: bitworkc.clone(),
					bitworkr: bitworkr.clone(),
					mint_ticker: ft.ticker.clone(),
					nonce,
					time,
				}
			},
		};
		let payload_encoded = util::cbor(&payload)?;
		// TODO: More op types.
		let reveal_script =
			util::build_reval_script(&wallet.funding.x_only_public_key, "dmt", &payload_encoded);
		let reveal_spend_info = TaprootBuilder::new()
			.add_leaf(0, reveal_script.clone())?
			.finalize(&secp, wallet.funding.x_only_public_key)
			.unwrap();
		// let has_bitworkr = if ft.mint_bitworkr.is_some() { true } else { false }; // not correct for perpetual mode
		let has_bitworkr = if bitworkr.is_some() { true } else { false };
		let fees = Self::fees_of(
			satsbyte,
			reveal_script.as_bytes().len(),
			&additional_outputs,
			has_bitworkr,
		);
		let funding_utxo = self
			.api
			.wait_until_utxo(wallet.funding.address.to_string(), fees.commit_and_reveal_and_outputs)
			.await?;

		Ok(Data {
			secp,
			satsbyte,
			bitworkc,
			bitworkr,
			additional_outputs,
			reveal_script,
			reveal_spend_info,
			fees,
			funding_utxo,
		})
	}

	fn fees_of(
		satsbyte: u64,
		reveal_script_len: usize,
		additional_outputs: &[TxOut],
		has_bitworkr: bool,
	) -> Fees {
		let satsbyte = satsbyte as f64;
		let commit = {
			(satsbyte * (Self::BASE_BYTES + Self::INPUT_BYTES_BASE + Self::OUTPUT_BYTES_BASE))
				.ceil() as u64
		};
		let reveal = {
			let compact_input_bytes = if reveal_script_len <= 252 {
				1.
			} else if reveal_script_len <= 0xFFFF {
				3.
			} else if reveal_script_len <= 0xFFFFFFFF {
				5.
			} else {
				9.
			};
			let op_return_bytes = if has_bitworkr { Self::OP_RETURN_BYTES } else { 0. };

			(satsbyte
				* (Self::BASE_BYTES
						+ Self::REVEAL_INPUT_BYTES_BASE
						+ (compact_input_bytes + reveal_script_len as f64) / 4.
						// + utxos.len() as f64 * Self::INPUT_BYTES_BASE
						+ additional_outputs.len() as f64 * Self::OUTPUT_BYTES_BASE
						+ op_return_bytes))
				.ceil() as u64
		};
		let outputs = additional_outputs.iter().map(|o| o.value.to_sat()).sum::<u64>();
		let commit_and_reveal = commit + reveal;
		let commit_and_reveal_and_outputs = commit_and_reveal + outputs;

		// While satsbyte at `150`.
		// Fees {
		// 	commit: 16650,
		// 	commit_and_reveal: 38700,
		// 	commit_and_reveal_and_outputs: 58700,
		// 	reveal: 22050,
		// 	reveal_and_outputs: 42050,
		// };
		Fees {
			commit,
			// commit_and_reveal,
			commit_and_reveal_and_outputs,
			// reveal,
			reveal_and_outputs: reveal + outputs,
		}
	}
}
#[derive(Debug)]
struct MinerBuilder<'a> {
	num_threads: u16,
	network: Network,
	fee_bound: &'a FeeBound,
	electrumx: &'a str,
	wallet_dir: &'a Path,
	ticker: &'a str,
	current: bool,
}
impl<'a> MinerBuilder<'a> {
	fn build(self) -> Result<Miner> {
		let api =
			ElectrumXBuilder::default().network(self.network).base_uri(self.electrumx).build()?;
		let wallets = RawWallet::load_wallets(self.wallet_dir)
			.into_iter()
			.map(|rw| Wallet::from_raw_wallet(rw, self.network))
			.collect::<Result<_>>()?;

		Ok(Miner {
			num_threads: self.num_threads,
			network: self.network,
			fee_bound: self.fee_bound.to_owned(),
			api,
			wallets,
			ticker: self.ticker.into(),
			current: self.current,
		})
	}
}

#[derive(Clone, Debug)]
struct Wallet {
	stash: Key,
	funding: Key,
}
impl Wallet {
	fn from_raw_wallet(raw_wallet: RawWallet, network: Network) -> Result<Self> {
		let s_p = util::keypair_from_wif(&raw_wallet.stash.key.wif)?;
		let f_p = util::keypair_from_wif(&raw_wallet.funding.wif)?;

		Ok(Self {
			stash: Key {
				pair: s_p,
				x_only_public_key: s_p.x_only_public_key().0,
				address: Address::from_str(&raw_wallet.stash.key.address)?
					.require_network(network)?,
			},
			funding: Key {
				pair: f_p,
				x_only_public_key: f_p.x_only_public_key().0,
				address: Address::from_str(&raw_wallet.funding.address)?
					.require_network(network)?,
			},
		})
	}
}

#[derive(Clone, Debug)]
struct Key {
	pair: Keypair,
	x_only_public_key: XOnlyPublicKey,
	address: Address,
}

#[derive(Debug, Serialize)]
pub struct PayloadWrapper {
	pub args: Payload,
}
#[derive(Debug, Serialize)]
pub struct Payload {
	pub bitworkc: Option<String>,
	pub bitworkr: Option<String>,
	pub mint_ticker: String,
	pub nonce: u64,
	pub time: u64,
}

#[derive(Clone, Debug)]
struct Data {
	secp: Secp256k1<All>,
	satsbyte: u64,
	bitworkc: Option<String>,
	bitworkr: Option<String>,
	additional_outputs: Vec<TxOut>,
	reveal_script: ScriptBuf,
	reveal_spend_info: TaprootSpendInfo,
	fees: Fees,
	funding_utxo: Utxo,
}
#[derive(Clone, Debug)]
struct Fees {
	commit: u64,
	// commit_and_reveal: u64,
	commit_and_reveal_and_outputs: u64,
	// reveal: u64,
	reveal_and_outputs: u64,
}

struct WorkerPool {
	task: &'static str,
	num_threads: u16,
	difficulty: String,
	result: Arc<Mutex<Option<Transaction>>>,
}
impl WorkerPool {
	fn new(task: &'static str, difficulty: String, num_threads: u16) -> Self {
		Self { task, difficulty, num_threads, result: Default::default() }
	}

	fn sequence_ranges(&self) -> Vec<Range<u32>> {
		let step = (Sequence::MAX.0 as f32 / self.num_threads as f32).ceil() as u32;
		let mut ranges = Vec::new();
		let mut start = 0;

		while start < Sequence::MAX.0 {
			let end = start.checked_add(step).unwrap_or(Sequence::MAX.0);

			ranges.push(start..end);

			start = end;
		}

		ranges
	}

	fn activate<P, F>(&self, p: P, t: u64, f: F) -> Result<&Self>
	where
		P: 'static + Clone + Send,
		F: 'static + Clone + Send + Fn(&P, u64, u32) -> Result<Transaction>,
	{
		let task = self.task;
		let mut ts = <Vec<JoinHandle<Result<()>>>>::new();
		let exit = Arc::new(AtomicBool::new(false));

		self.sequence_ranges().into_iter().enumerate().for_each(|(i, r)| {
			tracing::info!("spawning {task} worker thread {i} for sequence range {r:?}");

			let p = p.clone();
			let f = f.clone();
			let difficulty = self.difficulty.clone();
			let exit = exit.clone();
			let result = self.result.clone();

			ts.push(thread::spawn(move || {
				for s in r {
					if exit.load(Ordering::Relaxed) {
						return Ok(());
					}

					let tx = f(&p, t, s)?;

					if tx.txid().to_string().trim_start_matches("0x").starts_with(&difficulty) {
						tracing::info!("solution found for {task}");
						// tracing::info!("reveal sequence {s}");
						tracing::info!("solution time: {t}, solution nonce: {s}");

						exit.store(true, Ordering::Relaxed);
						*result.lock().unwrap() = Some(tx);

						return Ok(());
					}
				}

				Ok(())
			}));
		});

		for t in ts {
			t.join().unwrap()?;
		}

		Ok(self)
	}

	// TODO: If no solution found.
	fn result(&self) -> Transaction {
		self.result.lock().unwrap().take().unwrap()
	}
}

fn sign_commit_psbt(
	secp: &Secp256k1<All>,
	signer: &Keypair,
	signer_xpk: &XOnlyPublicKey,
	psbt: &mut Psbt,
	prevouts: &[TxOut],
) -> Result<()> {
	let commit_hty = TapSighashType::Default;
	let tap_key_sig = {
		let h = SighashCache::new(&psbt.unsigned_tx).taproot_key_spend_signature_hash(
			0,
			&Prevouts::All(prevouts),
			commit_hty,
		)?;
		let m = Message::from_digest(h.to_byte_array());

		Signature { sig: secp.sign_schnorr(&m, signer), hash_ty: commit_hty }
	};

	psbt.inputs[0] = Input {
		witness_utxo: Some(prevouts[0].clone()),
		final_script_witness: {
			let mut w = Witness::new();

			w.push(tap_key_sig.to_vec());

			Some(w)
		},
		tap_key_sig: Some(tap_key_sig),
		tap_internal_key: Some(*signer_xpk),
		..Default::default()
	};

	Ok(())
}

fn sign_reveal_psbt(
	secp: &Secp256k1<All>,
	signer: &Keypair,
	psbt: &mut Psbt,
	commit_output: &TxOut,
	reveal_left_hash: &TapLeafHash,
	reveal_spend_info: &TaprootSpendInfo,
	reveal_script: &ScriptBuf,
) -> Result<()> {
	let reveal_hty = TapSighashType::SinglePlusAnyoneCanPay;
	let tap_key_sig = {
		let h = SighashCache::new(&psbt.unsigned_tx).taproot_script_spend_signature_hash(
			0,
			&Prevouts::One(0, commit_output.to_owned()),
			*reveal_left_hash,
			reveal_hty,
		)?;
		let m = Message::from_digest(h.to_byte_array());

		Signature { sig: secp.sign_schnorr(&m, signer), hash_ty: reveal_hty }
	};

	psbt.inputs[0] = Input {
		// TODO: Check.
		witness_utxo: Some(commit_output.to_owned()),
		tap_internal_key: Some(reveal_spend_info.internal_key()),
		tap_merkle_root: reveal_spend_info.merkle_root(),
		final_script_witness: {
			let mut w = Witness::new();

			w.push(tap_key_sig.to_vec());
			w.push(reveal_script.as_bytes());
			w.push(
				reveal_spend_info
					.control_block(&(reveal_script.to_owned(), LeafVersion::TapScript))
					.unwrap()
					.serialize(),
			);

			Some(w)
		},
		..Default::default()
	};

	Ok(())
}
