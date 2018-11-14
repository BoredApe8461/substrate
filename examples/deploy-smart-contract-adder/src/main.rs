extern crate substrate_primitives as primitives;
extern crate hex;
extern crate node_primitives;
extern crate node_runtime;
extern crate sr_primitives as runtime_primitives;
extern crate srml_balances as balances;
extern crate srml_contract as contract;
extern crate parity_codec as codec;

#[macro_use]
extern crate hex_literal;

use std::fmt::Write;
use primitives::hexdisplay::HexDisplay;

use keyring::{self, Keyring};
use primitives::{twox_128, blake2_256, ed25519::{Public, Pair}};
use node_primitives::{AccountId};
use node_runtime::{UncheckedExtrinsic, Call, Runtime};
use runtime_primitives::generic::{Era};
use codec::{Encode};

/// Get Alice's account public key
fn get_alice_public_key() -> AccountId {
  AccountId::from(Keyring::Alice.to_raw_public())
}

/// Display the hex value of the smart contract
fn show_hex_of_smart_contract(raw_bytes: &[u8]) {
  let mut hex_raw_bytes = String::new();
  write!(hex_raw_bytes, "0x");
  for byte in raw_bytes {
    write!(hex_raw_bytes, "{:02x}", byte);
  }
  println!("Smart Contract 'Adder' WASM code in hex is: {}", hex_raw_bytes);
}

/// Display the hex value of the extrinsic
fn show_hex_of_extrinsic(raw_bytes: &[u8]) {
  let mut hex_raw_bytes = String::new();
  write!(hex_raw_bytes, "0x");
  for byte in raw_bytes {
    write!(hex_raw_bytes, "{:02x}", byte);
  }
  println!("Unchecked Extrinsic with Nonce 0: {}", hex_raw_bytes);
}

fn print_extrinsic(pair: &Pair, genesis_hash: &[u8; 32], index: u64, func: Call) {
  let pepa = AccountId::from(&pair.public().0[..]);
  let era = Era::immortal();
  let payload = (index, func.clone(), era, genesis_hash);
  let signature = pair.sign(&payload.encode()).into();
  let uxt = UncheckedExtrinsic {
    signature: Some((balances::address::Address::Id(pepa), signature, index, era)),
    function: func,
  };

  show_hex_of_extrinsic(&raw_uxt);
}

/// Returns only a first part of the storage key.
///
/// Hashed by 128 bit version of xxHash.
fn first_part_of_key(k1: AccountId) -> [u8; 16] {
  let mut raw_prefix = Vec::new();
  raw_prefix.extend(b"con:sto:");
  raw_prefix.extend(Encode::encode(&k1));
  twox_128(&raw_prefix)
}

/// Returns a compound key that consist of the two parts: (prefix, `k1`) and `k2`.
///
/// The first part is hashed by xxHash and then concatenated with a 256 bit version of blake2 hash of `k2`.
fn db_key_for_contract_storage(k1: AccountId, k2: Vec<u8>) -> Vec<u8> {
  let first_part = first_part_of_key(k1);
  let second_part = blake2_256(&Encode::encode(&k2));

  let mut k = Vec::new();
  k.extend(&first_part);
  k.extend(&second_part);
  k
}

fn main() {
  /// Add 0x-prefix to given genesis block hash.
  const GENESIS_BLOCK_HASH: &[u8; 32] = &hex!("771dfd2593b2f07998e3a1ffb196f78ca583c25641a3bc844d3d6a49405acde0");
  println!("Genesis Block Hash is: 0x{}\n", HexDisplay::from(GENESIS_BLOCK_HASH));

  /// Load Smart Contract 'Adder' WASM code into a bytes slice
  const ADDER_INIT_CODE: &'static [u8] = include_bytes!("/Users/scon/code/src/pepyakin/substrate-contracts-adder/target/wasm32-unknown-unknown/release/substrate_contracts_adder.wasm");
  show_hex_of_smart_contract(&ADDER_INIT_CODE);

  /// Get Alice's account key
  let pair = Pair::from(Keyring::from_public(Public::from_raw(get_alice_public_key().clone().into())).unwrap());
  let alice = AccountId::from(&pair.public().0[..]);
  println!("Alice's Account Key is: {:?} ({})\n", alice, keyring::ed25519::Public(alice.0).to_ss58check());

  /// Print the Extrinsic with Nonce 0 in encoded form where Alice would deploy Smart Contract "Adder" to the Substrate Node
  print_extrinsic(
    &pair, 
    GENESIS_BLOCK_HASH, 
    0, 
    Call::Contract(contract::Call::create::<Runtime>(1001.into(), 9_000_000.into(), ADDER_INIT_CODE.to_vec(), Vec::new()))
  );

  /// Pre-Determine upfront the Contract Address in the Runtime of the Substrate Node that the Smart Contract 'Adder' would be deployed to by Alice if an extrinsic was submitted
  let addr = <Runtime as contract::Trait>::DetermineContractAddress::contract_address_for(
    &ADDER_INIT_CODE,
    &[],
    &alice,
  );

  /// Print the Extrinsic with Nonce 1 of a Call to a method to Increment storage by 1 in the Smart Contract 'Adder' at the Pre-Determined Contract Address using the encoded form of the Extrinsic
  print_extrinsic(&pair, GENESIS_BLOCK_HASH, 1, Call::Contract(contract::Call::call::<Runtime>(addr, 1001.into(), 9_000_000.into(), vec![0x00, 0x01, 0x00, 0x00, 0x00])));

  println!("DB Storage Key of Smart Contract code:");
  println!("0x{}", HexDisplay::from(&db_key_for_contract_storage(addr.clone(), [1u8; 32].to_vec())));

  /// Print the Extrinsic with Nonce 2 of a Call to a method to further Increment storage by 7 in the Smart Contract 'Adder' at the Pre-Determined Contract Address using the encoded form of the Extrinsic
  print_extrinsic(&pair, GENESIS_BLOCK_HASH, 2, Call::Contract(contract::Call::call::<Runtime>(addr, 1001.into(), 9_000_000.into(), vec![0x00, 0x07, 0x00, 0x00, 0x00])));
}
