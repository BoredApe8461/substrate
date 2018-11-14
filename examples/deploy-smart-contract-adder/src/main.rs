extern crate substrate_primitives as primitives;
extern crate hex;

#[macro_use]
extern crate hex_literal;

use primitives::hexdisplay::HexDisplay;

fn main() {
  /// Enter block hash of genesis block retrieved above (required for creating extrinsics that we can execute on this chain)
  const GENESIS_HASH: &[u8; 32] = &hex!("771dfd2593b2f07998e3a1ffb196f78ca583c25641a3bc844d3d6a49405acde0");
  println!("GENESIS_HASH: 0x{}\n", HexDisplay::from(GENESIS_HASH));

  const ADDER_INIT_CODE: &'static [u8] = include_bytes!("/Users/scon/code/src/pepyakin/substrate-contracts-adder/target/wasm32-unknown-unknown/release/substrate_contracts_adder.wasm");
  println!("ADDER_INIT_CODE: 0x{}\n", HexDisplay::from(&ADDER_INIT_CODE));
}