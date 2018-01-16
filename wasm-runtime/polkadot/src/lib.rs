#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_support;

mod endiansensitive;
mod streamreader;
mod slicable;
mod primitives;
mod keyedvec;
mod function;
mod environment;
mod storage;
mod testing;
#[allow(unused)]
mod system;
#[allow(unused)]
mod consensus;
#[allow(unused)]
mod staking;
#[allow(unused)]
mod timestamp;

use runtime_support::Vec;
use slicable::Slicable;
use primitives::{ChainID, Block, Transaction};

// TODO: add keccak256 (or some better hashing scheme) & ECDSA-recover (or some better sig scheme)

pub fn execute_block(input: Vec<u8>) -> Vec<u8> {
	system::execute_block(Block::from_slice(&input).unwrap())
}

pub fn execute_transaction(input: Vec<u8>) -> Vec<u8> {
	system::execute_transaction(&Transaction::from_slice(&input).unwrap())
}

impl_stubs!(execute_block, execute_transaction);

/// The current relay chain identifier.
pub fn chain_id() -> ChainID {
	// TODO: retrieve from external
	unimplemented!()
}
