// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The Polkadot runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_std;

#[cfg(feature = "with-std")]
extern crate rustc_hex;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

pub mod codec;
#[macro_use]
pub mod support;
pub mod primitives;
pub mod runtime;

use runtime_std::prelude::*;
use codec::{Slicable, Joiner};
use runtime_std::print;
use primitives::{Block, Header, BlockNumber, UncheckedTransaction};

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(input: &[u8]) -> Vec<u8> {
	runtime::system::internal::execute_block(Block::from_slice(input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(input: &[u8]) -> Vec<u8> {
	let number = BlockNumber::from_slice(&input[0..8]).unwrap();
	let utx = UncheckedTransaction::from_slice(&input[8..]).unwrap();
	runtime::system::internal::execute_transaction(&utx, Header::from_block_number(number));
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn finalise_block(input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(input).unwrap();
	let header = runtime::system::internal::finalise_block(header);
	Vec::new().join(&header)
}

/// Run whatever tests we have.
pub fn run_tests(input: &[u8]) -> Vec<u8> {
	print("run_tests...");
	let block = Block::from_slice(input).unwrap();
	print("deserialised block.");
	let stxs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].to_vec()
}

impl_stubs!(execute_block, execute_transaction, finalise_block, run_tests);
