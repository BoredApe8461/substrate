// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.
use std::iter::once;
use trie_root::{Hasher, TrieStream};
use codec::Encode;

/// Codec-flavoured TrieStream
pub struct CodecTrieStreamAlt {
	buffer: Vec<u8>
}

pub const EMPTY_TRIE: u8 = 0;
pub const LEAF_NODE_OFFSET: u8 = 1;
pub const LEAF_NODE_BIG: u8 = 127;
pub const EXTENSION_NODE_OFFSET: u8 = 128;
pub const EXTENSION_NODE_BIG: u8 = 253;
pub const BRANCH_NODE_NO_VALUE: u8 = 254;
pub const BRANCH_NODE_WITH_VALUE: u8 = 255;

impl CodecTrieStreamAlt {
	// useful for debugging but not used otherwise
	pub fn as_raw(&self) -> &[u8] { &self.buffer }
}

/// Create a leaf/extension node, encoding a number of nibbles. Note that this
/// cannot handle a number of nibbles that is zero or greater than 127 and if
/// you attempt to do so *IT WILL PANIC*.
fn fuse_nibbles_node<'a>(nibbles: &'a [u8], leaf: bool) -> impl Iterator<Item = u8> + 'a {
	debug_assert!(nibbles.len() < 255 + 126, "nibbles length too long. what kind of size of key are you trying to include in the trie!?!");
	// We use two ranges of possible values; one for leafs and the other for extensions.
	// Each range encodes zero following nibbles up to some maximum. If the maximum is
	// reached, then it is considered "big" and a second byte follows it in order to
	// encode a further offset to the number of nibbles of up to 255. Beyond that, we
	// cannot encode. This shouldn't be a problem though since that allows for keys of
	// up to 380 nibbles (190 bytes) and we expect key sizes to be generally 128-bit (16
	// bytes) or, at a push, 384-bit (48 bytes).

	let (first_byte_small, big_threshold) = if leaf {
		(LEAF_NODE_OFFSET, (LEAF_NODE_BIG - LEAF_NODE_OFFSET) as usize)
	} else {
		(EXTENSION_NODE_OFFSET, (EXTENSION_NODE_BIG - EXTENSION_NODE_OFFSET) as usize)
	};
	let first_byte = first_byte_small + nibbles.len().min(big_threshold) as u8;
	once(first_byte)
		.chain(if nibbles.len() >= big_threshold { Some((nibbles.len() - big_threshold) as u8) } else { None })
		.chain(if nibbles.len() % 2 == 1 { Some(nibbles[0]) } else { None })
		.chain(nibbles[nibbles.len() % 2..].chunks(2).map(|ch| ch[0] << 4 | ch[1]))
}

pub fn branch_node(has_value: bool, has_children: impl Iterator<Item = bool>) -> [u8; 3] {
	let first = if has_value {
		BRANCH_NODE_WITH_VALUE
	} else {
		BRANCH_NODE_NO_VALUE
	};
	let mut bitmap: u16 = 0;
	let mut cursor: u16 = 1;
	for v in has_children {
		if v { bitmap |= cursor }
		cursor <<= 1;
	}
	[first, (bitmap % 256 ) as u8, (bitmap / 256 ) as u8]
}

impl TrieStream for CodecTrieStreamAlt {
	fn new() -> Self { Self {buffer: Vec::new() } }
	fn append_empty_data(&mut self) {
		self.buffer.push(EMPTY_TRIE);
	}

	fn append_leaf(&mut self, key: &[u8], value: &[u8]) {
		self.buffer.extend(fuse_nibbles_node(key, true));
		// OPTIMISATION: I'd like to do `hpe.encode_to(&mut self.buffer);` here; need an `impl<'a> Encode for impl Iterator<Item = u8> + 'a`?
		value.encode_to(&mut self.buffer);
	}
	fn begin_branch(&mut self, maybe_value: Option<&[u8]>, has_children: impl Iterator<Item = bool>) {
//		println!("[begin_branch] pushing BRANCH_NODE");
		self.buffer.extend(&branch_node(maybe_value.is_some(), has_children));
		// Push the value if one exists.
		if let Some(value) = maybe_value {
			value.encode_to(&mut self.buffer);
		}
//		println!("[begin_branch] buffer so far: {:#x?}", self.buffer);
	}
	fn append_extension(&mut self, key: &[u8]) {
		self.buffer.extend(fuse_nibbles_node(key, false));
	}
	fn append_substream<H: Hasher>(&mut self, other: Self) {
		let data = other.out();
//		println!("[append_substream] START own buffer: {:x?}", self.buffer);
//		println!("[append_substream] START other buffer: {:x?}", data);
		match data.len() {
			0...31 => {
//				println!("[append_substream] appending data, because data.len() = {}", data.len());
				self.buffer.extend_from_slice(&data[..]);
			},
			_ => {
//				println!("[append_substream] would have hashed, because data.len() = {}", data.len());
//				data.encode_to(&mut self.buffer)
				// TODO: re-enable hashing before merging
				self.buffer.push(EMPTY_TRIE);
				self.buffer.extend_from_slice(H::hash(&data).as_ref());
			}
		}
	}

	fn out(self) -> Vec<u8> { self.buffer }
}
