// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::mem;
use std::cmp;
use std::ops::Range;
use std::collections::{HashMap, BTreeMap};
use std::collections::hash_map::Entry;
use std::collections::btree_map::Entry as BTreeMapEntry;
use network_libp2p::NodeIndex;
use runtime_primitives::traits::{Block as BlockT, NumberFor, As, One};
use message;

const MAX_PARALLEL_DOWNLOADS: u32 = 1;

/// Block data with origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockData<B: BlockT> {
	pub block: message::BlockData<B>,
	pub origin: NodeIndex,
}

#[derive(Debug, PartialEq)]
enum BlockRangeState<B: BlockT> {
	Downloading {
		len: NumberFor<B>,
		downloading: u32,
	},
	RequestingAdditionalData(PausedBlock<B>),
	Complete(Vec<BlockData<B>>),
}

/// Data of block which import is paused because we require additional data.
#[derive(Debug, PartialEq)]
pub struct PausedBlock<B: BlockT> {
	/// Current number of concurrent downloads.
	pub downloading: u32,
	/// Number of the block that we're requesting additional data for.
	pub number: NumberFor<B>,
	/// Required attributes of blocks we're requesting.
	pub required: message::BlockAttributes,
	/// Known data of the block we're requesting additional data for.
	pub block: BlockData<B>,
}

/// Data of blocks which import is paused because we require additional data
/// for given block.
#[derive(Debug, PartialEq)]
pub struct PausedBlocks<B: BlockT> {
	/// Block which import is paused.
	pub block: PausedBlock<B>,
	/// Blocks following the paused block.
	pub rest: Vec<BlockData<B>>,
}

impl<B: BlockT> BlockRangeState<B> {
	pub fn len(&self) -> NumberFor<B> {
		match *self {
			BlockRangeState::Downloading { len, .. } => len,
			BlockRangeState::RequestingAdditionalData(_) => As::sa(1u64),
			BlockRangeState::Complete(ref blocks) => As::sa(blocks.len() as u64),
		}
	}
}

/// A collection of blocks being downloaded.
#[derive(Default)]
pub struct BlockCollection<B: BlockT> {
	/// Block attributes that are queried by default.
	required_block_attributes: message::BlockAttributes,
	/// Downloaded blocks.
	blocks: BTreeMap<NumberFor<B>, BlockRangeState<B>>,
	peer_requests: HashMap<NodeIndex, NumberFor<B>>,
}

impl<B: BlockT> BlockCollection<B> {
	/// Create a new instance.
	pub fn new(required_block_attributes: message::BlockAttributes) -> Self {
		BlockCollection {
			required_block_attributes,
			blocks: BTreeMap::new(),
			peer_requests: HashMap::new(),
		}
	}

	/// Return block attributes that are queried by default.
	pub fn required_block_attributes(&self) -> message::BlockAttributes {
		self.required_block_attributes
	}

	/// Clear everything.
	pub fn clear(&mut self) {
		self.blocks.clear();
		self.peer_requests.clear();
	}

	/// Insert a set of blocks into collection.
	pub fn insert(&mut self, start: NumberFor<B>, blocks: Vec<message::BlockData<B>>, who: NodeIndex) {
		if blocks.is_empty() {
			return;
		}

		let blocks: Vec<_> = match self.blocks.get_mut(&start) {
			Some(&mut BlockRangeState::Downloading { .. }) => {
				trace!(target: "sync", "Ignored block data still marked as being downloaded: {}", start);
				debug_assert!(false);
				return;
			},
			Some(&mut BlockRangeState::RequestingAdditionalData(_)) => {
				trace!(target: "sync", "Ignored block data still marked as being additionally downloaded: {}", start);
				return;
			},
			Some(&mut BlockRangeState::Complete(ref existing)) if existing.len() >= blocks.len() => {
				trace!(target: "sync", "Ignored block data already downloaded: {}", start);
				return;
			},
			_ => blocks.into_iter().map(|b| BlockData {
					origin: who,
					block: b,
				}).collect(),
		};

		self.blocks.insert(start, BlockRangeState::Complete(blocks));
	}

	/// Insert set of blocks back into collection because the first block of the set requires additional
	/// data from peers.
	pub fn return_paused_blocks(&mut self, paused_blocks: PausedBlocks<B>) {
		// there's a little chance that there could be an entry at number && number + 1:
		// this is possible when there are two competing forks that both require additional
		// data at given block number
		//
		// => prefer blocks from fork that has been received earlier
		// we will probably move back to the other fork when sync::maintain will be called

		let next_number = paused_blocks.block.number + One::one();
		match self.blocks.entry(paused_blocks.block.number) {
			BTreeMapEntry::Occupied(_) => return,
			BTreeMapEntry::Vacant(entry) => entry
				.insert(BlockRangeState::RequestingAdditionalData(paused_blocks.block)),
		};

		if !paused_blocks.rest.is_empty() {
			self.blocks.entry(next_number)
				.or_insert(BlockRangeState::Complete(paused_blocks.rest));
		}
	}

	/// Returns a set of block hashes that require a header download. The returned set is marked as being downloaded.
	pub fn needed_blocks(&mut self, who: NodeIndex, count: usize, peer_best: NumberFor<B>, common: NumberFor<B>)
		-> Option<(message::BlockAttributes, Range<NumberFor<B>>)>
	{
		// First block number that we need to download
		let first_different = common + As::sa(1);
		let count = As::sa(count as u64);
		let (mut range, is_additional, downloading) = {
			let mut downloading_iter = self.blocks.iter().peekable();
			let mut prev: Option<(&NumberFor<B>, &BlockRangeState<B>)> = None;
			loop {
				let next = downloading_iter.next();
				break match &(prev, next) {
					&(_, Some((start, &BlockRangeState::RequestingAdditionalData(ref paused)))) if paused.downloading < MAX_PARALLEL_DOWNLOADS =>
						(*start .. *start + One::one(), true, paused.downloading),
					&(_, Some((_, &BlockRangeState::RequestingAdditionalData(_)))) =>
						continue, // continue downloading future blocks even though we are still waiting for required data of previous block
					&(Some((start, &BlockRangeState::Downloading { ref len, downloading })), _) if downloading < MAX_PARALLEL_DOWNLOADS =>
						(*start .. *start + *len, false, downloading),
					&(Some((start, r)), Some((next_start, _))) if *start + r.len() < *next_start =>
						(*start + r.len() .. cmp::min(*next_start, *start + r.len() + count), false, 0), // gap
					&(Some((start, r)), None) =>
						(*start + r.len() .. *start + r.len() + count, false, 0), // last range
					&(None, None) =>
						(first_different .. first_different + count, false, 0), // empty
					&(None, Some((start, _))) if *start > first_different =>
						(first_different .. cmp::min(first_different + count, *start), false, 0), // gap at the start
					_ => {
						prev = next;
						continue
					},
				}
			}
		};

		// crop to peers best
		if range.start > peer_best {
			trace!(target: "sync", "Out of range for peer {} ({} vs {})", who, range.start, peer_best);
			return None;
		}
		range.end = cmp::min(peer_best + As::sa(1), range.end);

		self.peer_requests.insert(who, range.start);
		let attributes = if is_additional {
			let additional_request = self.blocks.get_mut(&range.start)
				.and_then(BlockRangeState::as_additional_data_request)
				.expect("is_additional is only true when range.start points to RequestingAdditionalData range; qed");
			additional_request.downloading = downloading + 1;
			additional_request.required
		} else {
			self.blocks.insert(range.start, BlockRangeState::Downloading { len: range.end - range.start, downloading: downloading + 1 });
			self.required_block_attributes
		};

		if range.end <= range.start {
			panic!("Empty range {:?}, count={}, peer_best={}, common={}, blocks={:?}", range, count, peer_best, common, self.blocks);
		}

		Some((attributes, range))
	}

	/// Get a valid chain of blocks ordered in descending order and ready for importing into blockchain.
	pub fn drain(&mut self, from: NumberFor<B>) -> Vec<BlockData<B>> {
		let mut drained = Vec::new();
		let mut ranges = Vec::new();
		{
			let mut prev = from;
			for (start, range_data) in &mut self.blocks {
				match range_data {
					&mut BlockRangeState::Complete(ref mut blocks) if *start <= prev => {
						prev = *start + As::sa(blocks.len() as u64);
						let mut blocks = mem::replace(blocks, Vec::new());
						drained.append(&mut blocks);
						ranges.push(*start);
					},
					_ => break,
				}
			}
		}
		for r in ranges {
			self.blocks.remove(&r);
		}
		trace!(target: "sync", "Drained {} blocks", drained.len());
		drained
	}

	pub fn clear_peer_download(&mut self, who: NodeIndex, blocks: Vec<message::BlockData<B>>) -> Vec<message::BlockData<B>> {
		match self.peer_requests.entry(who) {
			Entry::Occupied(entry) => {
				let start = entry.remove();
				let (blocks, remove) = match self.blocks.get_mut(&start) {
					Some(&mut BlockRangeState::Downloading { ref mut downloading, .. }) if *downloading > 1 => {
						*downloading = *downloading - 1;
						(blocks, false)
					},
					Some(&mut BlockRangeState::Downloading { .. }) => {
						(blocks, true)
					},
					Some(&mut BlockRangeState::RequestingAdditionalData(ref mut paused)) => {
						if paused.downloading > 1 {
							paused.downloading = paused.downloading - 1;
						}

						update_paused_block(paused, blocks)
					},
					_ => {
						debug_assert!(false);
						(blocks, false)
					},
				};
				if remove {
					self.blocks.remove(&start);
				}
				blocks
			},
			_ => blocks,
		}
	}
}

impl<B: BlockT> BlockRangeState<B> {
	fn as_additional_data_request(&mut self) -> Option<&mut PausedBlock<B>> {
		match *self {
			BlockRangeState::RequestingAdditionalData(ref mut paused) => Some(paused),
			_ => None,
		}
	}
}

/// Tries to update paused block with information recevied from peer.
fn update_paused_block<B: BlockT>(paused: &mut PausedBlock<B>, blocks: Vec<message::BlockData<B>>)
	-> (Vec<message::BlockData<B>>, bool)
{
	// prefer wider range of blocks over paused block
	match blocks.len() {
		0 => return (blocks, false),
		1 => (),
		_ => return (blocks, true),
	}

	// update paused block with missing data
	let mut block = blocks.into_iter().nth(0).expect("blocks.len() is 1; qed");
	let required_before = paused.required;
	if paused.required.contains(message::BlockAttributes::AUTHORITIES_JUSTIFICATION) {
		if let Some(authorities_justification) = block.authorities_justification.take() {
			paused.required.remove(message::BlockAttributes::AUTHORITIES_JUSTIFICATION);

			paused.block.block.authorities_justification = Some(authorities_justification);
		}
	}

	// if not all required data is received => leave as is
	if !paused.required.is_empty() {
		trace!(target: "sync", "Insufficient additional block data provided: {}. Before: {:?}, after: {:?}",
			paused.number, required_before, paused.required);
		return (vec![], false);
	}

	// updated paused block -> block
	::std::mem::swap(&mut block, &mut paused.block.block);

	(vec![block], true)
}

#[cfg(test)]
mod test {
	use super::{BlockCollection, BlockData, BlockRangeState, PausedBlocks,
		PausedBlock, update_paused_block};
	use message;
	use runtime_primitives::testing::Block as RawBlock;
	use primitives::H256;

	type Block = RawBlock<u64>;

	fn is_empty(bc: &BlockCollection<Block>) -> bool {
		bc.blocks.is_empty() &&
		bc.peer_requests.is_empty()
	}

	fn generate_blocks(n: usize) -> Vec<message::BlockData<Block>> {
		(0u64 .. n as u64).map(|i| message::generic::BlockData {
			hash: H256::from(i),
			header: None,
			body: None,
			message_queue: None,
			receipt: None,
			justification: None,
			authorities_justification: None,
		}).collect()
	}

	#[test]
	fn create_clear() {
		let mut bc = BlockCollection::new(Default::default());
		assert!(is_empty(&bc));
		bc.insert(1, generate_blocks(100), 0);
		assert!(!is_empty(&bc));
		bc.clear();
		assert!(is_empty(&bc));
	}

	#[test]
	fn insert_blocks() {
		let mut bc = BlockCollection::new(Default::default());
		assert!(is_empty(&bc));
		let peer0 = 0;
		let peer1 = 1;
		let peer2 = 2;

		let blocks = generate_blocks(150);
		assert_eq!(bc.needed_blocks(peer0, 40, 150, 0), Some((Default::default(), 1 .. 41)));
		assert_eq!(bc.needed_blocks(peer1, 40, 150, 0), Some((Default::default(), 41 .. 81)));
		assert_eq!(bc.needed_blocks(peer2, 40, 150, 0), Some((Default::default(), 81 .. 121)));

		bc.clear_peer_download(peer1, vec![]);
		bc.insert(41, blocks[41..81].to_vec(), peer1);
		assert_eq!(bc.drain(1), vec![]);
		assert_eq!(bc.needed_blocks(peer1, 40, 150, 0), Some((Default::default(), 121 .. 151)));
		bc.clear_peer_download(peer0, vec![]);
		bc.insert(1, blocks[1..11].to_vec(), peer0);

		assert_eq!(bc.needed_blocks(peer0, 40, 150, 0), Some((Default::default(), 11 .. 41)));
		assert_eq!(bc.drain(1), blocks[1..11].iter().map(|b| BlockData { block: b.clone(), origin: 0 }).collect::<Vec<_>>());

		bc.clear_peer_download(peer0, vec![]);
		bc.insert(11, blocks[11..41].to_vec(), peer0);

		let drained = bc.drain(12);
		assert_eq!(drained[..30], blocks[11..41].iter().map(|b| BlockData { block: b.clone(), origin: 0 }).collect::<Vec<_>>()[..]);
		assert_eq!(drained[30..], blocks[41..81].iter().map(|b| BlockData { block: b.clone(), origin: 1 }).collect::<Vec<_>>()[..]);

		bc.clear_peer_download(peer2, vec![]);
		assert_eq!(bc.needed_blocks(peer2, 40, 150, 80), Some((Default::default(), 81 .. 121)));
		bc.clear_peer_download(peer2, vec![]);
		bc.insert(81, blocks[81..121].to_vec(), peer2);
		bc.clear_peer_download(peer1, vec![]);
		bc.insert(121, blocks[121..150].to_vec(), peer1);

		assert_eq!(bc.drain(80), vec![]);
		let drained = bc.drain(81);
		assert_eq!(drained[..40], blocks[81..121].iter().map(|b| BlockData { block: b.clone(), origin: 2 }).collect::<Vec<_>>()[..]);
		assert_eq!(drained[40..], blocks[121..150].iter().map(|b| BlockData { block: b.clone(), origin: 1 }).collect::<Vec<_>>()[..]);
	}

	#[test]
	fn large_gap() {
		let mut bc: BlockCollection<Block> = BlockCollection::new(Default::default());
		bc.blocks.insert(100, BlockRangeState::Downloading {
			len: 128,
			downloading: 1,
		});
		let blocks = generate_blocks(10).into_iter().map(|b| BlockData { block: b, origin: 0 }).collect();
		bc.blocks.insert(114305, BlockRangeState::Complete(blocks));

		assert_eq!(bc.needed_blocks(0, 128, 10000, 000), Some((Default::default(), 1 .. 100)));
		assert_eq!(bc.needed_blocks(0, 128, 10000, 600), Some((Default::default(), 100 + 128 .. 100 + 128 + 128)));
	}

	fn make_paused_block() -> (PausedBlock<Block>, message::BlockData<Block>) {
		let block = generate_blocks(1).into_iter().nth(0).unwrap();
		(PausedBlock {
			downloading: 0,
			number: 100,
			required: message::BlockAttributes::AUTHORITIES_JUSTIFICATION,
			block: BlockData {
				block: block.clone(),
				origin: 0,
			},
		}, block)
	}

	fn prepare_for_additional_data() -> (message::BlockData<Block>, BlockCollection<Block>) {
		let mut bc: BlockCollection<Block> = BlockCollection::new(Default::default());
		let (paused_block, block) = make_paused_block();
		bc.blocks.insert(100, BlockRangeState::RequestingAdditionalData(paused_block));

		(block, bc)
	}

	#[test]
	fn insert_does_not_replace_additional_data_request() {
		let (block, mut bc) = prepare_for_additional_data();
		bc.insert(100, vec![block], 0);
		assert_eq!(bc.blocks.into_iter().collect::<Vec<_>>(), vec![
			(100, BlockRangeState::RequestingAdditionalData(make_paused_block().0))
		]);
	}

	#[test]
	fn return_paused_blocks_does_nothing_if_entry_is_occupied() {
		let mut bc: BlockCollection<Block> = BlockCollection::new(Default::default());
		bc.blocks.insert(100, BlockRangeState::Downloading { len: 128, downloading: 1 });
		bc.return_paused_blocks(PausedBlocks { block: make_paused_block().0, rest: vec![] });
		assert_eq!(bc.blocks.into_iter().collect::<Vec<_>>(), vec![
			(100, BlockRangeState::Downloading { len: 128, downloading: 1 })
		]);
	}

	#[test]
	fn return_paused_blocks_works() {
		let rest_data: Vec<_> = generate_blocks(10).into_iter().map(|block| BlockData { block, origin: 0 }).collect();
		let mut bc: BlockCollection<Block> = BlockCollection::new(Default::default());
		bc.return_paused_blocks(PausedBlocks { block: make_paused_block().0, rest: rest_data.clone() });
		assert_eq!(bc.blocks.into_iter().collect::<Vec<_>>(), vec![
			(100, BlockRangeState::RequestingAdditionalData(make_paused_block().0)),
			(101, BlockRangeState::Complete(rest_data)),
		]);
	}

	#[test]
	fn needed_blocks_requests_additional_data_request_first() {
		let (_, mut bc) = prepare_for_additional_data();
		assert_eq!(bc.blocks.get_mut(&100).unwrap().as_additional_data_request().unwrap().downloading, 0);
		assert_eq!(bc.needed_blocks(1, 1000, 1000, 0), Some((message::BlockAttributes::AUTHORITIES_JUSTIFICATION,
			100 .. 101)));
		assert_eq!(bc.blocks.get_mut(&100).unwrap().as_additional_data_request().unwrap().downloading, 1);
		assert_eq!(bc.needed_blocks(2, 1000, 1000, 0), Some((Default::default(),
			1 .. 1001)));
	}

	#[test]
	fn empty_blocks_set_does_not_overwrite_paused_block() {
		let (mut paused, _) = make_paused_block();
		assert_eq!(update_paused_block(&mut paused, vec![]), (vec![], false));
	}

	#[test]
	fn many_blocks_overwrite_paused_block() {
		let (mut paused, _) = make_paused_block();
		let blocks = generate_blocks(10);
		assert_eq!(update_paused_block(&mut paused, blocks.clone()),
			(blocks, true));
	}

	#[test]
	fn non_full_block_does_not_overwrite_paused_block() {
		let (mut paused, _) = make_paused_block();
		assert_eq!(update_paused_block(&mut paused, vec![]),
			(vec![], false));
	}

	#[test]
	fn update_paused_block_works() {
		let (mut paused, mut block) = make_paused_block();
		block.authorities_justification = Some(());
		assert_eq!(update_paused_block(&mut paused, vec![block.clone()]),
			(vec![block], true));
	}

	#[test]
	fn additional_data_fetch_is_queued() {
		let mut bc: BlockCollection<Block> = BlockCollection::new(Default::default());
		let msg_blocks = generate_blocks(10);
		let mut blocks = msg_blocks.clone().into_iter().map(|b| BlockData { block: b, origin: 0 }).collect::<Vec<_>>();

		// blocks [1..10] are ready to import
		bc.insert(1, msg_blocks.clone(), 0);
		// blocks [1..10] are drained && import starts
		assert_eq!(bc.drain(10), blocks);

		// block#3 requires additional data
		bc.return_paused_blocks(PausedBlocks {
			block: PausedBlock {
				downloading: 0,
				number: 3,
				required: message::BlockAttributes::AUTHORITIES_JUSTIFICATION,
				block: blocks[2].clone(),
			},
			rest: blocks[3..].to_vec(),
		});

		// additional data is requested from node#0
		assert_eq!(bc.needed_blocks(0, 128, 1000, 2), Some((
			message::BlockAttributes::AUTHORITIES_JUSTIFICATION,
			3..4)));

		// aditional data is filled on node#0
		let authorities_justification = Some(());
		let mut response_block = msg_blocks[2].clone();
		response_block.authorities_justification = authorities_justification.clone();

		// and returned back to our node
		let response_blocks = bc.clear_peer_download(0, vec![response_block]);
		bc.insert(3, response_blocks, 0);

		// blocks [3..10] are drained && import starts
		blocks[2].block.authorities_justification = authorities_justification;
		assert_eq!(bc.drain(10), blocks[2..].to_vec());
	}
}
