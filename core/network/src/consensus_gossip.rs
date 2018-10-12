// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Utility for gossip of network messages between authorities.
//! Handles chain-specific and standard BFT messages.

use std::collections::{HashMap, HashSet};
use futures::sync::mpsc;
use std::time::{Instant, Duration};
use rand::{self, Rng};
use network_libp2p::NodeIndex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use message::{self, generic::Message as GenericMessage};
use protocol::Context;
use service::Roles;
use specialization::Specialization;
use StatusMessage;
use generic_message;

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
	is_authority: bool,
}

/// Consensus messages.
#[derive(Debug, Clone, PartialEq)]
pub enum ConsensusMessage<B: BlockT> {
	/// A message concerning BFT agreement
	Bft(message::LocalizedBftMessage<B>),
	/// A message concerning some chain-specific aspect of consensus
	ChainSpecific(Vec<u8>, B::Hash),
}

struct MessageEntry<B: BlockT> {
	hash: B::Hash,
	message: ConsensusMessage<B>,
	instant: Instant,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<B::Hash, mpsc::UnboundedSender<ConsensusMessage<B>>>,
	messages: Vec<MessageEntry<B>>,
	message_hashes: HashSet<B::Hash>,
	session_start: Option<B::Hash>,
}

impl<B: BlockT> ConsensusGossip<B> where B::Header: HeaderT<Number=u64> {
	/// Create a new instance.
	pub fn new() -> Self {
		ConsensusGossip {
			peers: HashMap::new(),
			live_message_sinks: HashMap::new(),
			messages: Default::default(),
			message_hashes: Default::default(),
			session_start: None
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.live_message_sinks.clear();
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, who: NodeIndex, roles: Roles) {
		if roles.intersects(Roles::AUTHORITY) {
			trace!(target:"gossip", "Registering {:?} {}", roles, who);
			// Send out all known messages to authorities.
			// TODO: limit by size
			let mut known_messages = HashSet::new();
			for entry in self.messages.iter() {
				known_messages.insert(entry.hash);
				let message = match entry.message {
					ConsensusMessage::Bft(ref bft) => GenericMessage::BftMessage(bft.clone()),
					ConsensusMessage::ChainSpecific(ref msg, _) => GenericMessage::ChainSpecific(msg.clone()),
				};

				protocol.send_message(who, message);
			}
			self.peers.insert(who, PeerConsensus {
				known_messages,
				is_authority: true,
			});
		}
		else if roles.intersects(Roles::FULL) {
			self.peers.insert(who, PeerConsensus {
				known_messages: HashSet::new(),
				is_authority: false,
			});
		}
	}

	fn propagate(&mut self, protocol: &mut Context<B>, message: message::Message<B>, hash: B::Hash) {
		let mut non_authorities: Vec<_> = self.peers.iter()
			.filter_map(|(id, ref peer)| if !peer.is_authority && !peer.known_messages.contains(&hash) { Some(*id) } else { None })
			.collect();

		rand::thread_rng().shuffle(&mut non_authorities);
		let non_authorities: HashSet<_> = if non_authorities.is_empty() {
			HashSet::new()
		} else {
			non_authorities[0..non_authorities.len().min(((non_authorities.len() as f64).sqrt() as usize).max(3))].iter().collect()
		};

		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.is_authority {
				if peer.known_messages.insert(hash.clone()) {
					trace!(target:"gossip", "Propagating to authority {}: {:?}", id, message);
					protocol.send_message(*id, message.clone());
				}
			}
			else if non_authorities.contains(&id) {
				trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
				peer.known_messages.insert(hash.clone());
				protocol.send_message(*id, message.clone());
			}
		}
	}

	fn register_message(&mut self, hash: B::Hash, message: ConsensusMessage<B>) {
		if self.message_hashes.insert(hash) {
			self.messages.push(MessageEntry {
				hash,
				instant: Instant::now(),
				message,
			});
		}
	}

	/// Handles incoming BFT message, passing to stream and repropagating.
	pub fn on_bft_message(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: message::LocalizedBftMessage<B>) {
		if let Some((hash, message)) = self.handle_incoming(protocol, who, ConsensusMessage::Bft(message)) {
			// propagate to other peers.
			self.multicast(protocol, message, Some(hash));
		}
	}

	/// Handles incoming chain-specific message and repropagates
	pub fn on_chain_specific(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: Vec<u8>, topic: B::Hash) {
		debug!(target: "gossip", "received chain-specific gossip message");
		if let Some((hash, message)) = self.handle_incoming(protocol, who, ConsensusMessage::ChainSpecific(message, topic)) {
			debug!(target: "gossip", "handled incoming chain-specific message");
			// propagate to other peers.
			self.multicast(protocol, message, Some(hash));
		}
	}

	/// Get a stream of messages relevant to consensus for the given topic.
	pub fn messages_for(&mut self, topic: B::Hash) -> mpsc::UnboundedReceiver<ConsensusMessage<B>> {
		let (sink, stream) = mpsc::unbounded();

		for entry in self.messages.iter() {
			let message_matches = match entry.message {
				ConsensusMessage::Bft(ref msg) => msg.parent_hash == topic,
				ConsensusMessage::ChainSpecific(_, ref h) => h == &topic,
			};

			if message_matches {
				sink.unbounded_send(entry.message.clone()).expect("receiving end known to be open; qed");
			}
		}

		self.live_message_sinks.insert(topic, sink);
		stream
	}

	/// Multicast a chain-specific message to other authorities.
	pub fn multicast_chain_specific(&mut self, protocol: &mut Context<B>, message: Vec<u8>, topic: B::Hash) {
		trace!(target:"gossip", "sending chain-specific message");
		self.multicast(protocol, ConsensusMessage::ChainSpecific(message, topic), None);
	}

	/// Multicast a BFT message to other authorities
	pub fn multicast_bft_message(&mut self, protocol: &mut Context<B>, message: message::LocalizedBftMessage<B>) {
		// Broadcast message to all authorities.
		trace!(target:"gossip", "Broadcasting BFT message {:?}", message);
		self.multicast(protocol, ConsensusMessage::Bft(message), None);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, _protocol: &mut Context<B>, who: NodeIndex) {
		self.peers.remove(&who);
	}

	/// Prune old or no longer relevant consensus messages. Provide a predicate
	/// for pruning, which returns `false` when the items with a given topic should be pruned.
	pub fn collect_garbage<P: Fn(&B::Hash) -> bool>(&mut self, predicate: P) {
		self.live_message_sinks.retain(|_, sink| !sink.is_closed());

		let hashes = &mut self.message_hashes;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|entry| {
			let topic = match entry.message {
				ConsensusMessage::Bft(ref msg) => &msg.parent_hash,
				ConsensusMessage::ChainSpecific(_, ref h) => h,
			};

			if entry.instant + MESSAGE_LIFETIME >= now && predicate(topic) {
				true
			} else {
				hashes.remove(&entry.hash);
				false
			}
		});
		trace!(target:"gossip", "Cleaned up {} stale messages, {} left", before - self.messages.len(), self.messages.len());
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}

	fn handle_incoming(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: ConsensusMessage<B>) -> Option<(B::Hash, ConsensusMessage<B>)> {
		let (hash, topic, message) = match message {
			ConsensusMessage::Bft(msg) => {
				let parent = msg.parent_hash;
				let generic = GenericMessage::BftMessage(msg);
				(
					::protocol::hash_message(&generic),
					parent,
					match generic {
						GenericMessage::BftMessage(msg) => ConsensusMessage::Bft(msg),
						_ => panic!("`generic` is known to be the `BftMessage` variant; qed"),
					}
				)
			}
			ConsensusMessage::ChainSpecific(msg, topic) => {
				let generic = GenericMessage::ChainSpecific(msg);
				(
					::protocol::hash_message::<B>(&generic),
					topic,
					match generic {
						GenericMessage::ChainSpecific(msg) => ConsensusMessage::ChainSpecific(msg, topic),
						_ => panic!("`generic` is known to be the `ChainSpecific` variant; qed"),
					}
				)
			}
		};

		if self.message_hashes.contains(&hash) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			return None;
		}

		match (protocol.client().info(), protocol.client().header(&BlockId::Hash(topic))) {
			(_, Err(e)) | (Err(e), _) => {
				debug!(target:"gossip", "Error reading blockchain: {:?}", e);
				return None;
			},
			(Ok(info), Ok(Some(header))) => {
				if header.number() < &info.chain.best_number {
					trace!(target:"gossip", "Ignored ancient message from {}, hash={}", who, topic);
					return None;
				}
			},
			(Ok(_), Ok(None)) => {},
		}

		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			use std::collections::hash_map::Entry;
			peer.known_messages.insert(hash);
			if let Entry::Occupied(mut entry) = self.live_message_sinks.entry(topic) {
				debug!(target: "gossip", "Pushing relevant consensus message to sink.");
				if let Err(e) = entry.get().unbounded_send(message.clone()) {
					trace!(target:"gossip", "Error broadcasting message notification: {:?}", e);
				}

				if entry.get().is_closed() {
					entry.remove_entry();
				}
			}
		} else {
			trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
			return None;
		}

		Some((hash, message))
	}

	fn multicast(&mut self, protocol: &mut Context<B>, message: ConsensusMessage<B>, hash: Option<B::Hash>) {
		let generic = match message {
			ConsensusMessage::Bft(ref message) => GenericMessage::BftMessage(message.clone()),
			ConsensusMessage::ChainSpecific(ref message, _) => GenericMessage::ChainSpecific(message.clone()),
		};

		let hash = hash.unwrap_or_else(|| ::protocol::hash_message(&generic));
		self.register_message(hash, message);
		self.propagate(protocol, generic, hash);
	}

	/// Note new consensus session.
	pub fn new_session(&mut self, parent_hash: B::Hash) {
		let old_session = self.session_start.take();
		self.session_start = Some(parent_hash);
		self.collect_garbage(|topic| old_session.as_ref().map_or(true, |h| topic != h));
	}
}

impl<Block: BlockT> Specialization<Block> for ConsensusGossip<Block> where
	Block::Header: HeaderT<Number=u64>
{
	fn status(&self) -> Vec<u8> {
		Vec::new()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, who: NodeIndex, status: StatusMessage<Block>) {
		self.new_peer(ctx, who, status.roles);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, who: NodeIndex) {
		self.peer_disconnected(ctx, who);
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, who: NodeIndex, message: &mut Option<message::Message<Block>>) {
		match message.take() {
			Some(generic_message::Message::BftMessage(msg)) => {
				trace!(target: "gossip", "BFT message from {}: {:?}", who, msg);
				// TODO: check signature here? what if relevant block is unknown?
				self.on_bft_message(ctx, who, msg)
			}
			r => *message = r,
		}
	}

	fn on_abort(&mut self) {
		self.abort();
	}

	fn maintain_peers(&mut self, _ctx: &mut Context<Block>) {
		self.collect_garbage(|_| true);
	}

	fn on_block_imported(
		&mut self,
		_ctx: &mut Context<Block>,
		_hash: <Block as BlockT>::Hash,
		_header: &<Block as BlockT>::Header)
	{}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::bft::Justification;
	use runtime_primitives::testing::{H256, Header, Block as RawBlock};
	use std::time::Instant;
	use message::{self, generic};
	use super::*;

	type Block = RawBlock<u64>;

	#[test]
	fn collects_garbage() {
		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = ConsensusGossip::<Block>::new();
		let now = Instant::now();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = ConsensusMessage::Bft(message::LocalizedBftMessage {
			parent_hash: prev_hash,
			message: message::generic::BftMessage::Auxiliary(Justification {
				round_number: 0,
				hash: Default::default(),
				signatures: Default::default(),
			}),
		});
		let m2 = ConsensusMessage::ChainSpecific(vec![1, 2, 3], best_hash);

		macro_rules! push_msg {
			($hash:expr, $now: expr, $m:expr) => {
				consensus.messages.push(MessageEntry {
					hash: $hash,
					instant: $now,
					message: $m,
				})
			}
		}

		push_msg!(m1_hash, now, m1);
		push_msg!(m2_hash, now, m2.clone());
		consensus.message_hashes.insert(m1_hash);
		consensus.message_hashes.insert(m2_hash);

		// nothing to collect
		consensus.collect_garbage(|_topic| true);
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// random header, nothing should be cleared
		let mut header = Header {
			parent_hash: H256::default(),
			number: 0,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Default::default(),
		};

		consensus.collect_garbage(|&topic| topic != Default::default());
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// header that matches one of the messages
		header.parent_hash = prev_hash;
		consensus.collect_garbage(|topic| topic != &prev_hash);
		assert_eq!(consensus.messages.len(), 1);
		assert_eq!(consensus.message_hashes.len(), 1);
		assert!(consensus.message_hashes.contains(&m2_hash));

		// make timestamp expired
		consensus.messages.clear();
		push_msg!(m2_hash, now - MESSAGE_LIFETIME, m2);
		consensus.collect_garbage(|_topic| true);
		assert!(consensus.messages.is_empty());
		assert!(consensus.message_hashes.is_empty());
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::new();

		let bft_message = generic::BftMessage::Consensus(generic::SignedConsensusMessage::Vote(generic::SignedConsensusVote {
			vote: generic::ConsensusVote::AdvanceRound(0),
			sender: [0; 32].into(),
			signature: Default::default(),
		}));

		let parent_hash = [1; 32].into();

		let localized = ::message::LocalizedBftMessage::<Block> {
			message: bft_message,
			parent_hash: parent_hash,
		};

		let message = generic::Message::BftMessage(localized.clone());
		let message_hash = ::protocol::hash_message::<Block>(&message);

		let message = ConsensusMessage::Bft(localized);
		consensus.register_message(message_hash, message.clone());
		let stream = consensus.messages_for(parent_hash);

		assert_eq!(stream.wait().next(), Some(Ok(message)));
	}
}
