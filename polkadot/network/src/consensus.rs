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

//! Implementation of the traits for consensus networking for the polkadot protocol.

use bft;
use ed25519;
use substrate_network::{self as net, generic_message as msg};
use substrate_network::consensus_gossip::ConsensusMessage;
use polkadot_api::{PolkadotApi, LocalPolkadotApi};
use polkadot_consensus::{Network, SharedTable};
use polkadot_primitives::{Block, Hash, BlockId, SessionKey};

use futures::{future, prelude::*};
use futures::sync::mpsc;

use std::sync::Arc;

use tokio::runtime::TaskExecutor;

use super::{Message, NetworkService};
use router::Router;

/// Sink for output BFT messages.
pub struct BftSink<E> {
	network: Arc<NetworkService>,
	parent_hash: Hash,
	_marker: ::std::marker::PhantomData<E>,
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication<Block>;
	// TODO: replace this with the ! type when that's stabilized
	type SinkError = E;

	fn start_send(&mut self, message: bft::Communication<Block>) -> ::futures::StartSend<bft::Communication<Block>, E> {
		let network_message = net::LocalizedBftMessage {
			message: match message {
				bft::generic::Communication::Consensus(c) => msg::BftMessage::Consensus(match c {
					bft::generic::LocalizedMessage::Propose(proposal) => msg::SignedConsensusMessage::Propose(msg::SignedConsensusProposal {
						round_number: proposal.round_number as u32,
						proposal: proposal.proposal,
						digest: proposal.digest,
						sender: proposal.sender,
						digest_signature: proposal.digest_signature.signature,
						full_signature: proposal.full_signature.signature,
					}),
					bft::generic::LocalizedMessage::Vote(vote) => msg::SignedConsensusMessage::Vote(msg::SignedConsensusVote {
						sender: vote.sender,
						signature: vote.signature.signature,
						vote: match vote.vote {
							bft::generic::Vote::Prepare(r, h) => msg::ConsensusVote::Prepare(r as u32, h),
							bft::generic::Vote::Commit(r, h) => msg::ConsensusVote::Commit(r as u32, h),
							bft::generic::Vote::AdvanceRound(r) => msg::ConsensusVote::AdvanceRound(r as u32),
						}
					}),
				}),
				bft::generic::Communication::Auxiliary(justification) => msg::BftMessage::Auxiliary(justification.uncheck().into()),
			},
			parent_hash: self.parent_hash,
		};
		self.network.with_spec(
			move |spec, ctx| spec.consensus_gossip.multicast_bft_message(ctx, network_message)
		);
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
		Ok(Async::Ready(()))
	}
}

// check signature and authority validity of message.
fn process_bft_message(msg: msg::LocalizedBftMessage<Block, Hash>, local_id: &SessionKey, authorities: &[SessionKey]) -> Result<Option<bft::Communication<Block>>, bft::Error> {
	Ok(Some(match msg.message {
		msg::BftMessage::Consensus(c) => bft::generic::Communication::Consensus(match c {
			msg::SignedConsensusMessage::Propose(proposal) => bft::generic::LocalizedMessage::Propose({
				if &proposal.sender == local_id { return Ok(None) }
				let proposal = bft::generic::LocalizedProposal {
					round_number: proposal.round_number as usize,
					proposal: proposal.proposal,
					digest: proposal.digest,
					sender: proposal.sender,
					digest_signature: ed25519::LocalizedSignature {
						signature: proposal.digest_signature,
						signer: ed25519::Public(proposal.sender),
					},
					full_signature: ed25519::LocalizedSignature {
						signature: proposal.full_signature,
						signer: ed25519::Public(proposal.sender),
					}
				};
				bft::check_proposal(authorities, &msg.parent_hash, &proposal)?;

				trace!(target: "bft", "importing proposal message for round {} from {}", proposal.round_number, Hash::from(proposal.sender));
				proposal
			}),
			msg::SignedConsensusMessage::Vote(vote) => bft::generic::LocalizedMessage::Vote({
				if &vote.sender == local_id { return Ok(None) }
				let vote = bft::generic::LocalizedVote {
					sender: vote.sender,
					signature: ed25519::LocalizedSignature {
						signature: vote.signature,
						signer: ed25519::Public(vote.sender),
					},
					vote: match vote.vote {
						msg::ConsensusVote::Prepare(r, h) => bft::generic::Vote::Prepare(r as usize, h),
						msg::ConsensusVote::Commit(r, h) => bft::generic::Vote::Commit(r as usize, h),
						msg::ConsensusVote::AdvanceRound(r) => bft::generic::Vote::AdvanceRound(r as usize),
					}
				};
				bft::check_vote::<Block>(authorities, &msg.parent_hash, &vote)?;

				trace!(target: "bft", "importing vote {:?} from {}", vote.vote, Hash::from(vote.sender));
				vote
			}),
		}),
		msg::BftMessage::Auxiliary(a) => {
			let justification = bft::UncheckedJustification::from(a);
			// TODO: get proper error
			let justification: Result<_, bft::Error> = bft::check_prepare_justification::<Block>(authorities, msg.parent_hash, justification)
				.map_err(|_| bft::ErrorKind::InvalidJustification.into());
			bft::generic::Communication::Auxiliary(justification?)
		},
	}))
}

// task that processes all gossipped consensus messages,
// checking signatures
struct MessageProcessTask<P: PolkadotApi> {
	inner_stream: mpsc::UnboundedReceiver<ConsensusMessage<Block>>,
	bft_messages: mpsc::UnboundedSender<bft::Communication<Block>>,
	validators: Vec<SessionKey>,
	table_router: Router<P>,
}

impl<P: LocalPolkadotApi + Send + Sync + 'static> Future for MessageProcessTask<P> where P::CheckedBlockId: Send {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<(), ()> {
		loop {
			match self.inner_stream.poll() {
				Ok(Async::Ready(Some(val))) => match val {
					ConsensusMessage::Bft(msg) => {
						let local_id = self.table_router.table.session_key();
						match process_bft_message(msg, &local_id, &self.validators[..]) {
							Ok(Some(msg)) => {
								if let Err(_) = self.bft_messages.unbounded_send(msg) {
									// if the BFT receiving stream has ended then
									// we should just bail.
									trace!(target: "bft", "BFT message stream appears to have closed");
									return Ok(Async::Ready(()));
								}
							}
							Ok(None) => {} // ignored local message
							Err(e) => {
								debug!("Message validation failed: {:?}", e);
							}
						}
					}
					ConsensusMessage::ChainSpecific(msg, _) => {
						if let Ok(Message::Statement(parent_hash, statement)) = ::serde_json::from_slice(&msg) {
							if ::polkadot_consensus::check_statement(&statement.statement, &statement.signature, statement.sender, &parent_hash) {
								self.table_router.import_statement(statement);
							}
						}
					}
				}
				Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
				Ok(Async::NotReady) => {},
				Err(e) => debug!(target: "p_net", "Error getting consensus message: {:?}", e),
			}
		}
	}
}

/// Input stream from the consensus network.
pub struct InputAdapter {
	input: mpsc::UnboundedReceiver<bft::Communication<Block>>,
}

impl Stream for InputAdapter {
	type Item = bft::Communication<Block>;
	type Error = ::polkadot_consensus::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		match self.input.poll() {
			Err(_) | Ok(Async::Ready(None)) => Err(bft::InputStreamConcluded.into()),
			Ok(x) => Ok(x)
		}
	}
}

/// Wrapper around the network service
pub struct ConsensusNetwork<P> {
	network: Arc<NetworkService>,
	api: Arc<P>,
}

impl<P> ConsensusNetwork<P> {
	/// Create a new consensus networking object.
	pub fn new(network: Arc<NetworkService>, api: Arc<P>) -> Self {
		ConsensusNetwork { network, api }
	}
}

/// A long-lived network which can create parachain statement and BFT message routing processes on demand.
impl<P: LocalPolkadotApi + Send + Sync + 'static> Network for ConsensusNetwork<P> where P::CheckedBlockId: Send {
	type TableRouter = Router<P>;
	/// The input stream of BFT messages. Should never logically conclude.
	type Input = InputAdapter;
	/// The output sink of BFT messages. Messages sent here should eventually pass to all
	/// current validators.
	type Output = BftSink<::polkadot_consensus::Error>;

	/// Instantiate a table router using the given shared table.
	fn communication_for(&self, validators: &[SessionKey], table: Arc<SharedTable>, task_executor: TaskExecutor) -> (Self::TableRouter, Self::Input, Self::Output) {
		let parent_hash = table.consensus_parent_hash().clone();

		let sink = BftSink {
			network: self.network.clone(),
			parent_hash,
			_marker: Default::default(),
		};

		let (bft_send, bft_recv) = mpsc::unbounded();

		let checked_parent_hash = match self.api.check_id(BlockId::hash(parent_hash)) {
			Ok(checked) => Some(checked),
			Err(e) => {
				warn!(target: "p_net", "Unable to evaluate candidates: unknown block ID: {}", e);
				None
			}
		};

		let table_router = Router {
			table,
			network: self.network.clone(),
			api: self.api.clone(),
			task_executor,
			parent_hash: checked_parent_hash,
		};

		// spin up a task in the background that processes all incoming statements
		// TODO: propagate statements on a timer?
		let process_task = self.network.with_spec(|spec, _ctx| {
			MessageProcessTask {
				inner_stream: spec.consensus_gossip.messages_for(parent_hash),
				bft_messages: bft_send,
				validators: validators.to_vec(),
				table_router: table_router.clone(),
			}
		});

		match process_task {
			Some(task) => table_router.task_executor.spawn(task),
			None => warn!(target: "p_net", "Cannot process incoming messages: network appears to be down"),
		}

		(table_router, InputAdapter { input: bft_recv }, sink)
	}
}
