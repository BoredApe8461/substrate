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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use std::sync::Arc;
use std::collections::{BTreeMap};
use std::io;
use std::time::Duration;
use futures::sync::{oneshot, mpsc};
use network::{NetworkProtocolHandler, NetworkContext, HostInfo, PeerId, ProtocolId,
NetworkConfiguration , NonReservedPeerMode, ErrorKind};
use network_devp2p::{NetworkService};
use primitives::block::{ExtrinsicHash, Header, HeaderHash};
use primitives::Hash;
use core_io::{TimerToken};
use io::NetSyncIo;
use protocol::{Protocol, ProtocolStatus, PeerInfo as ProtocolPeerInfo, TransactionStats};
use config::{ProtocolConfig};
use error::Error;
use chain::Client;
use message::LocalizedBftMessage;

/// Polkadot devp2p protocol id
pub const DOT_PROTOCOL_ID: ProtocolId = *b"dot";

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;
/// Type that represents bft messages stream.
pub type BftMessageStream = mpsc::UnboundedReceiver<LocalizedBftMessage>;

const TICK_TOKEN: TimerToken = 0;
const TICK_TIMEOUT: Duration = Duration::from_millis(1000);

const PROPAGATE_TOKEN: TimerToken = 1;
const PROPAGATE_TIMEOUT: Duration = Duration::from_millis(5000);

bitflags! {
	/// Node roles bitmask.
	pub struct Role: u32 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, doe not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as an authority
		const AUTHORITY = 0b00000100;
	}
}

/// Sync status
pub trait SyncProvider: Send + Sync {
	/// Get sync status
	fn status(&self) -> ProtocolStatus;
	/// Get peers information
	fn peers(&self) -> Vec<PeerInfo>;
	/// Get this node id if available.
	fn node_id(&self) -> Option<String>;
	/// Returns propagation count for pending transactions.
	fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats>;
}

/// Transaction pool interface
pub trait TransactionPool: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)>;
	/// Import a transction into the pool.
	fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash>;
}

/// ConsensusService
pub trait ConsensusService: Send + Sync {
	/// Maintain connectivity to given addresses.
	fn connect_to_authorities(&self, addresses: &[String]);
	/// Get BFT message stream for messages corresponding to consensus on given
	/// parent hash.
	fn bft_messages(&self, parent_hash: Hash) -> BftMessageStream;
	/// Send out a BFT message.
	fn send_bft_message(&self, message: LocalizedBftMessage);
}

/// devp2p Protocol handler
struct ProtocolHandler {
	protocol: Protocol,
}

/// Peer connection information
#[derive(Debug)]
pub struct PeerInfo {
	/// Public node id
	pub id: Option<String>,
	/// Node client ID
	pub client_version: String,
	/// Capabilities
	pub capabilities: Vec<String>,
	/// Remote endpoint address
	pub remote_address: String,
	/// Local endpoint address
	pub local_address: String,
	/// Dot protocol info.
	pub dot_info: Option<ProtocolPeerInfo>,
}

/// Service initialization parameters.
pub struct Params {
	/// Configuration.
	pub config: ProtocolConfig,
	/// Network layer configuration.
	pub network_config: NetworkConfiguration,
	/// Polkadot relay chain access point.
	pub chain: Arc<Client>,
	/// Transaction pool.
	pub transaction_pool: Arc<TransactionPool>,
}

/// Polkadot network service. Handles network IO and manages connectivity.
pub struct Service {
	/// Network service
	network: NetworkService,
	/// Devp2p protocol handler
	handler: Arc<ProtocolHandler>,
}

impl Service {
	/// Creates and register protocol with the network service
	pub fn new(params: Params) -> Result<Arc<Service>, Error> {
		let service = NetworkService::new(params.network_config.clone(), None)?;
		let sync = Arc::new(Service {
			network: service,
			handler: Arc::new(ProtocolHandler {
				protocol: Protocol::new(params.config, params.chain.clone(), params.transaction_pool)?,
			}),
		});

		Ok(sync)
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: HeaderHash, header: &Header) {
		self.network.with_context(DOT_PROTOCOL_ID, |context| {
			self.handler.protocol.on_block_imported(&mut NetSyncIo::new(context), hash, header)
		});
	}

	/// Called when new transactons are imported by the client.
	pub fn trigger_repropagate(&self) {
		self.network.with_context(DOT_PROTOCOL_ID, |context| {
			self.handler.protocol.propagate_extrinsics(&mut NetSyncIo::new(context));
		});
	}

	fn start(&self) {
		match self.network.start().map_err(Into::into) {
			Err(ErrorKind::Io(ref e)) if  e.kind() == io::ErrorKind::AddrInUse =>
				warn!("Network port {:?} is already in use, make sure that another instance of Polkadot client is not running or change the port using the --port option.", self.network.config().listen_address.expect("Listen address is not set.")),
			Err(err) => warn!("Error starting network: {}", err),
			_ => {},
		};
		self.network.register_protocol(self.handler.clone(), DOT_PROTOCOL_ID, &[(::protocol::CURRENT_VERSION as u8, ::protocol::CURRENT_PACKET_COUNT)])
			.unwrap_or_else(|e| warn!("Error registering polkadot protocol: {:?}", e));
	}

	fn stop(&self) {
		self.handler.protocol.abort();
		self.network.stop().unwrap_or_else(|e| warn!("Error stopping network: {:?}", e));
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		self.stop();
	}
}

impl SyncProvider for Service {
	/// Get sync status
	fn status(&self) -> ProtocolStatus {
		self.handler.protocol.status()
	}

	/// Get sync peers
	fn peers(&self) -> Vec<PeerInfo> {
		self.network.with_context_eval(DOT_PROTOCOL_ID, |ctx| {
			let peer_ids = self.network.connected_peers();

			peer_ids.into_iter().filter_map(|peer_id| {
				let session_info = match ctx.session_info(peer_id) {
					None => return None,
					Some(info) => info,
				};

				Some(PeerInfo {
					id: session_info.id.map(|id| format!("{:x}", id)),
					client_version: session_info.client_version,
					capabilities: session_info.peer_capabilities.into_iter().map(|c| c.to_string()).collect(),
					remote_address: session_info.remote_address,
					local_address: session_info.local_address,
					dot_info: self.handler.protocol.peer_info(peer_id),
				})
			}).collect()
		}).unwrap_or_else(Vec::new)
	}

	fn node_id(&self) -> Option<String> {
		self.network.external_url()
	}

	fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats> {
		self.handler.protocol.transactions_stats()
	}
}

/// ConsensusService
impl ConsensusService for Service {
	fn connect_to_authorities(&self, _addresses: &[String]) {
		//TODO: implement me
	}

	fn bft_messages(&self, parent_hash: Hash) -> BftMessageStream {
		self.handler.protocol.bft_messages(parent_hash)
	}

	fn send_bft_message(&self, message: LocalizedBftMessage) {
		self.network.with_context(DOT_PROTOCOL_ID, |context| {
			self.handler.protocol.send_bft_message(&mut NetSyncIo::new(context), message);
		});
	}
}

impl NetworkProtocolHandler for ProtocolHandler {
	fn initialize(&self, io: &NetworkContext, _host_info: &HostInfo) {
		io.register_timer(TICK_TOKEN, TICK_TIMEOUT)
			.expect("Error registering sync timer");

		io.register_timer(PROPAGATE_TOKEN, PROPAGATE_TIMEOUT)
			.expect("Error registering transaction propagation timer");
	}

	fn read(&self, io: &NetworkContext, peer: &PeerId, _packet_id: u8, data: &[u8]) {
		self.protocol.handle_packet(&mut NetSyncIo::new(io), *peer, data);
	}

	fn connected(&self, io: &NetworkContext, peer: &PeerId) {
		self.protocol.on_peer_connected(&mut NetSyncIo::new(io), *peer);
	}

	fn disconnected(&self, io: &NetworkContext, peer: &PeerId) {
		self.protocol.on_peer_disconnected(&mut NetSyncIo::new(io), *peer);
	}

	fn timeout(&self, io: &NetworkContext, timer: TimerToken) {
		match timer {
			TICK_TOKEN => self.protocol.tick(&mut NetSyncIo::new(io)),
			PROPAGATE_TOKEN => self.protocol.propagate_extrinsics(&mut NetSyncIo::new(io)),
			_ => {}
		}
	}
}

/// Trait for managing network
pub trait ManageNetwork : Send + Sync {
	/// Set to allow unreserved peers to connect
	fn accept_unreserved_peers(&self);
	/// Set to deny unreserved peers to connect
	fn deny_unreserved_peers(&self);
	/// Remove reservation for the peer
	fn remove_reserved_peer(&self, peer: String) -> Result<(), String>;
	/// Add reserved peer
	fn add_reserved_peer(&self, peer: String) -> Result<(), String>;
	/// Start network
	fn start_network(&self);
	/// Stop network
	fn stop_network(&self);
}

impl ManageNetwork for Service {
	fn accept_unreserved_peers(&self) {
		self.network.set_non_reserved_mode(NonReservedPeerMode::Accept);
	}

	fn deny_unreserved_peers(&self) {
		self.network.set_non_reserved_mode(NonReservedPeerMode::Deny);
	}

	fn remove_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.network.remove_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.network.add_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn start_network(&self) {
		self.start();
	}

	fn stop_network(&self) {
		self.stop();
	}
}
