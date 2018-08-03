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

use super::*;
use self::error::{Error, ErrorKind};

use client::BlockOrigin;
use jsonrpc_macros::pubsub;
use rustc_hex::FromHex;
use test_client::{self, runtime, keyring::Keyring, TestClient, BlockBuilderExt};


#[test]
fn should_return_storage() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();
	let client = State::new(client, core.executor());

	assert_matches!(
		client.storage_at(StorageKey(vec![10]), genesis_hash),
		Err(Error(ErrorKind::Client(client::error::ErrorKind::NoValueForKey(ref k)), _)) if *k == vec![10]
	)
}

#[test]
fn should_call_contract() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();
	let client = State::new(client, core.executor());

	assert_matches!(
		client.call_at("balanceOf".into(), vec![1,2,3], genesis_hash),
		Err(Error(ErrorKind::Client(client::error::ErrorKind::Execution(_)), _))
	)
}

#[test]
fn should_notify_about_storage_changes() {
	let mut core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = pubsub::Subscriber::new_test("test");

	{
		let api = State {
			client: Arc::new(test_client::new()),
			subscriptions: Subscriptions::new(remote),
		};

		api.subscribe_storage(Default::default(), subscriber, None.into());

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(0))));

		let mut builder = api.client.new_block().unwrap();
		builder.push_transfer(runtime::Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		}).unwrap();
		api.client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert notification sent to transport
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}

#[test]
fn should_send_initial_storage_changes_and_notifications() {
	let mut core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = pubsub::Subscriber::new_test("test");

	{
		let api = State {
			client: Arc::new(test_client::new()),
			subscriptions: Subscriptions::new(remote),
		};

		api.subscribe_storage(Default::default(), subscriber, Some(vec![
			StorageKey("a52da2b7c269da1366b3ed1cdb7299ce".from_hex().unwrap()),
		]).into());

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(0))));

		let mut builder = api.client.new_block().unwrap();
		builder.push_transfer(runtime::Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		}).unwrap();
		api.client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert initial values sent to transport
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// assert notification sent to transport
	let (notification, next) = core.block_on(next.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}
