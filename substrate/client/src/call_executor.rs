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

use std::sync::Arc;

use primitives::block::Id as BlockId;
use state_machine::{self, OverlayedChanges, Backend as StateBackend, CodeExecutor};

use backend;
use error;

/// Information regarding the result of a call.
#[derive(Debug, Clone)]
pub struct CallResult {
	/// The data that was returned from the call.
	pub return_data: Vec<u8>,
	/// The changes made to the state by the call.
	pub changes: OverlayedChanges,
}

/// Method call executor.
pub trait CallExecutor {
	/// Externalities error type.
	type Error: state_machine::Error;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> Result<CallResult, error::Error>;

	/// Execute a call to a contract on top of given state.
	///
	/// No changes are made.
	fn call_at_state<S: state_machine::Backend>(&self, state: &S, overlay: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, S::Transaction), error::Error>;

	/// Execute a call to a contract on top of given state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_state<S: state_machine::Backend>(&self, state: S, overlay: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error>;
}

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
}

impl<B, E> LocalCallExecutor<B, E> {
	/// Creates new instance of local call executor.
	pub fn new(backend: Arc<B>, executor: E) -> Self {
		LocalCallExecutor { backend, executor }
	}
}

impl<B, E> Clone for LocalCallExecutor<B, E> where E: Clone {
	fn clone(&self) -> Self {
		LocalCallExecutor {
			backend: self.backend.clone(),
			executor: self.executor.clone(),
		}
	}
}

impl<B, E> CallExecutor for LocalCallExecutor<B, E>
	where
		B: backend::LocalBackend,
		E: CodeExecutor,
		error::Error: From<<<B as backend::Backend>::State as StateBackend>::Error>,
{
	type Error = E::Error;

	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let mut changes = OverlayedChanges::default();
		let (return_data, _) = self.call_at_state(&self.backend.state_at(*id)?, &mut changes, method, call_data)?;
		Ok(CallResult{ return_data, changes })
	}

	fn call_at_state<S: state_machine::Backend>(&self, state: &S, changes: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, S::Transaction)> {
		state_machine::execute(
			state,
			changes,
			&self.executor,
			method,
			call_data,
		).map_err(Into::into)
	}

	fn prove_at_state<S: state_machine::Backend>(&self, state: S, changes: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error> {
		state_machine::prove_execution(
			state,
			changes,
			&self.executor,
			method,
			call_data,
		)
		.map(|(result, proof, _)| (result, proof))
		.map_err(Into::into)
	}
}
