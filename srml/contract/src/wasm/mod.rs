// Copyright 2018 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! This module provides a means for executing contracts
//! represented in wasm.

use exec::{Ext, OutputBuf, VmExecResult};
use gas::GasMeter;
use rstd::prelude::*;
use sandbox;
use wasm::env_def::FunctionImplProvider;
use {Schedule, Trait, CodeHash};

#[macro_use]
pub mod env_def;
pub mod runtime;
pub mod code;
pub mod prepare;

use self::runtime::{to_execution_result, Runtime};

pub struct WasmExecutable {
	entrypoint_name: &'static [u8],
	memory_def: code::MemoryDefinition,
	instrumented_code: Vec<u8>,
}

pub struct WasmLoader<'a, T: Trait> {
	schedule: &'a Schedule<T::Gas>,
}

impl<'a, T: Trait> WasmLoader<'a, T> {
	pub fn new(schedule: &'a Schedule<T::Gas>) -> Self {
		WasmLoader { schedule }
	}
}

impl<'a, T: Trait> ::exec::Loader<T> for WasmLoader<'a, T> {
	type Executable = WasmExecutable;

	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let dest_code = code::load::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"deploy",
			memory_def: dest_code.memory_def,
			instrumented_code: dest_code.code,
		})
	}
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let dest_code = code::load::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"call",
			memory_def: dest_code.memory_def,
			instrumented_code: dest_code.code,
		})
	}
}

pub struct WasmVm<'a, T: Trait> {
	schedule: &'a Schedule<T::Gas>,
}

impl<'a, T: Trait> WasmVm<'a, T> {
	pub fn new(schedule: &'a Schedule<T::Gas>) -> Self {
		WasmVm { schedule }
	}
}

impl<'a, T: Trait> ::exec::Vm<T> for WasmVm<'a, T> {
	type Executable = WasmExecutable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &WasmExecutable,
		ext: &mut E,
		input_data: &[u8],
		output_buf: OutputBuf,
		gas_meter: &mut GasMeter<E::T>,
	) -> VmExecResult {
		let memory = sandbox::Memory::new(exec.memory_def.initial, Some(exec.memory_def.maximum))
			.unwrap_or_else(|_| {
				panic!(
					"memory_def.initial can't be greater than memory_def.maximum;
					thus Memory::new must not fail;
					qed"
				)
			});

		let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
		imports.add_memory("env", "memory", memory.clone());
		runtime::Env::impls(&mut |name, func_ptr| {
			imports.add_host_func("env", name, func_ptr);
		});

		let mut runtime = Runtime::new(
			ext,
			input_data,
			output_buf,
			&self.schedule,
			memory,
			gas_meter,
		);

		// Instantiate the instance from the instrumented module code.
		match sandbox::Instance::new(&exec.instrumented_code, &imports, &mut runtime) {
			// No errors or traps were generated on instantiation! That
			// means we can now invoke the contract entrypoint.
			Ok(mut instance) => {
				let err = instance
					.invoke(exec.entrypoint_name, &[], &mut runtime)
					.err();
				to_execution_result(runtime, err)
			}
			// `start` function trapped. Treat it in the same manner as an execution error.
			Err(err @ sandbox::Error::Execution) => to_execution_result(runtime, Some(err)),
			Err(_err @ sandbox::Error::Module) => {
				// `Error::Module` is returned only if instantiation or linking failed (i.e.
				// wasm bianry tried to import a function that is not provided by the host).
				// This shouldn't happen because validation proccess ought to reject such binaries.
				//
				// Because panics are really undesirable in the runtime code, we treat this as
				// a trap for now. Eventually, we might want to revisit this.
				return VmExecResult::Trap("validation error");
			}
			// Other instantiation errors.
			// Return without executing anything.
			Err(_) => return VmExecResult::Trap("during start function"),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use exec::{CallReceipt, InstantiateReceipt, Ext, OutputBuf};
	use wasm::prepare::prepare_contract;
	use gas::GasMeter;
	use std::collections::HashMap;
	use tests::Test;
	use wabt;
	use CodeHash;

	#[derive(Debug, PartialEq, Eq)]
	struct CreateEntry {
		// TODO: code_hash: H256,
		endowment: u64,
		data: Vec<u8>,
		gas_left: u64,
	}
	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: u64,
		value: u64,
		data: Vec<u8>,
		gas_left: u64,
	}
	#[derive(Default)]
	pub struct MockExt {
		storage: HashMap<Vec<u8>, Vec<u8>>,
		creates: Vec<CreateEntry>,
		transfers: Vec<TransferEntry>,
		next_account_id: u64,
	}
	impl Ext for MockExt {
		type T = Test;

		fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
			self.storage.get(key).cloned()
		}
		fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
			*self.storage.entry(key.to_vec()).or_insert(Vec::new()) = value.unwrap_or(Vec::new());
		}
		fn instantiate(
			&mut self,
			_code_hash: &CodeHash<Test>,
			endowment: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
		) -> Result<InstantiateReceipt<u64>, &'static str> {
			self.creates.push(CreateEntry {
				// code_hash: code_hash.clone(),
				endowment,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			let address = self.next_account_id;
			self.next_account_id += 1;

			Ok(InstantiateReceipt { address })
		}
		fn call(
			&mut self,
			to: &u64,
			value: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
			_output_data: OutputBuf,
		) -> Result<CallReceipt, &'static str> {
			self.transfers.push(TransferEntry {
				to: *to,
				value,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			// Assume for now that it was just a plain transfer.
			// TODO: Add tests for different call outcomes.
			Ok(CallReceipt {
				output_data: Vec::new(),
			})
		}
		fn caller(&self) -> &u64 {
			&42
		}
		fn address(&self) -> &u64 {
			&69
		}
	}

	fn execute<E: Ext>(
		wat: &str,
		input_data: &[u8],
		output_data: &mut Vec<u8>,
		ext: &mut E,
		gas_meter: &mut GasMeter<E::T>,
	) -> Result<(), &'static str> {
		use exec::Vm;

		let wasm = wabt::wat2wasm(wat).unwrap();
		let schedule = ::Schedule::<u64>::default();
		let ::wasm::code::InstrumentedWasmModule {
			memory_def, code, ..
		} = prepare_contract::<Test, super::runtime::Env>(&wasm, &schedule).unwrap();

		let exec = WasmExecutable {
			// Use a "call" convention.
			entrypoint_name: b"call",
			memory_def,
			instrumented_code: code,
		};

		let cfg = Default::default();
		let vm = WasmVm::new(&cfg);

		*output_data = vm
			.execute(&exec, ext, input_data, OutputBuf::empty(), gas_meter)
			.into_result()?;

		Ok(())
	}

	const CODE_TRANSFER: &str = r#"
(module
	;; ext_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32
	;;) -> u32
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 8)  ;; Length of "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 12) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
				(i32.const 20) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
			)
		)
	)
	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")

	(data (i32.const 20) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_transfer() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_TRANSFER,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![1, 2, 3, 4],
				gas_left: 49970,
			}]
		);
	}

	const CODE_CREATE: &str = r#"
(module
	;; ext_create(
	;;     code_ptr: u32,
	;;     code_len: u32,
	;;     gas: u64,
	;;     value_ptr: u32,
	;;     value_len: u32,
	;;     input_data_ptr: u32,
	;;     input_data_len: u32,
	;; ) -> u32
	(import "env" "ext_create" (func $ext_create (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_create
				(i32.const 16)   ;; Pointer to `code_hash`
				(i32.const 32)   ;; Length of `code_hash`
				(i64.const 0)    ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)    ;; Pointer to the buffer with value to transfer
				(i32.const 8)    ;; Length of the buffer with value to transfer
				(i32.const 12)   ;; Pointer to input data buffer address
				(i32.const 4)    ;; Length of input data buffer
			)
		)
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Input data to pass to the contract being created.
	(data (i32.const 12) "\01\02\03\04")
	;; Hash of code.
	(data (i32.const 16) "\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11")
)
"#;

	#[test]
	fn contract_create() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_CREATE,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.creates,
			&[CreateEntry {
				// code: vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00],
				endowment: 3,
				data: vec![1, 2, 3, 4],
				gas_left: 49946,
			}]
		);
	}

	const CODE_TRANSFER_LIMITED_GAS: &str = r#"
(module
	;; ext_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32
	;;) -> u32
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 8)  ;; Length of "callee" address.
				(i64.const 228)  ;; How much gas to devote for the execution.
				(i32.const 12)  ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer.
				(i32.const 20)   ;; Pointer to input data buffer address
				(i32.const 4)   ;; Length of input data buffer
			)
		)
	)
	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")

	(data (i32.const 20) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call_limited_gas() {
		let mut mock_ext = MockExt::default();
		execute(
			&CODE_TRANSFER_LIMITED_GAS,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![1, 2, 3, 4],
				gas_left: 228,
			}]
		);
	}

	const CODE_GET_STORAGE: &str = r#"
(module
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(local $buf_size i32)


		;; Load a storage value into the scratch buf.
		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 4)		;; The pointer to the storage key to fetch
				)

				;; Return value 0 means that the value is found and there were
				;; no errors.
				(i32.const 0)
			)
		)

		;; Find out the size of the scratch buffer
		(set_local $buf_size
			(call $ext_scratch_size)
		)

		;; Copy scratch buffer into this contract memory.
		(call $ext_scratch_copy
			(i32.const 36)		;; The pointer where to store the scratch buffer contents,
								;; 36 = 4 + 32
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(get_local			;; Count of bytes to copy.
				$buf_size
			)
		)

		;; Return the contents of the buffer
		(call $ext_return
			(i32.const 36)
			(get_local $buf_size)
		)

		;; env:ext_return doesn't return, so this is effectively unreachable.
		(unreachable)
	)

	(data (i32.const 4) "\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11")
)
"#;

	#[test]
	fn get_storage_puts_data_into_scratch_buf() {
		let mut mock_ext = MockExt::default();
		mock_ext
			.storage
			.insert([0x11; 32].to_vec(), [0x22; 32].to_vec());

		let mut return_buf = Vec::new();
		execute(
			CODE_GET_STORAGE,
			&[],
			&mut return_buf,
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(return_buf, [0x22; 32].to_vec());
	}

	/// calls `ext_caller`, loads the address from the scratch buffer and
	/// compares it with the constant 42.
	const CODE_CALLER: &'static str = r#"
(module
	(import "env" "ext_caller" (func $ext_caller))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the scratch buffer with the caller.
		(call $ext_caller)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 42.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 42)
			)
		)
	)
)
"#;

	#[test]
	fn caller() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_CALLER,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();
	}

	const CODE_RETURN_FROM_START_FN: &str = r#"
(module
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(start $start)
	(func $start
		(call $ext_return
			(i32.const 8)
			(i32.const 4)
		)
		(unreachable)
	)

	(func (export "call")
	)

	(data (i32.const 8) "\01\02\03\04")
)
"#;

	#[test]
	fn return_from_start_fn() {
		let mut mock_ext = MockExt::default();
		let mut output_data = Vec::new();
		execute(
			CODE_RETURN_FROM_START_FN,
			&[],
			&mut output_data,
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(output_data, vec![1, 2, 3, 4]);
	}

	// TODO: address
}
