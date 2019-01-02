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

use {Trait, Module, GasSpent};
use runtime_primitives::traits::{As, CheckedMul, CheckedSub, Zero};
use runtime_support::StorageValue;
use balances;

#[cfg(test)]
use std::{
	any::Any,
	fmt::Debug,
};

#[must_use]
#[derive(Debug, PartialEq, Eq)]
pub enum GasMeterResult {
	Proceed,
	OutOfGas,
}

impl GasMeterResult {
	pub fn is_out_of_gas(&self) -> bool {
		match *self {
			GasMeterResult::OutOfGas => true,
			GasMeterResult::Proceed => false,
		}
	}
}

#[cfg(not(test))]
pub trait TestAuxiliaries {}
#[cfg(not(test))]
impl<T> TestAuxiliaries for T {}

#[cfg(test)]
pub trait TestAuxiliaries: Any + Debug + PartialEq + Eq {}
#[cfg(test)]
impl<T: Any + Debug + PartialEq + Eq> TestAuxiliaries for T {}

/// This trait represents a token that can be used for charging `GasMeter`.
/// There is no other way of charging it.
///
/// Implementing type is expected to be super lightweight hence `Copy` (`Clone` is added
/// for consistency). If inlined there should be no observable difference compared
/// to a hand-written code.
pub trait Token<T: Trait>: Copy + Clone + TestAuxiliaries {
	/// Metadata type, which the token can require for calculating the amount
	/// of gas to charge. Can be a some configuration type or
	/// just the `()`.
	type Metadata;

	/// Calculate amount of gas that should be taken by this token.
	///
	/// Returns `None` if the amount can't be calculated e.g. because of overflow.
	/// This situation is treated as if out of gas happened.
	fn calculate_amount(&self, metadata: &Self::Metadata) -> Option<T::Gas>;
}

pub struct GasMeter<T: Trait> {
	limit: T::Gas,
	/// Amount of gas left from initial gas limit. Can reach zero.
	gas_left: T::Gas,
	gas_price: T::Balance,

	#[cfg(test)]
	tokens: Vec<Box<dyn Any>>,
}
impl<T: Trait> GasMeter<T> {
	#[cfg(test)]
	pub fn with_limit(gas_limit: T::Gas, gas_price: T::Balance) -> GasMeter<T> {
		GasMeter {
			limit: gas_limit,
			gas_left: gas_limit,
			gas_price,
			#[cfg(test)]
			tokens: Vec::new(),
		}
	}

	/// Account for used gas.
	///
	/// Amount is calculated by the given `token`. If `token::calculate_amount` returns
	/// `None` then all available gas is consumed and `OutOfGas` is returned.
	///
	/// Returns `OutOfGas` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `Proceed`.
	///
	/// NOTE that amount is always consumed, i.e. if there is not enough gas
	/// then the counter will be set to zero.
	#[inline]
	pub fn charge<Tok: Token<T>>(&mut self, metadata: &Tok::Metadata, token: Tok) -> GasMeterResult {
		// Unconditionally add the token.
		#[cfg(test)]
		self.tokens.push(Box::new(token));

		let amount = match token.calculate_amount(metadata) {
			Some(amount_in_gas) => amount_in_gas,
			None => self.gas_left, // Consume everything
		};

		let new_value = match self.gas_left.checked_sub(&amount) {
			None => None,
			Some(val) if val.is_zero() => None,
			Some(val) => Some(val),
		};

		// We always consume the gas even if there is not enough gas.
		self.gas_left = new_value.unwrap_or_else(Zero::zero);

		match new_value {
			Some(_) => GasMeterResult::Proceed,
			None => GasMeterResult::OutOfGas,
		}
	}

	/// Allocate some amount of gas and perform some work with
	/// a newly created nested gas meter.
	///
	/// Invokes `f` with either the gas meter that has `amount` gas left or
	/// with `None`, if this gas meter has not enough gas to allocate given `amount`.
	///
	/// All unused gas in the nested gas meter is returned to this gas meter.
	pub fn with_nested<R, F: FnOnce(Option<&mut GasMeter<T>>) -> R>(
		&mut self,
		amount: T::Gas,
		f: F,
	) -> R {
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			f(None)
		} else {
			self.gas_left = self.gas_left - amount;
			let mut nested = GasMeter {
				limit: amount,
				gas_left: amount,
				gas_price: self.gas_price,
				#[cfg(test)]
				tokens: Vec::new(),
			};

			let r = f(Some(&mut nested));

			self.gas_left = self.gas_left + nested.gas_left;

			r
		}
	}

	pub fn gas_price(&self) -> T::Balance {
		self.gas_price
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> T::Gas {
		self.gas_left
	}

	/// Returns how much gas was spent.
	fn spent(&self) -> T::Gas {
		self.limit - self.gas_left
	}

	#[cfg(test)]
	fn tokens(&self) -> &[Box<dyn Any>] {
		&self.tokens
	}
}

/// Buy the given amount of gas.
///
/// Cost is calculated by multiplying the gas cost (taken from the storage) by the `gas_limit`.
/// The funds are deducted from `transactor`.
pub fn buy_gas<T: Trait>(
	transactor: &T::AccountId,
	gas_limit: T::Gas,
) -> Result<GasMeter<T>, &'static str> {
	// Check if the specified amount of gas is available in the current block.
	// This cannot underflow since `gas_spent` is never greater than `block_gas_limit`.
	let gas_available = <Module<T>>::block_gas_limit() - <Module<T>>::gas_spent();
	if gas_limit > gas_available {
		return Err("block gas limit is reached");
	}

	// Buy the specified amount of gas.
	let gas_price = <Module<T>>::gas_price();
	let b = <balances::Module<T>>::free_balance(transactor);
	let cost = <T::Gas as As<T::Balance>>::as_(gas_limit.clone())
		.checked_mul(&gas_price)
		.ok_or("overflow multiplying gas limit by price")?;

	let new_balance = b.checked_sub(&cost);
	if new_balance < Some(<balances::Module<T>>::existential_deposit()) {
		return Err("not enough funds for transaction fee");
	}

	<balances::Module<T>>::set_free_balance(transactor, b - cost);
	<balances::Module<T>>::decrease_total_stake_by(cost);
	Ok(GasMeter {
		limit: gas_limit,
		gas_left: gas_limit,
		gas_price,
		#[cfg(test)]
		tokens: Vec::new()
	})
}

/// Refund the unused gas.
pub fn refund_unused_gas<T: Trait>(transactor: &T::AccountId, gas_meter: GasMeter<T>) {
	// Increase total spent gas.
	// This cannot overflow, since `gas_spent` is never greater than `block_gas_limit`, which
	// also has T::Gas type.
	let gas_spent = <Module<T>>::gas_spent() + gas_meter.spent();
	<GasSpent<T>>::put(gas_spent);

	// Refund gas left by the price it was bought.
	let b = <balances::Module<T>>::free_balance(transactor);
	let refund = <T::Gas as As<T::Balance>>::as_(gas_meter.gas_left) * gas_meter.gas_price;
	<balances::Module<T>>::set_free_balance(transactor, b + refund);
	<balances::Module<T>>::increase_total_stake_by(refund);
}

#[cfg(test)]
macro_rules! match_tokens {
	($tokens_iter:ident,) => {
	};
	($tokens_iter:ident, $x:expr, $($rest:tt)*) => {
		{
			let next = ($tokens_iter).next().unwrap();
			let pattern = $x;
			let mut _pattern_typed_next_ref = &pattern;
			_pattern_typed_next_ref = next.downcast_ref().unwrap();
			assert_eq!(_pattern_typed_next_ref, &pattern);
		}

		match_tokens!($tokens_iter, $($rest)*);
	};
}

#[cfg(test)]
mod tests {
	use super::{GasMeter, Token};
	use tests::Test;

	/// A trivial token that charges 1 unit of gas.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct UnitToken;
	impl Token<Test> for UnitToken {
		type Metadata = ();
		fn calculate_amount(&self, _metadata: &()) -> Option<u64> {
			Some(1)
		}
	}

	struct DoubleTokenMetadata {
		multiplier: u64,
	}
	/// A simple token that charges for the given amount multipled to
	/// a multiplier taken from a given metadata.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct DoubleToken(u64);

	impl Token<Test> for DoubleToken {
		type Metadata = DoubleTokenMetadata;
		fn calculate_amount(&self, metadata: &DoubleTokenMetadata) -> Option<u64> {
			Some(self.0 * metadata.multiplier)
		}
	}

	#[test]
	fn it_works() {
		let gas_meter = GasMeter::<Test>::with_limit(50000, 10);
		assert_eq!(gas_meter.gas_left(), 50000);
	}

	#[test]
	fn simple() {
		let mut gas_meter = GasMeter::<Test>::with_limit(50000, 10);

		let result = gas_meter.charge(
			&DoubleTokenMetadata { multiplier: 3 },
			DoubleToken(10),
		);
		assert!(!result.is_out_of_gas());

		assert_eq!(gas_meter.gas_left(), 49_970);
		assert_eq!(gas_meter.spent(), 30);
		assert_eq!(gas_meter.gas_price(), 10);
	}

	#[test]
	fn tracing() {
		let mut gas_meter = GasMeter::<Test>::with_limit(50000, 10);
		assert!(!gas_meter.charge(&(), UnitToken).is_out_of_gas());
		assert!(!gas_meter.charge(
			&DoubleTokenMetadata { multiplier: 3 },
			DoubleToken(10),
		).is_out_of_gas());

		let mut tokens = gas_meter.tokens()[0..2].iter();
		match_tokens!(tokens,
			UnitToken,
			DoubleToken(10),
		);
	}
}
