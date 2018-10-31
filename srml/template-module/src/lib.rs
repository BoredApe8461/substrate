//! TODO: Documentation for the runtime module.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate sr_std;
#[cfg(test)]
extern crate sr_io;
#[cfg(test)]
extern crate substrate_primitives;
extern crate sr_primitives;
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate parity_codec_derive;
extern crate parity_codec as codec;
#[macro_use]
extern crate srml_support as support;
extern crate srml_system as system;

use support::{StorageValue, dispatch::Result};
use system::ensure_signed;

/// The module's configuration trait.
pub trait Trait: system::Trait {
	// TODO: Other types and constants that configure this module.

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_storage! {
	// This module's storage items.
	trait Store for Module<T: Trait> as TemplateModule {
		/// Just a dummy storage item. TODO: Documentation for this item (or just remove it).
		Something get(something) config(): Option<T::AccountId>;
	}
}

decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Just a dummy entry point. TODO: Documentation for this entry point (or just remove it).
		pub fn do_something(origin, _something: T::AccountId) -> Result {
			// TODO: You only need this if you want to check it was signed.
			let _who = ensure_signed(origin)?;
			// TODO: Code to execute when something calls this.
			Ok(())
		}

		fn on_finalise(_n: T::BlockNumber) {
			// TODO: Code to execute at the end of the block.
		}
	}
}

decl_event!(
	/// An event in this module.
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		/// Just a dummy event. TODO: Documentation for this event (or just remove it).
		Something(AccountId),
	}
);

#[cfg(test)]
mod tests {
	use super::*;

	use sr_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	use sr_primitives::{
		BuildStorage, traits::BlakeTwo256, testing::{Digest, DigestItem, Header}
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl Trait for Test {
		type Event = ();
	}
	type TemplateModule = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sr_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test>{
			something: 42,
		}.build_storage().unwrap());
		t.into()
	}

	#[test]
	fn it_works_for_default_value() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(TemplateModule::something(), Some(42));
		});
	}
}
