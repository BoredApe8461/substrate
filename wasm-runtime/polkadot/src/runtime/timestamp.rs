use primitives::Timestamp;
use storage::Storage;

pub fn get() -> Timestamp {
	Storage::into(b"tim\0val")
}

pub fn set(now: Timestamp) {
	now.store(b"tim\0val")
}

#[cfg(test)]
mod tests {
	use joiner::Joiner;
	use keyedvec::KeyedVec;
	use runtime_support::with_externalities;
	use runtime::timestamp;
	use testing::TestExternalities;

	#[test]
	fn timestamp_works() {
		let mut t = TestExternalities { storage: map![
			b"tim\0val".to_vec() => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(timestamp::get(), 42);
			timestamp::set(69);
			assert_eq!(timestamp::get(), 69);
		});
	}
}
