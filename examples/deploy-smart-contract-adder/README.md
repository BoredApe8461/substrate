* Run Rust binary program

```shell
cargo run
```

* Known Bugs
  * Error relating to `ADDER_INIT_CODE`: `^^^^^^^^^^^^^^^ doesn't have a size known at compile-time`

* References:
	* Web 3 Summit Video - Smart Contract Deployment: https://youtu.be/26ucTSSaqog?t=5298

	* "Adder" Smart Contract Source Code - https://github.com/pepyakin/substrate-contracts-adder

	* Copy of code used in Demo is included in a file in this program for reference: just_for_demo.patch

  * Note that in the video tests are run as follows to run code
    ```
    cargo test -p node-executor --nocapture just_for_demo
    cargo test -p node-executor --nocapture pepyakin
    ```
