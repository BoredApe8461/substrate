* Run Rust binary program

```shell
cargo run -p deploy-smart-contract-adder
```

* Known Bugs
  * View current issues when you run `cargo run -p deploy-smart-contract-adder`

* References:
	* Web 3 Summit Video - Smart Contract Deployment: https://youtu.be/26ucTSSaqog?t=5298

	* "Adder" Smart Contract Source Code - https://github.com/pepyakin/substrate-contracts-adder

	* Copy of code used in Demo is included in a file in this program for reference: just_for_demo.patch

  * Note that in the video tests are run as follows to run code. These have not been included in this branch as we've implemented the code in binary program that we run instead.
    ```
    cargo test -p node-executor --nocapture just_for_demo
    cargo test -p node-executor --nocapture pepyakin
    ```
