# U256 

Pure Move language implementation of U256 numbers.

Would be nice to help with the `TODO` list, you can see it in the [header comment](sources/U256.move).

Supported features:
* mul
* div
* add
* sub
* shift left
* shift right
* compare
* if math overflows the contract crashes with abort code.

The audit still missed, so use at your own risk.

### Build

    aptos move build

### Test

    aptos move test

## License

Apache 2.0
