# ct-kemeleon

This is a work-in-progress crate for experimenting with and implementing the [Kemeleon](https://datatracker.ietf.org/doc/draft-veitch-kemeleon/) encoding algorithm(s).

Kemeleon encodes ML-KEM public keys and ciphertexts as uniform-looking bytestrings.
This is useful when you want to hide the fact that a message contains cryptographic material at all (e.g., in [obfuscated key exchange](https://eprint.iacr.org/2024/1086)), or when we require an ideal cipher to operate on public keys or ciphertexts, such as in [some PAKEs](https://eprint.iacr.org/2023/470).

## Warning

None of the code in this repo has been audited by a third party. Use at your own peril.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
