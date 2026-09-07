# Wychelean

This repo contains Lean4 specifications for common cryptographic algorithms.

# Guarantee

Every specification in this repo:

1. Passes unit tests from NIST, [Wycheproof](https://github.com/C2SP/wycheproof), and or [CCTV](https://github.com/C2SP/CCTV)
2. A human has inspected the specification

We aim to produce a trustworthy base from which reliable software can be built. Use of an LLM is permitted, but the human author is ultimately held responsible for its output.

# Testing

To run known-answer tests, just run `lake test`

Each specification's known-answer tests live next to it, e.g. the Curve25519 vectors are in
`Wychelean/Curves/Curve25519/Tests.lean`. They are written against the hex strings the source
documents print, so a test vector can be checked against its specification by eye. The harness
they use is `KnownAnswerTests/Basic.lean`, and `KnownAnswerTests/Main.lean` lists every suite to
run; adding a new one means importing its module there. Test modules are built by `lake test`
only, not by `lake build`.

# License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
* MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
