# Wychelean

This repo contains Lean4 specifications for common cryptographic algorithms.

# Our Guarantee

Every specification in this repo:

1. Passes known-answer tests, and
2. Has had a human inspect the specification

We aim to produce a trustworthy base from which reliable software can be built. Use of an LLM is permitted, but the human author is ultimately held responsible for its output.

# Building

First run `lake exec cache get` to fetch the mathlib cache.

Then run `lake build` to build the library and verify all the theorems.

# Testing

Run `lake test` from the repository root. It builds and runs the native `RunTests` executable.

Every primitive contains its own tests in `Tests.lean`. Suites are registered in
`RunTests/Main.lean`; each suite loads its fixtures and evaluates its checks when it runs.
The ordinary `lake build` target does not import the test suites.

SHA256 reads the checked-in `SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`, and
`SHA256Monte.rsp` files in `Wychelean/Hashes/SHA256/Vectors/`. These are unmodified files from
the [NIST CAVP byte-oriented SHA vectors](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip).
All 65 short-message vectors, 64 long-message vectors, and 100 Monte Carlo checkpoints
(100,000 hashes) run by default. No network access is needed to load the fixtures.

`RunTests/Rsp.lean` provides the reusable response-file parser. It preserves headers,
records, fields, bare flags, and line numbers; each algorithm validates its own schema.
Missing or malformed fixtures, unexpected vector counts, and digest mismatches fail the run.

# Docs

To build docs:
* `cd docbuild`
* `lake build Wychelean:docs` this will take a while
* `cd .lake/build/doc`
* `python3 -m http.server 8080`
* Open your web browser to `localhost:8080`

# License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
* MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
