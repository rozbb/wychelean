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

Run `lake test`

Every primitive contains its own tests in `Tests.lean`. Running `lake test` calls `RunTests`.

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
