# ML-KEM

The specification follows the pseudocode of [FIPS 203](https://doi.org/10.6028/NIST.FIPS.203)
and stands alone: it imports neither `Wychelean.Utils.PolyRing` nor its own proofs
(`Tests/Standalone.lean` enforces this). The proofs relating it to the ring library live in
`Properties/`.

## Specification

- `Parameters.lean`: `q`, `ζ = 17`, the parameter sets and byte lengths. `Polynomial` (an element
  of `R_q`) and `Tq` (an element of `T_q`) are coefficient arrays in `Zq^256` (§2.4.4). Both have
  coordinate-wise `+` and `-`; `Tq` multiplies by `MultiplyNTTs` (Eq. 2.8). There is no product on
  `Polynomial`: the pseudocode never multiplies in `R_q` (§2.4.5).
- `NTT.lean`: Algorithms 9–12 as the FIPS loops. `Polynomial.NTT` and `PolyVector.NTT` (and the
  inverses) are both opened where used, so `NTT(s)` resolves by the type of `s` (§2.4.8).
- `Basic.lean`: hash functions, Compress/Decompress, and Algorithms 7–8.
- `Encode.lean`: Algorithms 5–6 and their application to vectors.
- `Layout.lean`: typed keys and ciphertexts with their byte encodings.
- `Scheme.lean`: Algorithms 13–21.

Each algorithm is imperative (`Id.run do`, `for`, `while`), one statement per FIPS line, with
`-- Alg. N, step M` comments.

## Properties

- `Loops.lean`: the FIPS loops of Algorithms 9–11 equal the stage folds of `Stages.lean`
  (`NTT_eq_forward`, `NTTInv_eq_inverse`, `mul_eq_multiply`).
- `Ring.lean`: `Polynomial` as `ℤ_q[X]/(X^256 + 1)` of PolyRing (`Polynomial.ringEquiv`), its
  product, and `ζRoot`, ζ as a primitive 256-th root of unity.
- `Tq.lean`: `T_q` as the product of the 128 quadratic quotients (`Tq.abstractRingEquiv`).
- `NTTStages.lean`, `NTTEquivalence.lean`: each fold stage against the recursive transform of
  PolyRing; `nttEquiv : Polynomial ≃+* Tq`.
- `NTT.lean`: the public results, e.g. `nttInv_mul : NTTInv (NTT f * NTT g) = f * g` (Eq. 4.9),
  `ntt_eq_nttSpec` (Eq. 4.12), `mul_residue` (Eq. 4.14).

`Tests/Axioms.lean` guards the axioms of these results: only `propext`, `Classical.choice` and
`Quot.sound`.

## Verification

```sh
lake build
lake test
lake test -- --full
lake test -- --only 'ML-KEM'
```

On 2026-09-23 with Lean `v4.34.0-rc2`, `lake build` passed without warnings and `lake test`
passed all 15,628 checks, including the ACVP and Wycheproof ML-KEM vectors.
