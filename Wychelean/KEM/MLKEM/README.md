# ML-KEM arithmetic

The executable arithmetic follows [FIPS 203](https://doi.org/10.6028/NIST.FIPS.203), Algorithms 9–12.
`Polynomial` retains its polynomial-ring representation. `Tq` stores 256 field coefficients in FIPS
order; component `i` consists of coefficients `2*i` and `2*i+1`, and its multiplicative identity is
128 copies of `(1, 0)`.

| Public operation | Executable definition |
| --- | --- |
| `f.ntt` | `NTT.forward`, Algorithm 9 |
| `a.nttInv` | `NTT.inverse`, Algorithm 10 |
| `a * b : Tq` | `NTT.multiply`, Algorithm 11, calling `NTT.baseCaseMultiply`, Algorithm 12 |

The seven stages, their blocks, and their butterfly pairs use bounded `Fin.foldl` traversals.
Forward lengths are 128 through 2; inverse lengths are 2 through 128. The inverse normalizes with
3303. Vector methods apply these operations entrywise. Matrix multiplication and inner products
retain the generic definitions in `Wychelean.Utils.PolyRing`.

## Modules and proofs

- `Parameters.lean` defines the parameters, polynomial types, and flat `Tq` representation.
- `NTT.lean` defines the executable arithmetic. `Basic`, `Layout`, and `Scheme` depend on it.
- `NTTRepresentation.lean` proves the coefficient conversions inverse and packages
  `Tq.abstractRingEquiv`, retaining the concrete arithmetic operations. Its `AbstractTq` abbreviation
  is definitionally `NTTDomain 7 ζ 256`, with dimensions reduced to 2 and 128 for elaboration.
- `NTTStages.lean` proves invariants for completed pairs and blocks, including the twiddle counters.
- `NTTEquivalence.lean` relates forward stage `s` to the recursive transform with root
  `17^(2^(7-s))`. Each inverse stage is twice the corresponding `splitInv`; its traversal accumulates
  a factor `2^7`, cancelled by 3303. `nttEquiv : Polynomial ≃+* Tq` uses the executable operations.
- `Properties.lean` exposes inverse, multiplication, coefficient-sum, scalar, and quotient-map results.

The main bridges quantify over every input:

```lean
toAbstract_ntt (f : Polynomial) : Tq.toAbstract f.ntt = abstractNTT f
nttInv_eq_abstract (a : Tq) : a.nttInv = abstractNTTInv a.toAbstract
Tq.toAbstract_mul (a b : Tq) : (a * b).toAbstract = a.toAbstract * b.toAbstract
```

The reusable recursive transforms and algebraic proofs live under the public namespace and import
path `Wychelean.Utils.PolyRing`. There are no compatibility modules at the former location.

## Verification

```sh
lake build
lake build runTests
lake test
lake test -- --full
lake test -- --only 'ML-KEM FIPS arithmetic'
```

`Tests/Arithmetic.lean` checks notation resolution by definitional equality and runs 70 comparisons
on zero, one, boundary monomials, dense polynomials, and arbitrary flat NTT inputs.
`Tests/Axioms.lean` guards the transitive axiom reports for the public bridges and arithmetic theorems:
only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No compiler-trust proof shortcut is
used. Source review of the FIPS transcription remains the connection to the standard's pseudocode.

## Validation record

Validated on 2026-09-20 with Lean `v4.34.0-rc2`:

- Library and native test-executable builds passed at the default Lean limits.
- Default suite: 15,628 checks passed; full suite: 18,711 checks passed.
- Existing ACVP and Wycheproof fixtures were unchanged.
- After making arithmetic test setup lazy, its 70 checks and the full ML-KEM subset's 1,977 checks
  passed again. The change only defers pure test evaluation until the suite is selected.
- Guarded transitive axiom checks passed. Source scans found no old namespace imports, removed-loop
  imports, proof placeholders, or compiler-trust proof shortcuts in the new arithmetic.

Native timing on the same machine and toolchain, including process startup, fixture loading, and
output, with compilation outside the measurements:

| Run | Baseline | FIPS arithmetic |
| --- | ---: | ---: |
| ACVP, 18 identical checks, median of three interleaved rounds | 2.63 s | 2.27 s |
| Full `--only ML-KEM` subset, one run | 159.04 s | 129.61 s |

The full subset grew from 1,907 to 1,977 checks. ACVP wall time decreased by about 14%; the full
subset took about 19% less time despite the additional checks. These are test-process timings,
not isolated transform benchmarks.

The new proof modules built in approximately 2.6–4.7 seconds each. Profiling identified bounded
traversal reasoning and typeclass inference as the main proof costs; kernel checking of the
transform-equivalence module took approximately 0.33 seconds. No heartbeat or recursion limit was
raised.
