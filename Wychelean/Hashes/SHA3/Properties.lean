import Wychelean.Hashes.SHA3.Basic

/-!
# Properties of the SHA-3 specification (FIPS 202)

## Pure spec-level properties

1. KECCAK-f = KECCAK-p[1600, 24] (§3.4) — by definition.
2. Padding length ≥ 2 (§5.1).
3. Domain separation: hash and RawSHAKE suffixes are distinct (§6.1, §6.3).
4. ρ offsets table matches Algorithm 2 (§3.2.2).

## Spec-side helpers used by the code-verification bridge

This file collects spec-only properties of the FIPS 202 SHA-3 specification
that are reused by the code-verification proofs in `Properties/SHA3/`.

- `stringToState` ↔ `stateToString` round-trips (§3.1.2–3.1.3).
- Byte/bit access bridges for `bitsToBytes` / `bytesToBits` (Algorithms 3 & 4):
  point-wise characterizations that are awkward to derive from the
  `Fin.foldl` / `Nat.testBit` definitions.
- `SPONGE.squeeze` block-level characterization (`squeezeBlocks` +
  `SPONGE_squeeze_blocks` family): expresses the squeeze as a
  concatenation of whole r-bit rate blocks `Trunc r (f^[j] S)`.
-/

namespace Wychelean.Hashes.SHA3

open scoped Wychelean.Notations

scoped macro_rules
| `(tactic| get_elem_tactic) => `(tactic| grind)

/-! ## Layer 0: Pure spec-level properties -/

theorem KECCAK_f_eq : KECCAK_f = KECCAK_p 24 := rfl

theorem padLen_ge_two (x m : Nat) : padLen x m ≥ 2 := by
  simp [padLen]

theorem hash_raw_suffixes_distinct : hashSuffix ≠ rawSuffix := by decide

/-! ## ρ offsets verification (§3.2.2, Table 2)

Table 2 of FIPS 202 lists the rotation offsets. We verify that the
algorithmic definition `ρ.Offsets` (from Algorithm 2) matches. -/

/-- Table 2 (§3.2.2): precomputed ρ rotation offsets. -/
def ρOffsetsTable2 : Vector (Vector Nat 5) 5 := #v[
  #v[  0,  36,   3, 105, 210],
  #v[  1, 300,  10,  45,  66],
  #v[190,   6, 171,  15, 253],
  #v[ 28,  55, 153,  21, 120],
  #v[ 91, 276, 231, 136,  78]]

/-- Algorithm 2 matches Table 2 (§3.2.2). -/
theorem rhoOffsets_eq_table2 : ρ.Offsets = ρOffsetsTable2 := by native_decide


/-! ## stringToState / stateToString round-trips

These are fundamental properties of the spec's state↔string conversions (§3.1.2–3.1.3).
They hold by elementary index arithmetic:
- lane index = i / w, x = lane % 5, y = lane / 5, z = i % w
- 5 * (lane / 5) + (lane % 5) = lane (division algorithm)
- w * (i / w) + (i % w) = i (division algorithm) -/

/-- Round-trip: `stringToState ∘ stateToString = id`. -/
theorem stringToState_stateToString (A : State) :
    stringToState (stateToString A) = A := by
  apply Vector.ext
  intro x hx
  apply Vector.ext
  intro y hy
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  change z < 64 at hz
  simp only [stringToState, Vector.getElem_ofFn, BitVec.getLsbD_ofBitsLE _ _ hz,
    stateToString]
  have h1 : (64 * (5 * y + x) + z) / 64 = 5 * y + x := by omega
  have h2 : (64 * (5 * y + x) + z) % 64 = z := by omega
  have h3 : (5 * y + x) % 5 = x := by omega
  have h4 : (5 * y + x) / 5 = y := by omega
  simp only [w, h1, h2, h3, h4]

/-- Round-trip: `stateToString ∘ stringToState = id`. -/
theorem stateToString_stringToState (S : Vector Bool b) :
    stateToString (stringToState S) = S := by
  simp only [stateToString, stringToState]
  ext i hi
  simp only [Vector.getElem_ofFn]
  rw [BitVec.getLsbD_ofBitsLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [Vector.getElem_ofFn]
  simp only [show w = 64 from rfl, show b = 1600 from rfl] at hi ⊢
  have h1 : 64 * (5 * (i / 64 / 5) + i / 64 % 5) + i % 64 = i := by omega
  simp only [h1]


end Wychelean.Hashes.SHA3
