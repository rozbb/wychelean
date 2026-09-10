import Wychelean.Hashes.Keccak.Basic

namespace Wychelean.Hashes.Keccak
open Wychelean
open scoped Wychelean.Notations

/-- Padding always produces a total length divisible by x.
    Used to discharge the `blocks` divisibility precondition.
    Proof: `pad10*1(x, m)` has length `j + 2` where `j = (−m − 2) mod x`,
    so `m + j + 2 ≡ m + (−m − 2) + 2 ≡ 0 (mod x)`. -/
theorem padLen_dvd (r n : Nat) (hr : 0 < r := by grind) : (n + padLen r n) % r = 0 := by
  simp only [padLen, padLen.j]
  have hnn : (-(↑n : Int) - 2) % ↑r ≥ 0 := Int.emod_nonneg _ (by omega)
  have h_eq : (n : Int) + (1 + ((-(↑n : Int) - 2) % ↑r).toNat + 1) =
    ((-(↑n : Int) - 2) % ↑r + ↑n + 2) := by omega
  have h_mod : ((-(↑n : Int) - 2) % ↑r + ↑n + 2) % ↑r = 0 := by
    have := Int.emod_add_mul_ediv (-(n : Int) - 2) r
    rw [show (-(↑n : Int) - 2) % ↑r + ↑n + 2 = -(↑r * ((-(↑n : Int) - 2) / ↑r)) from by omega]
    exact Int.neg_mul_emod_right r _
  grind

/-- The state at position i does not depend on how many later states are requested. -/
theorem squeezeStates_prefix (f : α → α) (S : α) (k j i : Nat) (hi : i ≤ k) (hj : k ≤ j) :
    (squeezeStates f S j)[i] = (squeezeStates f S k)[i] := by
  induction j with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ j ih =>
    by_cases h : k ≤ j
    · simp only [squeezeStates, Vector.getElem_push]
      rw [dite_eq_left (by omega)]
      exact ih h
    · have : k = j + 1 := by omega
      subst k
      rfl

/-- Squeezing a shorter output is exactly a prefix of a longer output. -/
theorem squeeze_prefix {b : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (S : Vector Bool b) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (squeeze f r S e hr) 0 d (by omega) = squeeze f r S d hr := by
  apply Vector.ext
  intro i hi
  simp only [slice, squeeze, Vector.getElem_ofFn, Nat.zero_add]
  congr 1
  apply squeezeStates_prefix
  · exact Nat.div_le_div_right (by omega)
  · exact Nat.div_le_div_right h

theorem SPONGE_fn_prefix {b : Nat} (f : Vector Bool b → Vector Bool b) (r n : Nat)
    (N : Fin n → Bool) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (SPONGE_fn f r n N e hr) 0 d (by omega) = SPONGE_fn f r n N d hr :=
  squeeze_prefix f r _ d e hr h

theorem SPONGE_prefix {b n : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (N : Vector Bool n) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (SPONGE f r N e hr) 0 d (by omega) = SPONGE f r N d hr :=
  squeeze_prefix f r _ d e hr h

/-- FIPS 202 §5.1 mandates both a leading and trailing one. -/
theorem padLen_ge_two (r n : Nat) : 2 ≤ padLen r n := by simp [padLen]

theorem pad_last (r n : Nat) : («pad10*1» r n)[padLen r n - 1]'(by simp [padLen]) = true := by
  unfold «pad10*1»
  change ((#v[true] ++ Vector.replicate (padLen.j r n) false) ++ #v[true])[padLen r n - 1] = true
  rw [Vector.getElem_append_right _ (by simp [padLen])]
  simp [padLen]

end Wychelean.Hashes.Keccak
