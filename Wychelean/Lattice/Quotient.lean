import Wychelean.Lattice.Poly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod

/-!
# Coefficient vectors and the quotient rings

`Poly q n` with `Poly.mulBinomial c` is a computable representation of Mathlib's
`AdjoinRoot (X^n - C c)` over `ZMod q`: `Poly.toR c` sends a coefficient vector to the ring
element with those coefficients, respects addition and the product, and is injective. The case
`c = -1` is `ℤ_q[X] / (X^n + 1)`, the ring of the module-lattice schemes; the cases `c = γ` with
`n = 2` are the base-case rings of ML-KEM's NTT domain.
-/

namespace Wychelean.Lattice

open Polynomial

noncomputable section

/-- Mathlib's `ℤ_q[X] / (X^n - c)`. -/
abbrev R (q n : ℕ) (c : ZMod q) := AdjoinRoot ((X : (ZMod q)[X]) ^ n - C c)

namespace R

variable {q n : ℕ} {c : ZMod q}

/-- The image of `X`. -/
abbrev root : R q n c := AdjoinRoot.root _

theorem root_pow_n : (root : R q n c) ^ n = AdjoinRoot.of _ c := by
  have h := AdjoinRoot.eval₂_root ((X : (ZMod q)[X]) ^ n - C c)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem root_pow_add_n (i : ℕ) : (root : R q n c) ^ (i + n) = AdjoinRoot.of _ c * root ^ i := by
  rw [pow_add, root_pow_n, mul_comm]

end R

namespace Poly

variable {q n : ℕ} {c : ZMod q}

/-- The element of `ℤ_q[X] / (X^n - c)` with coefficients `f`. -/
def toR (c : ZMod q) (f : Poly q n) : R q n c :=
  ∑ i : Fin n, AdjoinRoot.of _ f[i] * R.root ^ i.val

theorem toR_add (f g : Poly q n) : toR c (f + g) = toR c f + toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_add, map_add, add_mul, Finset.sum_add_distrib]

/-- The product of two monomials, wrapping `X^n` around to `c`. -/
private theorem monomial_mul (a b : ZMod q) (i j : Fin n) :
    (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      ∑ k : Fin n, AdjoinRoot.of _
        (if i.val + j.val = k.val then a * b
         else if i.val + j.val = k.val + n then c * (a * b) else 0) * (R.root : R q n c) ^ k.val := by
  have hprod : (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      AdjoinRoot.of _ (a * b) * (R.root : R q n c) ^ (i.val + j.val) := by
    rw [map_mul, pow_add]; ring
  by_cases hij : i.val + j.val < n
  · rw [Finset.sum_eq_single ⟨i.val + j.val, hij⟩]
    · rw [hprod]
      simp only [↓reduceIte]
    · intro k _ hk
      have h1 : ¬ i.val + j.val = k.val := fun h => hk (Fin.ext h.symm)
      have h2 : ¬ i.val + j.val = k.val + n := by omega
      simp only [h1, h2, ↓reduceIte, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hk : i.val + j.val - n < n := by omega
    rw [Finset.sum_eq_single ⟨i.val + j.val - n, hk⟩]
    · have h1 : ¬ i.val + j.val = i.val + j.val - n := by omega
      have h2 : i.val + j.val = i.val + j.val - n + n := by omega
      have hp : (R.root : R q n c) ^ (i.val + j.val) =
          AdjoinRoot.of _ c * R.root ^ (i.val + j.val - n) := by
        rw [← R.root_pow_add_n]
        congr 1
      rw [hprod, hp]
      simp only [h1, ↓reduceIte, ← h2, map_mul]
      ring
    · intro k _ hk
      have h1 : ¬ i.val + j.val = k.val := by omega
      have h2 : ¬ i.val + j.val = k.val + n :=
        fun h => hk (Fin.ext (show k.val = i.val + j.val - n by omega))
      simp only [h1, h2, ↓reduceIte, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_zero : toR c (0 : Poly q n) = 0 := by
  simp [toR]

theorem toR_const (a : ZMod q) [NeZero n] : toR c (const a : Poly q n) = AdjoinRoot.of _ a := by
  simp only [toR, Fin.getElem_fin, getElem_const]
  rw [Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_one [NeZero n] : toR c (1 : Poly q n) = 1 := by
  rw [show (1 : Poly q n) = const 1 from rfl, toR_const, map_one]

theorem toR_neg (f : Poly q n) : toR c (-f) = -toR c f := by
  simp only [toR, Fin.getElem_fin, getElem_neg, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem toR_sub (f g : Poly q n) : toR c (f - g) = toR c f - toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem toR_smul (a : ZMod q) (f : Poly q n) : toR c (a • f) = AdjoinRoot.of _ a * toR c f := by
  simp only [toR, Fin.getElem_fin, getElem_smul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem toR_mulBinomial (f g : Poly q n) : toR c (mulBinomial c f g) = toR c f * toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_mulBinomial, map_sum, Finset.sum_mul, Finset.mul_sum,
    monomial_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- `toR` as the class of the polynomial with coefficients `f`. -/
theorem toR_eq_mk (f : Poly q n) :
    toR c f = AdjoinRoot.mk _ (∑ i : Fin n, C f[i] * X ^ i.val) := by
  simp only [toR, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

theorem coeff_sum_C_mul_X_pow (f : Poly q n) (i : ℕ) (hi : i < n) :
    (∑ j : Fin n, C f[j] * X ^ j.val).coeff i = f[i] := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj
    have : ¬ i = j.val := fun h => hj (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_injective [Fact q.Prime] : Function.Injective (toR c : Poly q n → R q n c) := by
  intro f g h
  apply Vector.ext
  intro i hi
  have hn : 0 < n := by omega
  rw [toR_eq_mk, toR_eq_mk, AdjoinRoot.mk_eq_mk] at h
  have hdeg : (∑ j : Fin n, C f[j] * X ^ j.val - ∑ j : Fin n, C g[j] * X ^ j.val).degree <
      (n : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt (degree_sum_fin_lt _) (degree_sum_fin_lt _))
  have hzero := Polynomial.eq_zero_of_dvd_of_degree_lt h (by rwa [degree_X_pow_sub_C hn])
  have := congrArg (fun p => p.coeff i) hzero
  simp only [coeff_sub, coeff_sum_C_mul_X_pow _ i hi, coeff_zero] at this
  exact sub_eq_zero.mp this

theorem toR_mul (f g : Poly q n) : toR (-1) (f * g) = toR (-1) f * toR (-1) g :=
  toR_mulBinomial f g

theorem toR_pow [NeZero n] (f : Poly q n) (k : ℕ) : toR (-1) (f ^ k) = toR (-1) f ^ k := by
  induction k with
  | zero => rw [pow_zero', toR_one, pow_zero]
  | succ k ih => rw [pow_succ', toR_mul, ih, pow_succ]

theorem toR_natCast [NeZero n] (k : ℕ) : toR c ((k : ℕ) : Poly q n) = k := by
  rw [show ((k : ℕ) : Poly q n) = const k from rfl, toR_const, map_natCast]

theorem toR_intCast [NeZero n] (k : ℤ) : toR c ((k : ℤ) : Poly q n) = k := by
  rw [show ((k : ℤ) : Poly q n) = const k from rfl, toR_const, map_intCast]

theorem toR_nsmul (k : ℕ) (f : Poly q n) : toR c (k • f) = k • toR c f := by
  rw [show k • f = (k : ZMod q) • f from rfl, toR_smul, map_natCast, nsmul_eq_mul]

theorem toR_zsmul (k : ℤ) (f : Poly q n) : toR c (k • f) = k • toR c f := by
  rw [show k • f = (k : ZMod q) • f from rfl, toR_smul, map_intCast, zsmul_eq_mul]

/-- The ring structure of `ℤ_q[X] / (X^n + 1)` on coefficient vectors, transported along the
injective `toR (-1)` (`q` prime, `n ≥ 1`). -/
instance instCommRing [Fact q.Prime] [NeZero n] : CommRing (Poly q n) :=
  Function.Injective.commRing (toR (-1)) toR_injective toR_zero toR_one toR_add toR_mul toR_neg
    toR_sub toR_nsmul toR_zsmul toR_pow toR_natCast toR_intCast

/-- `toR (-1)` as a ring homomorphism. -/
def toRingHom [Fact q.Prime] [NeZero n] : Poly q n →+* R q n (-1) where
  toFun := toR (-1)
  map_one' := toR_one
  map_mul' := toR_mul
  map_zero' := toR_zero
  map_add' := toR_add

end Poly

end

end Wychelean.Lattice
