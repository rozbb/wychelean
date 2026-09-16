import Wychelean.PolyRing.Poly
import Mathlib.RingTheory.AdjoinRoot

/-!
`Poly A n` with the product `mulMod c` is a computable representation of Mathlib's
`AdjoinRoot (X^n - C c)`: `toR c` is injective (`A` a domain) and respects the operations,
which is how `Residues` gets its ring laws.
-/

namespace Wychelean.PolyRing

open Polynomial

noncomputable section

/-- Mathlib's `A[X] / (X^n - c)`. -/
abbrev R (A : Type*) [CommRing A] (n : ℕ) (c : A) := AdjoinRoot ((X : A[X]) ^ n - C c)

namespace R

variable {A : Type*} [CommRing A] {n : ℕ} {c : A}

abbrev root : R A n c := AdjoinRoot.root _

theorem root_pow_n : (root : R A n c) ^ n = AdjoinRoot.of _ c := by
  have h := AdjoinRoot.eval₂_root ((X : A[X]) ^ n - C c)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem root_pow_add_n (i : ℕ) : (root : R A n c) ^ (i + n) = AdjoinRoot.of _ c * root ^ i := by
  rw [pow_add, root_pow_n, mul_comm]

end R

namespace Poly

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The representative of degree below `n` in `A[X]`. -/
def toPoly (f : Poly A n) : A[X] := ∑ i : Fin n, C f[i] * X ^ i.val

@[simp] theorem coeff_toPoly (f : Poly A n) (i : ℕ) (hi : i < n) : f.toPoly.coeff i = f[i] := by
  rw [toPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj
    have : ¬ i = j.val := fun h => hj (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem degree_toPoly_lt (f : Poly A n) : f.toPoly.degree < n := degree_sum_fin_lt _

theorem toPoly_injective : Function.Injective (toPoly : Poly A n → A[X]) := by
  intro f g h
  ext i hi
  rw [← coeff_toPoly f i hi, ← coeff_toPoly g i hi, h]

/-- The element of `A[X] / (X^n - c)` with coefficients `f`. -/
def toR (c : A) (f : Poly A n) : R A n c :=
  ∑ i : Fin n, AdjoinRoot.of _ f[i] * R.root ^ i.val

variable (c : A)

theorem toR_eq_mk (f : Poly A n) : toR c f = AdjoinRoot.mk _ f.toPoly := by
  simp only [toR, toPoly, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

theorem toR_add (f g : Poly A n) : toR c (f + g) = toR c f + toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_add, map_add, add_mul, Finset.sum_add_distrib]

private theorem monomial_mul (a b : A) (i j : Fin n) :
    (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      ∑ k : Fin n, AdjoinRoot.of _
        (if i.val + j.val = k.val then a * b
         else if i.val + j.val = k.val + n then c * (a * b) else 0) * (R.root : R A n c) ^ k.val := by
  have hprod : (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      AdjoinRoot.of _ (a * b) * (R.root : R A n c) ^ (i.val + j.val) := by
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
      have hp : (R.root : R A n c) ^ (i.val + j.val) =
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

theorem toR_zero : toR c (0 : Poly A n) = 0 := by
  simp [toR]

theorem toR_const (a : A) [NeZero n] : toR c (const a : Poly A n) = AdjoinRoot.of _ a := by
  simp only [toR, Fin.getElem_fin, getElem_const]
  rw [Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_one [NeZero n] : toR c (1 : Poly A n) = 1 := by
  rw [show (1 : Poly A n) = const 1 from rfl, toR_const, map_one]

theorem toR_neg (f : Poly A n) : toR c (-f) = -toR c f := by
  simp only [toR, Fin.getElem_fin, getElem_neg, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem toR_sub (f g : Poly A n) : toR c (f - g) = toR c f - toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem toR_smul (a : A) (f : Poly A n) : toR c (a • f) = AdjoinRoot.of _ a * toR c f := by
  simp only [toR, Fin.getElem_fin, getElem_smul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem toR_mulMod (f g : Poly A n) : toR c (mulMod c f g) = toR c f * toR c g := by
  simp only [toR, Fin.getElem_fin, getElem_mulMod, map_sum, Finset.sum_mul, Finset.mul_sum,
    monomial_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem toR_injective [IsDomain A] : Function.Injective (toR c : Poly A n → R A n c) := by
  intro f g h
  ext i hi
  have hn : 0 < n := by omega
  rw [toR_eq_mk, toR_eq_mk, AdjoinRoot.mk_eq_mk] at h
  have hdeg : (f.toPoly - g.toPoly).degree < (n : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt (degree_toPoly_lt _) (degree_toPoly_lt _))
  have hzero := Polynomial.eq_zero_of_dvd_of_degree_lt h (by rwa [degree_X_pow_sub_C hn])
  have := congrArg (fun p => p.coeff i) hzero
  simp only [coeff_sub, coeff_toPoly _ i hi, coeff_zero] at this
  exact sub_eq_zero.mp this

end Poly

end

end Wychelean.PolyRing
