import Wychelean.Lattice.Poly
import Mathlib.RingTheory.AdjoinRoot

/-!
# Coefficient vectors and the quotient ring

`Poly q n` is a computable representation of Mathlib's `AdjoinRoot (X^n + 1)` over `ZMod q`.
`Poly.toRq` sends a coefficient vector to the corresponding ring element, and the theorems here
show it respects addition and the negacyclic product, so the ring laws of `Poly.mul` are those of
`ℤ_q[X] / (X^n + 1)`.
-/

namespace Wychelean.Lattice

open Polynomial

noncomputable section

/-- Mathlib's `ℤ_q[X] / (X^n + 1)`. -/
abbrev Rq (q n : ℕ) := AdjoinRoot ((X : (ZMod q)[X]) ^ n + 1)

namespace Rq

variable {q n : ℕ}

/-- The image of `X`. -/
abbrev root : Rq q n := AdjoinRoot.root _

theorem root_pow_n : (root : Rq q n) ^ n = -1 := by
  have h := AdjoinRoot.eval₂_root ((X : (ZMod q)[X]) ^ n + 1)
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem root_pow_add_n (i : ℕ) : (root : Rq q n) ^ (i + n) = -(root ^ i) := by
  rw [pow_add, root_pow_n, mul_neg, mul_one]

end Rq

namespace Poly

variable {q n : ℕ}

/-- The element of `ℤ_q[X] / (X^n + 1)` with coefficients `f`. -/
def toRq (f : Poly q n) : Rq q n :=
  ∑ i : Fin n, AdjoinRoot.of _ f[i] * Rq.root ^ i.val

theorem toRq_add (f g : Poly q n) : toRq (f + g) = toRq f + toRq g := by
  simp only [toRq, Fin.getElem_fin, getElem_add, map_add, add_mul, Finset.sum_add_distrib]

/-- The product of two monomials, with the wrap-around sign of `X^n = -1`. -/
private theorem monomial_mul (a b : ZMod q) (i j : Fin n) :
    (AdjoinRoot.of _ a * Rq.root ^ i.val) * (AdjoinRoot.of _ b * Rq.root ^ j.val) =
      ∑ k : Fin n, AdjoinRoot.of _
        (if i.val + j.val = k.val then a * b
         else if i.val + j.val = k.val + n then -(a * b) else 0) * (Rq.root : Rq q n) ^ k.val := by
  have hprod : (AdjoinRoot.of _ a * Rq.root ^ i.val) * (AdjoinRoot.of _ b * Rq.root ^ j.val) =
      AdjoinRoot.of _ (a * b) * (Rq.root : Rq q n) ^ (i.val + j.val) := by
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
      have hp : (Rq.root : Rq q n) ^ (i.val + j.val) = -(Rq.root ^ (i.val + j.val - n)) := by
        rw [← Rq.root_pow_add_n]
        congr 1
      rw [hprod, hp]
      simp only [h1, ↓reduceIte, ← h2, map_neg]
      ring
    · intro k _ hk
      have h1 : ¬ i.val + j.val = k.val := by omega
      have h2 : ¬ i.val + j.val = k.val + n :=
        fun h => hk (Fin.ext (show k.val = i.val + j.val - n by omega))
      simp only [h1, h2, ↓reduceIte, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem toRq_mul (f g : Poly q n) : toRq (f * g) = toRq f * toRq g := by
  simp only [toRq, Fin.getElem_fin, getElem_mul, map_sum, Finset.sum_mul, Finset.mul_sum,
    monomial_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Poly

end

end Wychelean.Lattice
