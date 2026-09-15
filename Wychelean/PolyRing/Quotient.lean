import Wychelean.PolyRing.Poly
import Mathlib.RingTheory.AdjoinRoot

/-!
`Poly A n c` is a computable representation of Mathlib's `AdjoinRoot (X^n - C c)`: `toR` is
injective (`A` a domain) and respects the operations, which transports the ring laws.
-/

namespace Wychelean.PolyRing

open Polynomial

noncomputable section

/-- Mathlib's `A[X] / (X^n - c)`. -/
abbrev R (A : Type) [CommRing A] (n : ℕ) (c : A) := AdjoinRoot ((X : A[X]) ^ n - C c)

namespace R

variable {A : Type} [CommRing A] {n : ℕ} {c : A}

abbrev root : R A n c := AdjoinRoot.root _

theorem root_pow_n : (root : R A n c) ^ n = AdjoinRoot.of _ c := by
  have h := AdjoinRoot.eval₂_root ((X : A[X]) ^ n - C c)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem root_pow_add_n (i : ℕ) : (root : R A n c) ^ (i + n) = AdjoinRoot.of _ c * root ^ i := by
  rw [pow_add, root_pow_n, mul_comm]

end R

namespace Poly

variable {A : Type} [CommRing A] {n : ℕ} {c : A}

/-- The element of `A[X] / (X^n - c)` with coefficients `f`. -/
def toR (f : Poly A n c) : R A n c :=
  ∑ i : Fin n, AdjoinRoot.of _ f[i] * R.root ^ i.val

theorem toR_add (f g : Poly A n c) : toR (f + g) = toR f + toR g := by
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

theorem toR_zero : toR (0 : Poly A n c) = 0 := by
  simp [toR]

theorem toR_const (a : A) [NeZero n] : toR (const a : Poly A n c) = AdjoinRoot.of _ a := by
  simp only [toR, Fin.getElem_fin, getElem_const]
  rw [Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_one [NeZero n] : toR (1 : Poly A n c) = 1 := by
  rw [show (1 : Poly A n c) = const 1 from rfl, toR_const, map_one]

theorem toR_neg (f : Poly A n c) : toR (-f) = -toR f := by
  simp only [toR, Fin.getElem_fin, getElem_neg, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem toR_sub (f g : Poly A n c) : toR (f - g) = toR f - toR g := by
  simp only [toR, Fin.getElem_fin, getElem_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem toR_smul (a : A) (f : Poly A n c) : toR (a • f) = AdjoinRoot.of _ a * toR f := by
  simp only [toR, Fin.getElem_fin, getElem_smul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem toR_mul (f g : Poly A n c) : toR (f * g) = toR f * toR g := by
  simp only [toR, Fin.getElem_fin, getElem_mul, map_sum, Finset.sum_mul, Finset.mul_sum,
    monomial_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem toR_eq_mk (f : Poly A n c) :
    toR f = AdjoinRoot.mk _ (∑ i : Fin n, C f[i] * X ^ i.val) := by
  simp only [toR, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

theorem coeff_sum_C_mul_X_pow (f : Poly A n c) (i : ℕ) (hi : i < n) :
    (∑ j : Fin n, C f[j] * X ^ j.val).coeff i = f[i] := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj
    have : ¬ i = j.val := fun h => hj (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_injective [IsDomain A] : Function.Injective (toR : Poly A n c → R A n c) := by
  intro f g h
  ext i hi
  have hn : 0 < n := by omega
  rw [toR_eq_mk, toR_eq_mk, AdjoinRoot.mk_eq_mk] at h
  have hdeg : (∑ j : Fin n, C f[j] * X ^ j.val - ∑ j : Fin n, C g[j] * X ^ j.val).degree <
      (n : WithBot ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt (degree_sum_fin_lt _) (degree_sum_fin_lt _))
  have hzero := Polynomial.eq_zero_of_dvd_of_degree_lt h (by rwa [degree_X_pow_sub_C hn])
  have := congrArg (fun p => p.coeff i) hzero
  simp only [coeff_sub, coeff_sum_C_mul_X_pow _ i hi, coeff_zero] at this
  exact sub_eq_zero.mp this

end Poly

end

namespace Poly

variable {A : Type} [CommRing A] {n : ℕ} {c : A}

/-- A ring law on `Poly A n c`, through the quotient ring. -/
local macro "poly_law" : tactic =>
  `(tactic| (apply toR_injective; simp only [toR_add, toR_mul, toR_neg, toR_sub, toR_zero, toR_one]; ring))

/-- The ring `A[X] / (X^n - c)` on coefficient vectors (`A` a domain, `n ≥ 1`); the operations
are the computable ones of `Poly`. -/
instance instCommRing [IsDomain A] [NeZero n] : CommRing (Poly A n c) where
  add_assoc _ _ _ := by poly_law
  zero_add _ := by poly_law
  add_zero _ := by poly_law
  add_comm _ _ := by poly_law
  neg_add_cancel _ := by poly_law
  sub_eq_add_neg _ _ := by poly_law
  left_distrib _ _ _ := by poly_law
  right_distrib _ _ _ := by poly_law
  zero_mul _ := by poly_law
  mul_zero _ := by poly_law
  mul_assoc _ _ _ := by poly_law
  one_mul _ := by poly_law
  mul_one _ := by poly_law
  mul_comm _ _ := by poly_law
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable def toRingHom [IsDomain A] [NeZero n] : Poly A n c →+* R A n c where
  toFun := toR
  map_one' := toR_one
  map_mul' := toR_mul
  map_zero' := toR_zero
  map_add' := toR_add

/-! ### Reduction modulo `q`: `ℤ[X]/(X^n - c) → ℤ_q[X]/(X^n - c)` -/

variable {n : ℕ} {c : ℤ} (q : ℕ)

def reduce (f : Poly ℤ n c) : Poly (ZMod q) n (c : ZMod q) := ⟨f.coeffs.map Int.cast⟩

@[simp] theorem getElem_reduce (f : Poly ℤ n c) (i : ℕ) (hi : i < n) :
    (reduce q f)[i] = (f[i] : ZMod q) :=
  Vector.getElem_map ..

theorem reduce_add (f g : Poly ℤ n c) : reduce q (f + g) = reduce q f + reduce q g := by
  ext i hi; simp

theorem reduce_mul (f g : Poly ℤ n c) : reduce q (f * g) = reduce q f * reduce q g := by
  ext i hi
  simp only [getElem_reduce, getElem_mul, Fin.getElem_fin]
  push_cast
  rfl

theorem reduce_surjective [NeZero q] : Function.Surjective (reduce q : Poly ℤ n c → Poly (ZMod q) n c) :=
  fun g => ⟨⟨g.coeffs.map fun x => x.val⟩, by
    ext i hi
    simp only [getElem_reduce, getElem_mk, Vector.getElem_map, Int.cast_natCast]
    exact ZMod.natCast_zmod_val _⟩

/-- The kernel of `reduce q` is the multiples of `q`. -/
theorem reduce_eq_zero_iff (f : Poly ℤ n c) : reduce q f = 0 ↔ ∀ (i : ℕ) (hi : i < n), (q : ℤ) ∣ f[i] := by
  constructor
  · intro h i hi
    have := congrArg (fun p : Poly (ZMod q) n c => p[i]) h
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  · intro h
    ext i hi
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h i hi

end Poly

end Wychelean.PolyRing
