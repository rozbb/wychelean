import Wychelean.PolyRing.Poly
import Mathlib.RingTheory.AdjoinRoot

/-!
`Poly A d` is a computable representation of Mathlib's `AdjoinRoot (X^d + μ)` for any monic
modulus `X^d + μ` given by its lower coefficients `μ`: `toR μ` sends the coefficient vector to
the class of its representative, is injective (`A` nontrivial), surjective, and turns the
wrap-around product `mulMod c` into the product of `A[X]/(X^d - c)`. The quotient maps between
these rings for a divisibility of moduli are `R.reduce`.
-/

namespace Wychelean.PolyRing

open Polynomial

noncomputable section

namespace Poly

variable {A : Type*} [CommRing A] {n d : ℕ}

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

theorem coeff_toPoly_of_le (f : Poly A n) (i : ℕ) (hi : n ≤ i) : f.toPoly.coeff i = 0 := by
  rw [toPoly, finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h
  · omega
  · rfl

theorem degree_toPoly_lt (f : Poly A n) : f.toPoly.degree < n := degree_sum_fin_lt _

theorem toPoly_injective : Function.Injective (toPoly : Poly A n → A[X]) := by
  intro f g h
  ext i hi
  rw [← coeff_toPoly f i hi, ← coeff_toPoly g i hi, h]

theorem toPoly_zero_deg (f : Poly A 0) : f.toPoly = 0 := by
  simp [toPoly]

/-- The monic modulus `X^d + μ` with lower coefficients `μ`. -/
def monicPoly (μ : Poly A d) : A[X] := X ^ d + μ.toPoly

theorem monicPoly_monic (μ : Poly A d) : (monicPoly μ).Monic :=
  monic_X_pow_add (degree_toPoly_lt μ)

theorem degree_monicPoly [Nontrivial A] (μ : Poly A d) : (monicPoly μ).degree = d := by
  rw [monicPoly, degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_toPoly_lt μ

theorem monicPoly_zero_deg (μ : Poly A 0) : monicPoly μ = 1 := by
  rw [monicPoly, toPoly_zero_deg, pow_zero, add_zero]

theorem toPoly_binomial [NeZero d] (c : A) : (binomial c : Poly A d).toPoly = -C c := by
  rw [toPoly, Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem monicPoly_binomial [NeZero d] (c : A) : monicPoly (binomial c : Poly A d) = X ^ d - C c := by
  rw [monicPoly, toPoly_binomial, sub_eq_add_neg]

/-- `X^d - δ` divides `X^n - δ^r` when `n = r·d`. -/
theorem monicPoly_binomial_dvd {r : ℕ} [NeZero r] {δ γ : A} (hn : n = r * d) (hδ : δ ^ r = γ) :
    monicPoly (binomial δ : Poly A d) ∣ monicPoly (binomial γ : Poly A n) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · subst hn
    rw [Nat.mul_zero, monicPoly_zero_deg, monicPoly_zero_deg]
  · have : NeZero d := ⟨hd.ne'⟩
    have : NeZero n := ⟨hn ▸ Nat.mul_ne_zero (NeZero.ne r) hd.ne'⟩
    rw [monicPoly_binomial, monicPoly_binomial, hn, pow_mul', ← hδ, map_pow]
    exact sub_dvd_pow_sub_pow (X ^ d) (C δ) r

end Poly

/-- Mathlib's `A[X] / (X^d + μ)`. -/
abbrev R (A : Type*) [CommRing A] (d : ℕ) (μ : Poly A d) := AdjoinRoot (Poly.monicPoly μ)

namespace Poly

variable {A : Type*} [CommRing A] {n d : ℕ}

/-- The class of the polynomial with coefficients `f` in `A[X]/(X^d + μ)`. -/
def toR (μ : Poly A d) (f : Poly A d) : R A d μ :=
  ∑ i : Fin d, AdjoinRoot.of _ f[i] * AdjoinRoot.root _ ^ i.val

theorem toR_eq_mk (μ : Poly A d) (f : Poly A d) : toR μ f = AdjoinRoot.mk _ f.toPoly := by
  simp only [toR, toPoly, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

end Poly

namespace R

variable {A : Type*} [CommRing A] {d : ℕ} {μ : Poly A d}

abbrev root : R A d μ := AdjoinRoot.root _

/-- `root^d = -μ(root)`. -/
theorem root_pow_d : (root : R A d μ) ^ d = -Poly.toR μ μ := by
  have h := AdjoinRoot.eval₂_root (Poly.monicPoly μ)
  rw [Poly.monicPoly, eval₂_add, eval₂_pow, eval₂_X] at h
  rw [Poly.toR_eq_mk, ← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]
  exact eq_neg_of_add_eq_zero_left h

instance subsingleton_zero_deg (μ : Poly A 0) : Subsingleton (R A 0 μ) :=
  subsingleton_of_zero_eq_one (by
    rw [← AdjoinRoot.mk_self (f := Poly.monicPoly μ), ← map_one (AdjoinRoot.mk (Poly.monicPoly μ)),
      AdjoinRoot.mk_eq_mk, Poly.monicPoly_zero_deg]
    simp)

theorem toR_binomial [NeZero d] (c : A) : Poly.toR μ (Poly.binomial c) = -AdjoinRoot.of _ c := by
  rw [Poly.toR, Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem root_pow_binomial [NeZero d] (c : A) :
    (root : R A d (Poly.binomial c)) ^ d = AdjoinRoot.of _ c := by
  rw [root_pow_d, toR_binomial, neg_neg]

theorem root_pow_add_binomial [NeZero d] (c : A) (i : ℕ) :
    (root : R A d (Poly.binomial c)) ^ (i + d) = AdjoinRoot.of _ c * root ^ i := by
  rw [pow_add, root_pow_binomial, mul_comm]

/-- The quotient map `A[X]/(X^d' + μ) → A[X]/(X^d + μ')` when `X^d + μ'` divides `X^d' + μ`. -/
def reduce {d' : ℕ} {μ : Poly A d'} {μ' : Poly A d} (h : Poly.monicPoly μ' ∣ Poly.monicPoly μ) :
    R A d' μ →+* R A d μ' :=
  AdjoinRoot.lift (AdjoinRoot.of _) root (by
    rw [← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 h)

variable {d' : ℕ} {μ : Poly A d'} {μ' : Poly A d} (h : Poly.monicPoly μ' ∣ Poly.monicPoly μ)

@[simp] theorem reduce_of (a : A) : reduce h (AdjoinRoot.of _ a) = AdjoinRoot.of _ a :=
  AdjoinRoot.lift_of _

@[simp] theorem reduce_root : reduce h root = root :=
  AdjoinRoot.lift_root _

theorem reduce_mk (g : A[X]) : reduce h (AdjoinRoot.mk _ g) = AdjoinRoot.mk _ g := by
  rw [reduce, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]

/-- Quotient maps compose along a tower of divisibilities. -/
theorem reduce_comp {d'' : ℕ} {μ'' : Poly A d''} (h' : Poly.monicPoly μ'' ∣ Poly.monicPoly μ') :
    (reduce h').comp (reduce h) = reduce (h'.trans h) :=
  AdjoinRoot.ringHom_ext (RingHom.ext fun a => by simp) (by simp)

/-- The quotient map `A[X]/(X^n - γ) → A[X]/(X^d - δ)` for `n = r·d` and `δ^r = γ`. -/
abbrev reduceBinomial {n : ℕ} (r d : ℕ) [NeZero r] (hn : n = r * d) (δ : A) {γ : A} (hδ : δ ^ r = γ) :
    R A n (Poly.binomial γ) →+* R A d (Poly.binomial δ) :=
  reduce (Poly.monicPoly_binomial_dvd hn hδ)

end R

namespace Poly

variable {A : Type*} [CommRing A] {n d : ℕ} (μ : Poly A d)

theorem toR_add (f g : Poly A d) : toR μ (f + g) = toR μ f + toR μ g := by
  simp only [toR, Fin.getElem_fin, getElem_add, map_add, add_mul, Finset.sum_add_distrib]

theorem toR_zero : toR μ (0 : Poly A d) = 0 := by
  simp [toR]

theorem toR_const (a : A) [NeZero d] : toR μ (const a : Poly A d) = AdjoinRoot.of _ a := by
  simp only [toR, Fin.getElem_fin, getElem_const]
  rw [Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toR_one [NeZero d] : toR μ (1 : Poly A d) = 1 := by
  rw [show (1 : Poly A d) = const 1 from rfl, toR_const, map_one]

theorem toR_neg (f : Poly A d) : toR μ (-f) = -toR μ f := by
  simp only [toR, Fin.getElem_fin, getElem_neg, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem toR_sub (f g : Poly A d) : toR μ (f - g) = toR μ f - toR μ g := by
  simp only [toR, Fin.getElem_fin, getElem_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem toR_smul (a : A) (f : Poly A d) : toR μ (a • f) = AdjoinRoot.of _ a * toR μ f := by
  simp only [toR, Fin.getElem_fin, getElem_smul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem monomial_mul (c a b : A) (i j : Fin n) :
    (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      ∑ k : Fin n, AdjoinRoot.of _
        (if i.val + j.val = k.val then a * b
         else if i.val + j.val = k.val + n then c * (a * b) else 0) *
          (R.root : R A n (binomial c)) ^ k.val := by
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.1 i.pos⟩
  have hprod : (AdjoinRoot.of _ a * R.root ^ i.val) * (AdjoinRoot.of _ b * R.root ^ j.val) =
      AdjoinRoot.of _ (a * b) * (R.root : R A n (binomial c)) ^ (i.val + j.val) := by
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
      have hp : (R.root : R A n (binomial c)) ^ (i.val + j.val) =
          AdjoinRoot.of _ c * R.root ^ (i.val + j.val - n) := by
        rw [← R.root_pow_add_binomial]
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

/-- The wrap-around product is the product of `A[X]/(X^n - c)`. -/
theorem toR_mulMod (c : A) (f g : Poly A n) :
    toR (binomial c) (mulMod c f g) = toR (binomial c) f * toR (binomial c) g := by
  simp only [toR, Fin.getElem_fin, getElem_mulMod, map_sum, Finset.sum_mul, Finset.mul_sum,
    monomial_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem toR_injective [Nontrivial A] : Function.Injective (toR μ : Poly A d → R A d μ) := by
  intro f g h
  rw [toR_eq_mk, toR_eq_mk, AdjoinRoot.mk_eq_mk] at h
  have hmonic := monicPoly_monic μ
  have hmod := (modByMonic_eq_zero_iff_dvd hmonic).2 h
  rw [(modByMonic_eq_self_iff hmonic).2 (by
    rw [degree_monicPoly]
    exact (degree_sub_le _ _).trans_lt (max_lt (degree_toPoly_lt _) (degree_toPoly_lt _)))] at hmod
  exact toPoly_injective (sub_eq_zero.1 hmod)

/-- Equality through the quotient ring, for any coefficient ring. -/
theorem ext_toR {f g : Poly A d} (h : ∀ [Nontrivial A], toR μ f = toR μ g) : f = g := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact Subsingleton.elim _ _
  · exact toR_injective μ h

/-- Every class has a representative of degree below `d`. -/
theorem toR_surjective [Nontrivial A] : Function.Surjective (toR μ : Poly A d → R A d μ) := by
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hmonic := monicPoly_monic μ
    refine ⟨⟨Vector.ofFn fun i => (g %ₘ monicPoly μ).coeff i⟩, ?_⟩
    rw [toR_eq_mk, AdjoinRoot.mk_eq_mk]
    have : (⟨Vector.ofFn fun i => (g %ₘ monicPoly μ).coeff i⟩ : Poly A d).toPoly =
        g %ₘ monicPoly μ := by
      rw [toPoly]
      simp only [Fin.getElem_fin, getElem_mk, Vector.getElem_ofFn, C_mul_X_pow_eq_monomial]
      exact sum_modByMonic_coeff hmonic (by rw [degree_monicPoly])
    rw [this]
    exact dvd_modByMonic_sub g _

end Poly

end

end Wychelean.PolyRing
