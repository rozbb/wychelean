import Wychelean.PolyRing.ModBinomial
import Wychelean.PolyRing.Quotient

/-!
`Poly.modBinomial` is the quotient map `A[X]/(X^n - γ) → A[X]/(X^d - δ)` when `n = r·d` and
`δ^r = γ`: it agrees with Mathlib's map between the `AdjoinRoot`s (`toR_modBinomial`), with
`%ₘ (X^d - C δ)` on representatives (`toPoly_modBinomial`), it turns `mulMod γ` into `mulMod δ`,
and it is characterised by divisibility (`modBinomial_eq_iff_dvd`).
-/

namespace Wychelean.PolyRing

open Polynomial

noncomputable section

namespace R

variable {A : Type*} [CommRing A] {n r d : ℕ} {γ : A}

/-- The quotient map `A[X]/(X^n - γ) →+* A[X]/(X^d - δ)`, defined because `X^d - δ` divides
`X^n - γ` when `n = r·d` and `δ^r = γ`. -/
def reduce (r d : ℕ) (hn : n = r * d) (δ : A) (hδ : δ ^ r = γ) : R A n γ →+* R A d δ :=
  AdjoinRoot.lift (AdjoinRoot.of _) R.root (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [hn, pow_mul', R.root_pow_n, ← map_pow, hδ, sub_self])

variable (hn : n = r * d) (δ : A) (hδ : δ ^ r = γ)

@[simp] theorem reduce_of (a : A) : reduce r d hn δ hδ (AdjoinRoot.of _ a) = AdjoinRoot.of _ a :=
  AdjoinRoot.lift_of _

@[simp] theorem reduce_root : reduce r d hn δ hδ R.root = R.root :=
  AdjoinRoot.lift_root _

theorem reduce_mk (g : A[X]) : reduce r d hn δ hδ (AdjoinRoot.mk _ g) = AdjoinRoot.mk _ g := by
  rw [reduce, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]

/-- Quotient maps compose: the tower `A[X]/(X^n - γ) → A[X]/(X^n₁ - δ₁) → A[X]/(X^d - δ₂)`. -/
theorem reduce_comp {n₁ r₁ r₂ : ℕ} (hn : n = r₁ * n₁) (hn₁ : n₁ = r₂ * d) {δ₁ δ₂ : A}
    (h₁ : δ₁ ^ r₁ = γ) (h₂ : δ₂ ^ r₂ = δ₁) (hn' : n = (r₁ * r₂) * d) :
    (reduce r₂ d hn₁ δ₂ h₂).comp (reduce r₁ n₁ hn δ₁ h₁) =
      reduce (r₁ * r₂) d hn' δ₂ (by rw [pow_mul', h₂, h₁]) :=
  AdjoinRoot.ringHom_ext (RingHom.ext fun a => by simp) (by simp)

end R

namespace Poly

variable {A : Type*} [CommRing A] {n r d : ℕ}

/-- Coefficient index `s + d·t` from the block coordinates. -/
def blockIndex (r d : ℕ) (hn : n = r * d) : Fin r × Fin d ≃ Fin n :=
  finProdFinEquiv.trans (finCongr hn.symm)

theorem blockIndex_apply (hn : n = r * d) (t : Fin r) (s : Fin d) :
    (blockIndex r d hn (t, s)).val = s.val + d * t.val := rfl

variable (p : Poly A n) (δ : A) (hn : n = r * d) {γ : A}

/-- The reduction is the quotient map on `AdjoinRoot`. -/
theorem toR_modBinomial (hδ : δ ^ r = γ) :
    toR δ (p.modBinomial r d δ hn) = R.reduce r d hn δ hδ (toR γ p) := by
  simp only [Poly.toR, map_sum, map_mul, map_pow, R.reduce_of, R.reduce_root]
  rw [← Fintype.sum_equiv (blockIndex r d hn) (fun x => AdjoinRoot.of _ p[(blockIndex r d hn x).val] *
      (R.root : R A d δ) ^ (blockIndex r d hn x).val) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.getElem_fin, getElem_modBinomial, map_sum, map_mul, map_pow, Finset.sum_mul,
    blockIndex_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [pow_add, pow_mul, R.root_pow_n]
  ring

theorem modBinomial_mulMod [IsDomain A] (hδ : δ ^ r = γ) (q : Poly A n) :
    (mulMod γ p q).modBinomial r d δ hn =
      mulMod δ (p.modBinomial r d δ hn) (q.modBinomial r d δ hn) := by
  apply toR_injective δ
  rw [toR_mulMod, toR_modBinomial _ _ _ hδ, toR_modBinomial _ _ _ hδ, toR_modBinomial _ _ _ hδ,
    toR_mulMod, map_mul]

theorem modBinomial_one [IsDomain A] [NeZero r] [NeZero d] (hδ : δ ^ r = γ) :
    (1 : Poly A n).modBinomial r d δ hn = 1 := by
  have : NeZero n := ⟨hn ▸ Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne d)⟩
  apply toR_injective δ
  rw [toR_modBinomial _ _ _ hδ, toR_one, toR_one, map_one]

/-- On representatives, the reduction is `%ₘ (X^d - C δ)`. -/
theorem toPoly_modBinomial [Nontrivial A] [NeZero d] (hδ : δ ^ r = γ) :
    (p.modBinomial r d δ hn).toPoly = p.toPoly %ₘ (X ^ d - C δ) := by
  have hmonic : (X ^ d - C δ : A[X]).Monic := monic_X_pow_sub_C δ (NeZero.ne d)
  have h := toR_modBinomial p δ hn hδ
  rw [toR_eq_mk, toR_eq_mk, R.reduce_mk, AdjoinRoot.mk_eq_mk] at h
  rw [← modByMonic_eq_of_dvd_sub hmonic h]
  symm
  rw [modByMonic_eq_self_iff hmonic, degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne d))]
  exact degree_toPoly_lt _

/-- The reduction is the residue whose representative differs from `p` by a multiple of
`X^d - δ`. -/
theorem modBinomial_eq_iff_dvd [Nontrivial A] [NeZero d] (hδ : δ ^ r = γ) (b : Poly A d) :
    p.modBinomial r d δ hn = b ↔ (X ^ d - C δ : A[X]) ∣ p.toPoly - b.toPoly := by
  have hmonic : (X ^ d - C δ : A[X]).Monic := monic_X_pow_sub_C δ (NeZero.ne d)
  have hb : b.toPoly %ₘ (X ^ d - C δ) = b.toPoly := by
    rw [modByMonic_eq_self_iff hmonic, degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne d))]
    exact degree_toPoly_lt _
  constructor
  · rintro rfl
    rw [toPoly_modBinomial _ _ _ hδ]
    have := dvd_modByMonic_sub p.toPoly (X ^ d - C δ)
    rwa [← dvd_neg, neg_sub] at this
  · intro h
    apply toPoly_injective
    rw [toPoly_modBinomial _ _ _ hδ, modByMonic_eq_of_dvd_sub hmonic h, hb]

theorem modBinomial_eq_iff_toR [IsDomain A] (hδ : δ ^ r = γ) (b : Poly A d) :
    p.modBinomial r d δ hn = b ↔ toR δ b = R.reduce r d hn δ hδ (toR γ p) := by
  rw [← toR_modBinomial _ _ _ hδ, (toR_injective δ).eq_iff, eq_comm]

/-- In degree one the reduction is evaluation at `δ`. -/
theorem getElem_modBinomial_eval (h1 : n = r * 1) :
    (p.modBinomial r 1 δ h1)[0] = p.toPoly.eval δ := by
  rw [getElem_modBinomial, toPoly, eval_finsetSum]
  refine (Fintype.sum_equiv (finCongr (by rw [h1, Nat.mul_one])) _ _ fun t => ?_).symm
  simp

theorem getElem_modBinomial_eval' (hd : d = 1) :
    (p.modBinomial r d δ hn)[0]'(by omega) = p.toPoly.eval δ := by
  subst hd
  exact getElem_modBinomial_eval (d := 1) p δ hn

end Poly

end

end Wychelean.PolyRing
