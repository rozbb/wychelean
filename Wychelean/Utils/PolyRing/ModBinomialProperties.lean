import Wychelean.Utils.PolyRing.ModBinomial
import Wychelean.Utils.PolyRing.Quotient

namespace Wychelean.Utils.PolyRing

open Polynomial

noncomputable section


namespace Poly

variable {A : Type*} [CommRing A] {n r d : ℕ}

/-- Coefficient index `s + d·t` from the block coordinates. -/
def blockIndex (r d : ℕ) (hn : n = r * d) : Fin r × Fin d ≃ Fin n :=
  finProdFinEquiv.trans (finCongr hn.symm)

theorem blockIndex_apply (hn : n = r * d) (t : Fin r) (s : Fin d) :
    (blockIndex r d hn (t, s)).val = s.val + d * t.val := rfl

variable (p : Poly A n) (δ : A) (hn : n = r * d) {γ : A}

/-- The reduction is the quotient map on `AdjoinRoot`. -/
theorem toR_modBinomial [NeZero r] (hδ : δ ^ r = γ) :
    toR (binomial δ) (p.modBinomial r d δ hn) = R.reduceBinomial r d hn δ hδ (toR (binomial γ) p) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  have : NeZero d := ⟨hd.ne'⟩
  simp only [Poly.toR, map_sum, map_mul, map_pow, R.reduce_of, R.reduce_root]
  rw [← Fintype.sum_equiv (blockIndex r d hn) (fun x => AdjoinRoot.of _ p[(blockIndex r d hn x).val] *
      (R.root : R A d (binomial δ)) ^ (blockIndex r d hn x).val) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.getElem_fin, getElem_modBinomial, map_sum, map_mul, map_pow, Finset.sum_mul,
    blockIndex_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [pow_add, pow_mul, R.root_pow_binomial]
  ring

theorem modBinomial_mulMod [Nontrivial A] [NeZero r] (hδ : δ ^ r = γ) (q : Poly A n) :
    (mulMod γ p q).modBinomial r d δ hn =
      mulMod δ (p.modBinomial r d δ hn) (q.modBinomial r d δ hn) := by
  apply toR_injective (binomial δ)
  rw [toR_mulMod, toR_modBinomial _ _ _ hδ, toR_modBinomial _ _ _ hδ, toR_modBinomial _ _ _ hδ,
    toR_mulMod, map_mul]

theorem modBinomial_one [Nontrivial A] [NeZero r] [NeZero d] (hδ : δ ^ r = γ) :
    (1 : Poly A n).modBinomial r d δ hn = 1 := by
  have : NeZero n := ⟨hn ▸ Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne d)⟩
  apply toR_injective (binomial δ)
  rw [toR_modBinomial _ _ _ hδ, toR_one, toR_one, map_one]

/-- On representatives, the reduction is `%ₘ (X^d - C δ)`. -/
theorem toPoly_modBinomial [Nontrivial A] [NeZero r] [NeZero d] (hδ : δ ^ r = γ) :
    (p.modBinomial r d δ hn).toPoly = p.toPoly %ₘ (X ^ d - C δ) := by
  have hmonic : (X ^ d - C δ : A[X]).Monic := monic_X_pow_sub_C δ (NeZero.ne d)
  have h := toR_modBinomial p δ hn hδ
  rw [toR_eq_mk, toR_eq_mk, R.reduce_mk, AdjoinRoot.mk_eq_mk, monicPoly_binomial] at h
  rw [← modByMonic_eq_of_dvd_sub hmonic h]
  symm
  rw [modByMonic_eq_self_iff hmonic, degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne d))]
  exact degree_toPoly_lt _

/-- The reduction is the residue whose representative differs from `p` by a multiple of
`X^d - δ`. -/
theorem modBinomial_eq_iff_dvd [Nontrivial A] [NeZero r] [NeZero d] (hδ : δ ^ r = γ) (b : Poly A d) :
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

theorem modBinomial_eq_iff_toR [Nontrivial A] [NeZero r] (hδ : δ ^ r = γ) (b : Poly A d) :
    p.modBinomial r d δ hn = b ↔
      toR (binomial δ) b = R.reduceBinomial r d hn δ hδ (toR (binomial γ) p) := by
  rw [← toR_modBinomial _ _ _ hδ, (toR_injective _).eq_iff, eq_comm]

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

end Wychelean.Utils.PolyRing
