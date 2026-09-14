import Wychelean.Lattice.NTTSpec
import Wychelean.Lattice.Quotient

/-!
# Correctness of the transform

The residue map `modBinomial` is the quotient homomorphism `ℤ_q[X]/(X^256+1) → ℤ_q[X]/(X^d - γ)`
whenever `γ^(2^levels) = -1`, i.e. whenever `X^d - γ` divides `X^256 + 1`. Hence residues of a
product are products of residues, which is what multiplying in the NTT domain block by block
computes (FIPS 203 Algorithms 11–12).
-/

namespace Wychelean.Lattice.NTT

open Polynomial Wychelean.Lattice

noncomputable section

variable {q levels : ℕ}

/-- The quotient map onto `ℤ_q[X]/(X^d - γ)`, defined because `X^d - γ` divides `X^256 + 1`. -/
def reduce (hL : levels ≤ 8) (γ : ZMod q) (hγ : γ ^ 2 ^ levels = -1) :
    R q 256 (-1) →+* R q (blockSize levels) γ :=
  AdjoinRoot.lift (AdjoinRoot.of _) R.root (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [← blockSize_mul_pow hL, pow_mul, R.root_pow_n, ← map_pow, hγ, map_neg, map_one,
      sub_neg_eq_add, neg_add_cancel])

theorem reduce_of (hL : levels ≤ 8) (γ : ZMod q) (hγ : γ ^ 2 ^ levels = -1) (a : ZMod q) :
    reduce hL γ hγ (AdjoinRoot.of _ a) = AdjoinRoot.of _ a :=
  AdjoinRoot.lift_of _

theorem reduce_root (hL : levels ≤ 8) (γ : ZMod q) (hγ : γ ^ 2 ^ levels = -1) :
    reduce hL γ hγ R.root = R.root :=
  AdjoinRoot.lift_root _

/-- Coefficient index `r + d·t` of `Fin 256` from the block coordinates. -/
def blockIndex (hL : levels ≤ 8) : Fin (2 ^ levels) × Fin (blockSize levels) ≃ Fin 256 :=
  finProdFinEquiv.trans (finCongr (by rw [Nat.mul_comm]; exact blockSize_mul_pow hL))

theorem blockIndex_apply (hL : levels ≤ 8) (t : Fin (2 ^ levels)) (r : Fin (blockSize levels)) :
    (blockIndex hL (t, r)).val = r.val + blockSize levels * t.val := rfl

/-- The residue of `f` is the image of `f` under the quotient map. -/
theorem toR_modBinomial (hL : levels ≤ 8) (f : Poly q 256) (γ : ZMod q)
    (hγ : γ ^ 2 ^ levels = -1) :
    Poly.toR γ (modBinomial levels hL f γ) = reduce hL γ hγ (Poly.toR (-1) f) := by
  simp only [Poly.toR, map_sum, map_mul, map_pow, reduce_of, reduce_root]
  rw [← Fintype.sum_equiv (blockIndex hL) (fun p => AdjoinRoot.of _ f[(blockIndex hL p).val] *
      (R.root : R q (blockSize levels) γ) ^ (blockIndex hL p).val) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [modBinomial, Fin.getElem_fin, Vector.getElem_ofFn, map_sum, map_mul, map_pow,
    Finset.sum_mul, blockIndex_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  rw [pow_add, pow_mul, R.root_pow_n]
  ring

/-- Residues of a product are products of residues (`q` prime). -/
theorem modBinomial_mul [Fact q.Prime] (hL : levels ≤ 8) (f g : Poly q 256) (γ : ZMod q)
    (hγ : γ ^ 2 ^ levels = -1) :
    modBinomial levels hL (f * g) γ =
      Poly.mulBinomial γ (modBinomial levels hL f γ) (modBinomial levels hL g γ) := by
  apply Poly.toR_injective (c := γ)
  rw [Poly.toR_mulBinomial, toR_modBinomial hL _ _ hγ, toR_modBinomial hL _ _ hγ,
    toR_modBinomial hL _ _ hγ, Poly.mul_eq, Poly.toR_mulBinomial, map_mul]

end

end Wychelean.Lattice.NTT
