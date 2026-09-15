import Wychelean.PolyRing.NTTSpec
import Wychelean.PolyRing.Quotient
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.OrderOfElement

/-!
`modBinomial` is the quotient map `ℤ_q[X]/(X^256+1) → ℤ_q[X]/(X^d - γ)` when `γ^(2^levels) = -1`,
so the transform is multiplicative; it is invertible because the points are the odd powers of a
primitive `2^(levels+1)`-th root of unity (`q` an odd prime); and the recursive transform agrees
with the closed form.
-/

namespace Wychelean.PolyRing.NTT

open Polynomial Wychelean.PolyRing

noncomputable section

variable {q levels : ℕ}

/-- The quotient map onto `ℤ_q[X]/(X^d - γ)`, defined because `X^d - γ` divides `X^256 + 1`. -/
def reduce (hL : levels ≤ 8) (γ : ZMod q) (hγ : γ ^ 2 ^ levels = -1) :
    R (ZMod q) 256 (-1) →+* R (ZMod q) (blockSize levels) γ :=
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

/-- Coefficient index `r + d·t` from the block coordinates. -/
def blockIndex (hL : levels ≤ 8) : Fin (2 ^ levels) × Fin (blockSize levels) ≃ Fin 256 :=
  finProdFinEquiv.trans (finCongr (by rw [Nat.mul_comm]; exact blockSize_mul_pow hL))

theorem blockIndex_apply (hL : levels ≤ 8) (t : Fin (2 ^ levels)) (r : Fin (blockSize levels)) :
    (blockIndex hL (t, r)).val = r.val + blockSize levels * t.val := rfl

theorem toR_modBinomial (hL : levels ≤ 8) (f : Poly (ZMod q) 256 (-1)) (γ : ZMod q)
    (hγ : γ ^ 2 ^ levels = -1) :
    (modBinomial levels hL f γ).toR = reduce hL γ hγ f.toR := by
  simp only [Poly.toR, map_sum, map_mul, map_pow, reduce_of, reduce_root]
  rw [← Fintype.sum_equiv (blockIndex hL) (fun p => AdjoinRoot.of _ f[(blockIndex hL p).val] *
      (R.root : R (ZMod q) (blockSize levels) γ) ^ (blockIndex hL p).val) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [modBinomial, Fin.getElem_fin, Poly.getElem_ofFn, map_sum, map_mul, map_pow,
    Finset.sum_mul, blockIndex_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  rw [pow_add, pow_mul, R.root_pow_n]
  ring

theorem modBinomial_mul [Fact q.Prime] (hL : levels ≤ 8) (f g : Poly (ZMod q) 256 (-1)) (γ : ZMod q)
    (hγ : γ ^ 2 ^ levels = -1) :
    modBinomial levels hL (f * g) γ = modBinomial levels hL f γ * modBinomial levels hL g γ := by
  apply Poly.toR_injective
  rw [Poly.toR_mul, toR_modBinomial hL _ _ hγ, toR_modBinomial hL _ _ hγ,
    toR_modBinomial hL _ _ hγ, Poly.toR_mul, map_mul]

theorem point_pow (ζ : ZMod q) (hζ : ζ ^ 2 ^ levels = -1) (i : ℕ) :
    point ζ levels i ^ 2 ^ levels = -1 := by
  rw [point, ← pow_mul, Nat.mul_comm, pow_mul, hζ]
  exact Odd.neg_one_pow ⟨bitRev levels i, rfl⟩

/-- The transform is multiplicative (`q` prime, `ζ^(2^levels) = -1`). -/
theorem nttSpec_mul [Fact q.Prime] (ζ : ZMod q) (hL : levels ≤ 8) (hζ : ζ ^ 2 ^ levels = -1)
    (f g : Poly (ZMod q) 256 (-1)) :
    nttSpec ζ levels (f * g) hL = nttSpec ζ levels f hL * nttSpec ζ levels g hL := by
  refine Residues.ext fun i => ?_
  rw [Residues.mul_apply, nttSpec_apply, nttSpec_apply, nttSpec_apply]
  exact modBinomial_mul hL f g _ (point_pow ζ hζ _)

/-! ### The inverse transform -/

section Inverse

open Finset

variable [Fact q.Prime] (ζ : ZMod q)

theorem two_ne_zero' [Fact (2 < q)] : (2 : ZMod q) ≠ 0 := by
  intro h
  have hdvd := (ZMod.natCast_eq_zero_iff 2 q).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by decide) hdvd
  have := (Fact.out : 2 < q)
  omega

theorem zeta_pow_succ (hζ : ζ ^ 2 ^ levels = -1) : ζ ^ 2 ^ (levels + 1) = 1 := by
  rw [pow_succ, pow_mul, hζ, neg_one_sq]

theorem orderOf_zeta [Fact (2 < q)] (hζ : ζ ^ 2 ^ levels = -1) : orderOf ζ = 2 ^ (levels + 1) :=
  orderOf_eq_prime_pow (by rw [hζ]; exact ZMod.neg_one_ne_one) (zeta_pow_succ ζ hζ)

theorem zeta_pow_two_mul_eq_one_iff [Fact (2 < q)] (hζ : ζ ^ 2 ^ levels = -1) (m : ℕ) :
    ζ ^ (2 * m) = 1 ↔ 2 ^ levels ∣ m := by
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_zeta ζ hζ, pow_succ, Nat.mul_comm (2 ^ levels) 2]
  exact Nat.mul_dvd_mul_iff_left (by decide)

theorem point_pow_eq (i m : ℕ) :
    point ζ levels i ^ m = ζ ^ m * (ζ ^ (2 * m)) ^ bitRev levels i := by
  rw [point, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem point_pow_succ (hζ : ζ ^ 2 ^ levels = -1) (i : ℕ) :
    point ζ levels i ^ 2 ^ (levels + 1) = 1 := by
  rw [pow_succ, pow_mul, point_pow ζ hζ, neg_one_sq]

theorem sum_bitRev (g : ℕ → ZMod q) :
    ∑ i : Fin (2 ^ levels), g (bitRev levels i) = ∑ i : Fin (2 ^ levels), g i :=
  Fintype.sum_bijective (fun i : Fin (2 ^ levels) => (⟨bitRev levels i, bitRev_lt _ _⟩ : Fin (2 ^ levels)))
    (Function.Involutive.bijective fun i => Fin.ext (bitRev_bitRev _ _ i.isLt)) _ _ fun _ => rfl

theorem sum_point_pow_of_dvd (hζ : ζ ^ 2 ^ levels = -1) (m : ℕ) (hm : 2 ^ (levels + 1) ∣ m) :
    ∑ i : Fin (2 ^ levels), point ζ levels i ^ m = 2 ^ levels := by
  have h1 : ζ ^ m = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, zeta_pow_succ ζ hζ, one_pow]
  have h2 : ζ ^ (2 * m) = 1 := by rw [pow_mul', h1, one_pow]
  simp [point_pow_eq, h1, h2]

theorem sum_point_pow_of_not_dvd [Fact (2 < q)] (hζ : ζ ^ 2 ^ levels = -1) (m : ℕ)
    (hm : ¬ 2 ^ levels ∣ m) :
    ∑ i : Fin (2 ^ levels), point ζ levels i ^ m = 0 := by
  simp only [point_pow_eq, ← Finset.mul_sum]
  rw [sum_bitRev (fun j => (ζ ^ (2 * m)) ^ j), Fin.sum_univ_eq_sum_range (fun j => (ζ ^ (2 * m)) ^ j)]
  have hne : ζ ^ (2 * m) ≠ 1 := fun h => hm ((zeta_pow_two_mul_eq_one_iff ζ hζ m).1 h)
  rw [geom_sum_eq hne, ← pow_mul, show 2 * m * 2 ^ levels = 2 ^ (levels + 1) * m by ring, pow_mul,
    zeta_pow_succ ζ hζ, one_pow, sub_self, zero_div, mul_zero]

theorem inv_pow_point (hζ : ζ ^ 2 ^ levels = -1) (i t : ℕ) (ht : t ≤ 2 ^ (levels + 1)) :
    (point ζ levels i)⁻¹ ^ t = point ζ levels i ^ (2 ^ (levels + 1) - t) := by
  rw [inv_pow]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_cancel' ht, point_pow_succ ζ hζ]

theorem not_dvd_of_ne {t t0 : ℕ} (ht : t < 2 ^ levels) (ht0 : t0 < 2 ^ levels) (hne : t ≠ t0) :
    ¬ 2 ^ levels ∣ t + (2 ^ (levels + 1) - t0) := by
  rintro ⟨c, hc⟩
  have hp : 0 < 2 ^ levels := Nat.two_pow_pos levels
  rw [pow_succ] at hc
  have hc2 : c = 2 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · have : 2 ^ levels * c ≤ 2 ^ levels * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    · rcases Nat.lt_or_ge c 3 with h' | h'
      · omega
      · have : 2 ^ levels * 3 ≤ 2 ^ levels * c := Nat.mul_le_mul_left _ h'
        omega
  subst hc2
  omega

theorem nttInvSpec_nttSpec [Fact (2 < q)] (hL : levels ≤ 8) (hζ : ζ ^ 2 ^ levels = -1)
    (f : Poly (ZMod q) 256 (-1)) : nttInvSpec ζ levels (nttSpec ζ levels f hL) = f := by
  ext k hk
  have ht0 : k / blockSize levels < 2 ^ levels := div_blockSize_lt hL hk
  have hle : k / blockSize levels ≤ 2 ^ (levels + 1) :=
    le_of_lt (lt_of_lt_of_le ht0 (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
  rw [getElem_nttInvSpec]
  have hsum : ∀ i : Fin (2 ^ levels),
      (nttSpec ζ levels f hL i)[k % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
          (point ζ levels i.val)⁻¹ ^ (k / blockSize levels) =
        ∑ t : Fin (2 ^ levels),
          f[k % blockSize levels + blockSize levels * t.val]'(block_idx_lt hL (Nat.mod_lt _ (blockSize_pos levels)) t.isLt) *
            point ζ levels i.val ^ (t.val + (2 ^ (levels + 1) - k / blockSize levels)) := by
    intro i
    rw [nttSpec_apply, getElem_modBinomial, inv_pow_point ζ hζ _ _ hle, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_assoc, ← pow_add]
  simp only [hsum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single ⟨k / blockSize levels, ht0⟩]
  · rw [sum_point_pow_of_dvd ζ hζ _ ⟨1, by
        show k / blockSize levels + (2 ^ (levels + 1) - k / blockSize levels) = 2 ^ (levels + 1) * 1
        rw [Nat.mul_one, Nat.add_sub_cancel' hle]⟩,
      ← mul_assoc, mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (two_ne_zero' (q := q))),
      one_mul]
    congr 1
    exact Nat.mod_add_div k (blockSize levels)
  · intro t _ ht
    rw [sum_point_pow_of_not_dvd ζ hζ _ (not_dvd_of_ne t.isLt ht0 fun h => ht (Fin.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Multiplying in the NTT domain computes the product in `ℤ_q[X]/(X^256 + 1)`. -/
theorem nttInvSpec_mul [Fact (2 < q)] (hL : levels ≤ 8) (hζ : ζ ^ 2 ^ levels = -1)
    (f g : Poly (ZMod q) 256 (-1)) :
    nttInvSpec ζ levels (nttSpec ζ levels f hL * nttSpec ζ levels g hL) = f * g := by
  rw [← nttSpec_mul ζ hL hζ, nttInvSpec_nttSpec ζ hL hζ]

end Inverse

/-! ### The recursive transform -/

section Recursive

/-- Reducing modulo `X^(2d) - γ'^2` and then `X^d - γ'` is reducing modulo `X^d - γ'`:
coefficient `r` is `lo[r] + γ' · hi[r]`. -/
theorem getElem_modBinomial_succ (hL : levels + 1 ≤ 8) (f : Poly (ZMod q) 256 (-1)) {γ γ' : ZMod q}
    (hγ : γ' ^ 2 = γ) (r : ℕ) (hr : r < blockSize (levels + 1)) :
    (modBinomial (levels + 1) hL f γ')[r] =
      (modBinomial levels (by omega) f γ)[r]'(by rw [blockSize_succ hL]; omega) +
        γ' * (modBinomial levels (by omega) f γ)[r + blockSize (levels + 1)]'(by rw [blockSize_succ hL]; omega) := by
  subst hγ
  simp only [getElem_modBinomial]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine ((Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl).symm).trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.sum_univ_two, finProdFinEquiv_apply_val, Fin.val_zero, Fin.val_one]
  have hd := blockSize_succ hL
  have h0 : r + blockSize (levels + 1) * (0 + 2 * t.val) = r + blockSize levels * t.val := by
    rw [hd]; ring
  have h1 : r + blockSize (levels + 1) * (1 + 2 * t.val) =
      r + blockSize (levels + 1) + blockSize levels * t.val := by
    rw [hd]; ring
  simp only [h0, h1]
  simp only [Nat.zero_add, pow_mul, pow_add, pow_one]
  ring

theorem point_succ_sq (ζ : ZMod q) (hζ : ζ ^ 2 ^ (levels + 1) = -1) (j : ℕ) :
    point ζ (levels + 1) j ^ 2 = point (ζ ^ 2) levels (j / 2) := by
  have h1 : ζ ^ 2 ^ (levels + 2) = 1 := by rw [pow_succ, pow_mul, hζ, neg_one_sq]
  simp only [point, ← pow_mul, bitRev_succ]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h]
    congr 1
    ring
  · rw [h, show (2 * (bitRev levels (j / 2) + 2 ^ levels * 1) + 1) * 2 =
      2 * (2 * bitRev levels (j / 2) + 1) + 2 ^ (levels + 2) by ring, pow_add, h1, mul_one]

/-- The recursive transform is the closed form. -/
theorem nttRec_eq_nttSpec (ζ : ZMod q) (hL : levels ≤ 8) (hζ : ζ ^ 2 ^ levels = -1)
    (f : Poly (ZMod q) 256 (-1)) : nttRec ζ levels hL f = nttSpec ζ levels f hL := by
  induction levels generalizing ζ with
  | zero =>
    ext i r hr
    simp [nttRec, nttSpec_apply, getElem_modBinomial]
  | succ l ih =>
    have hζ' : (ζ ^ 2) ^ 2 ^ l = -1 := by rw [← pow_mul, ← pow_succ']; exact hζ
    ext j r hr
    rw [nttRec, ih (ζ ^ 2) (by omega) hζ', Residues.getElem_split, nttSpec_apply, nttSpec_apply,
      getElem_modBinomial_succ hL f (point_succ_sq ζ hζ j)]

end Recursive

end

end Wychelean.PolyRing.NTT
