import Wychelean.Utils.PolyRing.ModMonic
import Wychelean.Utils.PolyRing.ModBinomialProperties

namespace Wychelean.Utils.PolyRing.Poly

open Polynomial

noncomputable section

variable {A : Type*} [CommRing A] {n d k : ℕ}

theorem toPoly_zero : (0 : Poly A n).toPoly = 0 := by
  simp [toPoly]

theorem toPoly_one [NeZero n] : (1 : Poly A n).toPoly = 1 := by
  rw [toPoly, Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi
    have : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toPoly_pad (f : Poly A n) : (pad d f).toPoly = f.toPoly := by
  ext i
  by_cases hi : i < d + n
  · rw [coeff_toPoly _ i hi, getElem_pad]
    split_ifs with h
    · rw [coeff_toPoly _ i h]
    · rw [coeff_toPoly_of_le _ i (by omega)]
  · rw [coeff_toPoly_of_le _ i (by omega), coeff_toPoly_of_le _ i (by omega)]

theorem toPoly_shift (μ : Poly A d) : (shift k μ).toPoly = X ^ k * μ.toPoly := by
  ext i
  rw [coeff_X_pow_mul']
  by_cases hi : i < d + k
  · rw [coeff_toPoly _ i hi, getElem_shift]
    split_ifs with h
    · rw [coeff_toPoly _ _ (by omega)]
    · rfl
  · rw [coeff_toPoly_of_le _ i (by omega)]
    split_ifs with h
    · rw [coeff_toPoly_of_le _ _ (by omega)]
    · rfl

theorem X_pow_mul_monicPoly (μ : Poly A d) :
    X ^ k * monicPoly μ = X ^ (d + k) + (shift k μ).toPoly := by
  rw [monicPoly, mul_add, ← pow_add, toPoly_shift, Nat.add_comm d k]

variable (μ : Poly A d)

theorem toPoly_reduceTop (f : Poly A (d + k + 1)) :
    (reduceTop μ f).toPoly = f.toPoly - C f[d + k] * (X ^ k * monicPoly μ) := by
  rw [X_pow_mul_monicPoly]
  ext i
  rw [coeff_sub, coeff_C_mul, coeff_add, coeff_X_pow]
  rcases Nat.lt_trichotomy i (d + k) with hi | rfl | hi
  · rw [coeff_toPoly _ i hi, getElem_reduceTop, coeff_toPoly _ i (Nat.lt_succ_of_lt hi),
      coeff_toPoly _ i hi]
    simp only [hi.ne, ite_false]
    ring
  · rw [coeff_toPoly_of_le _ _ le_rfl, coeff_toPoly _ _ (Nat.lt_succ_self _),
      coeff_toPoly_of_le _ _ le_rfl]
    simp only [ite_true]
    ring
  · rw [coeff_toPoly_of_le _ i hi.le, coeff_toPoly_of_le _ i hi, coeff_toPoly_of_le _ i hi.le]
    simp only [hi.ne', ite_false]
    ring

theorem dvd_sub_reduceTop (f : Poly A (d + k + 1)) :
    monicPoly μ ∣ f.toPoly - (reduceTop μ f).toPoly :=
  ⟨C f[d + k] * X ^ k, by rw [toPoly_reduceTop]; ring⟩

theorem dvd_sub_modMonicAux : ∀ (k : ℕ) (f : Poly A (d + k)),
    monicPoly μ ∣ f.toPoly - (modMonicAux μ k f).toPoly
  | 0, f => by rw [modMonicAux, sub_self]; exact dvd_zero _
  | k + 1, f => by
    rw [modMonicAux, ← sub_add_sub_cancel _ (reduceTop μ f).toPoly]
    exact dvd_add (dvd_sub_reduceTop μ f) (dvd_sub_modMonicAux k _)

/-- The core fact, over any commutative ring: the reduction differs from `f` by a multiple of
`X^d + μ`. -/
theorem dvd_sub_modMonic (f : Poly A n) : monicPoly μ ∣ f.toPoly - (modMonic μ f).toPoly := by
  rw [modMonic, ← toPoly_pad (d := d) f]
  exact dvd_sub_modMonicAux μ n _

theorem toR_modMonicAux (k : ℕ) (f : Poly A (d + k)) :
    toR μ (modMonicAux μ k f) = AdjoinRoot.mk _ f.toPoly := by
  rw [toR_eq_mk, AdjoinRoot.mk_eq_mk]
  have := dvd_sub_modMonicAux μ k f
  rwa [← dvd_neg, neg_sub] at this

/-- The reduction is the quotient map onto `A[X]/(X^d + μ)`. -/
theorem toR_modMonic (f : Poly A n) : toR μ (modMonic μ f) = AdjoinRoot.mk _ f.toPoly := by
  rw [modMonic, toR_modMonicAux, toPoly_pad]

/-- Two representatives of degree below `d` that agree modulo `X^d + μ` are equal. -/
theorem eq_of_dvd_sub_toPoly {b c : Poly A d} (h : monicPoly μ ∣ b.toPoly - c.toPoly) : b = c :=
  ext_toR μ (by rw [toR_eq_mk, toR_eq_mk, AdjoinRoot.mk_eq_mk]; exact h)

/-- On representatives, the reduction is `%ₘ (X^d + μ)`. -/
theorem toPoly_modMonic [Nontrivial A] (f : Poly A n) :
    (modMonic μ f).toPoly = f.toPoly %ₘ monicPoly μ := by
  have hmonic := monicPoly_monic μ
  have h := dvd_sub_modMonic μ f
  rw [← dvd_neg, neg_sub] at h
  rw [← modByMonic_eq_of_dvd_sub hmonic h]
  symm
  rw [modByMonic_eq_self_iff hmonic, degree_monicPoly]
  exact degree_toPoly_lt _

theorem modMonic_eq_iff_dvd (f : Poly A n) (b : Poly A d) :
    modMonic μ f = b ↔ monicPoly μ ∣ f.toPoly - b.toPoly := by
  constructor
  · rintro rfl
    exact dvd_sub_modMonic μ f
  · intro h
    apply eq_of_dvd_sub_toPoly μ
    rw [← sub_add_sub_cancel _ f.toPoly]
    refine dvd_add ?_ h
    have := dvd_sub_modMonic μ f
    rwa [← dvd_neg, neg_sub] at this

/-- The decidable test that `X^d + μ` divides a polynomial. -/
theorem modMonic_eq_zero_iff_dvd (f : Poly A n) : modMonic μ f = 0 ↔ monicPoly μ ∣ f.toPoly := by
  rw [modMonic_eq_iff_dvd, toPoly_zero, sub_zero]

theorem modMonic_self (f : Poly A d) : modMonic μ f = f :=
  (modMonic_eq_iff_dvd μ f f).2 (by rw [sub_self]; exact dvd_zero _)

theorem modMonic_one [NeZero d] [NeZero n] : modMonic μ (1 : Poly A n) = 1 :=
  (modMonic_eq_iff_dvd μ _ _).2 (by rw [toPoly_one, toPoly_one, sub_self]; exact dvd_zero _)

/-- Reducing modulo `X^d₁ + μ₁` and then modulo a divisor `X^d + μ₂` of it is reducing modulo
`X^d + μ₂`: the tower of quotients. -/
theorem modMonic_modMonic {d₁ : ℕ} {μ₁ : Poly A d₁} (h : monicPoly μ ∣ monicPoly μ₁) (f : Poly A n) :
    modMonic μ (modMonic μ₁ f) = modMonic μ f := by
  rw [modMonic_eq_iff_dvd]
  have h₁ := h.trans (dvd_sub_modMonic μ₁ f)
  have h₂ := dvd_sub_modMonic μ f
  have := dvd_sub h₂ h₁
  rwa [show f.toPoly - (modMonic μ f).toPoly - (f.toPoly - (modMonic μ₁ f).toPoly) =
    (modMonic μ₁ f).toPoly - (modMonic μ f).toPoly by ring] at this

/-! ### Products -/

theorem toPoly_conv {a b : ℕ} (f : Poly A a) (g : Poly A b) :
    (conv f g).toPoly = f.toPoly * g.toPoly := by
  ext k
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f.toPoly.coeff i * g.toPoly.coeff j)]
  -- both sides are `∑ i, G i` for `G i = if i ≤ k ∧ k - i < b then f[i] g[k-i] else 0`
  set G : ℕ → A := fun i => if i ≤ k ∧ k - i < b then f.toPoly.coeff i * g.toPoly.coeff (k - i) else 0
    with hG
  have hL : (conv f g).toPoly.coeff k = ∑ i ∈ Finset.range a, G i := by
    by_cases hk : k < a + b
    · rw [coeff_toPoly _ k hk, getElem_conv, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hG]
      split_ifs with h
      · rw [coeff_toPoly _ _ i.isLt, coeff_toPoly _ _ h.2]
        rfl
      · rfl
    · rw [coeff_toPoly_of_le _ k (by omega)]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      simp only [hG]
      rw [Finset.mem_range] at hi
      split_ifs with h
      · omega
      · rfl
  have hR : ∑ i ∈ Finset.range (k + 1), f.toPoly.coeff i * g.toPoly.coeff (k - i) =
      ∑ i ∈ Finset.range (k + 1), G i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp only [hG]
    split_ifs with h
    · rfl
    · rw [coeff_toPoly_of_le g _ (by omega), mul_zero]
  rw [hL, hR]
  -- extend both to `range (a + k + 1)`, where `G` vanishes outside each
  have hz : ∀ i, a ≤ i ∨ k < i → G i = 0 := by
    intro i hi
    simp only [hG]
    split_ifs with h
    · rcases hi with hi | hi
      · rw [coeff_toPoly_of_le f _ hi, zero_mul]
      · omega
    · rfl
  rw [Finset.sum_subset (Finset.range_mono (by omega : a ≤ a + k + 1))
      (fun i _ hia => hz i (Or.inl (by rw [Finset.mem_range] at hia; omega))),
    Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ a + k + 1))
      (fun i _ hik => hz i (Or.inr (by rw [Finset.mem_range] at hik; omega)))]

theorem dvd_sub_mulMonic (f g : Poly A d) :
    monicPoly μ ∣ f.toPoly * g.toPoly - (mulMonic μ f g).toPoly := by
  rw [mulMonic, ← toPoly_conv]
  exact dvd_sub_modMonicAux μ d _

/-- The product `mulMonic` is the product of `A[X]/(X^d + μ)`. -/
theorem toR_mulMonic (f g : Poly A d) : toR μ (mulMonic μ f g) = toR μ f * toR μ g := by
  rw [mulMonic, toR_modMonicAux, toPoly_conv, map_mul, toR_eq_mk, toR_eq_mk]

/-- The wrap-around product is the monic product at the binomial `X^d - c`. -/
theorem mulMonic_binomial (c : A) (f g : Poly A d) : mulMonic (binomial c) f g = mulMod c f g :=
  ext_toR _ (by intro; rw [toR_mulMonic, toR_mulMod])

/-- Reduction respects products across a divisibility of moduli. -/
theorem modMonic_mulMonic {d' : ℕ} {μ' : Poly A d'} (h : monicPoly μ ∣ monicPoly μ') (f g : Poly A d') :
    modMonic μ (mulMonic μ' f g) = mulMonic μ (modMonic μ f) (modMonic μ g) := by
  refine ext_toR μ ?_
  intro
  rw [toR_mulMonic, toR_modMonic, toR_modMonic, toR_modMonic, ← map_mul, AdjoinRoot.mk_eq_mk]
  have := h.trans (dvd_sub_mulMonic μ' f g)
  rwa [← dvd_neg, neg_sub] at this

/-- The closed-form binomial reduction is the long division at `X^d - δ`. -/
theorem modMonic_binomial {r : ℕ} [NeZero r] (p : Poly A n) (δ : A) (hn : n = r * d) :
    modMonic (binomial δ) p = p.modBinomial r d δ hn := by
  rw [modMonic_eq_iff_dvd]
  have h := toR_modBinomial p δ hn (γ := δ ^ r) rfl
  rw [toR_eq_mk, toR_eq_mk, R.reduce_mk, AdjoinRoot.mk_eq_mk] at h
  rwa [← dvd_neg, neg_sub] at h

end

end Wychelean.Utils.PolyRing.Poly
