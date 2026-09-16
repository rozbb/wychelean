import Wychelean.PolyRing.Split
import Wychelean.PolyRing.ModBinomialProperties
import Mathlib.Algebra.Ring.GeomSum

/-!
A layer is a quotient map when its points are roots of the points above (`LayerPoints`): it is
multiplicative and agrees with Mathlib's maps between the `AdjoinRoot`s. It is a bijection when the
points above each residue are all the roots (`SplitPoints`): `splitInv` inverts it on both sides,
by the orthogonality of the powers of a primitive root of unity. The characterisations
`split_eq_iff_*` are what an external witness of a layer's output has to discharge.
-/

namespace Wychelean.PolyRing

open Polynomial

/-! ### Orthogonality -/

namespace Poly

variable {F : Type*} [Field F] {n r d : ℕ}

/-- The `u`-th powers of the `r`-th roots of unity, in any order, sum to `r` or `0`. -/
theorem sum_pow_perm {ω : F} (hω : IsPrimitiveRoot ω r) (σ : Fin r ≃ Fin r) (u : ℕ) :
    ∑ k : Fin r, (ω ^ (σ k).val) ^ u = if r ∣ u then (r : F) else 0 := by
  have hcomm : ∀ k : Fin r, (ω ^ (σ k).val) ^ u = (ω ^ u) ^ (σ k).val := fun k => pow_right_comm ..
  simp_rw [hcomm]
  rw [Equiv.sum_comp σ (fun k : Fin r => (ω ^ u) ^ k.val),
    Fin.sum_univ_eq_sum_range (fun k => (ω ^ u) ^ k) r]
  split_ifs with h
  · rw [(hω.pow_eq_one_iff_dvd u).2 h]
    simp
  · have hne : ω ^ u ≠ 1 := fun h1 => h ((hω.pow_eq_one_iff_dvd u).1 h1)
    have := geom_sum_mul (ω ^ u) r
    rw [← pow_mul, mul_comm u r, pow_mul, hω.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)

theorem sum_pow_pow {ω : F} (hω : IsPrimitiveRoot ω r) (u : ℕ) :
    ∑ t : Fin r, (ω ^ u) ^ t.val = if r ∣ u then (r : F) else 0 := by
  rw [← sum_pow_perm hω (Equiv.refl _) u]
  exact Finset.sum_congr rfl fun t _ => (pow_right_comm ..).symm

/-- The `u`-th powers of the `r`-th roots `δ₀·ω^(σ k)` of `δ₀^r` sum to `r·δ₀^u` or `0`. -/
theorem sum_root_pow {ω δ₀ : F} (hω : IsPrimitiveRoot ω r) (σ : Fin r ≃ Fin r) (δ : Fin r → F)
    (hpts : ∀ k, δ k = δ₀ * ω ^ (σ k).val) (u : ℕ) :
    ∑ k : Fin r, δ k ^ u = δ₀ ^ u * (if r ∣ u then (r : F) else 0) := by
  simp_rw [hpts, mul_pow, ← Finset.mul_sum, sum_pow_perm hω σ]

theorem root_pow_eq {ω δ₀ γ : F} (hω : IsPrimitiveRoot ω r) (hδ₀ : δ₀ ^ r = γ) (k : ℕ) :
    (δ₀ * ω ^ k) ^ r = γ := by
  rw [mul_pow, ← pow_mul, mul_comm k r, pow_mul, hω.pow_eq_one, one_pow, mul_one, hδ₀]

theorem inv_pow_root {δ γ : F} (hδ : δ ^ r = γ) (hγ : γ ≠ 0) {t : ℕ} (ht : t ≤ r) :
    δ⁻¹ ^ t = γ⁻¹ * δ ^ (r - t) := by
  rw [inv_pow]
  apply inv_eq_of_mul_eq_one_right
  rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' ht, hδ, inv_mul_cancel₀ hγ]

theorem not_dvd_of_ne {t t₀ : ℕ} (ht : t < r) (ht₀ : t₀ < r) (hne : t ≠ t₀) :
    ¬ r ∣ t + (r - t₀) := by
  rintro ⟨c, hc⟩
  rcases c with _ | _ | c
  · simp at hc; omega
  · simp at hc; omega
  · have := Nat.mul_le_mul_left r (show 2 ≤ c + 1 + 1 by omega)
    rw [Nat.mul_two] at this
    omega

theorem dvd_self_of_le {t₀ : ℕ} (ht₀ : t₀ ≤ r) : r ∣ t₀ + (r - t₀) :=
  ⟨1, by omega⟩

/-! ### The inverse of a reduction onto all the roots -/

section Merge

variable (hn : n = r * d) (hr : (r : F) ≠ 0) {γ ω δ₀ : F} (hγ : γ ≠ 0)
  (hω : IsPrimitiveRoot ω r) (σ : Fin r ≃ Fin r) (hδ₀ : δ₀ ^ r = γ) (δ : Fin r → F)
  (hpts : ∀ k, δ k = δ₀ * ω ^ (σ k).val)

theorem getElem_merge_block (b : Fin r → Poly F d) (s t : ℕ) (hs : s < d) (ht : t < r) :
    (merge r d hn δ b)[s + d * t]'(by rw [hn]; exact idx_lt hs ht) =
      (r : F)⁻¹ * ∑ k : Fin r, (b k)[s] * (δ k)⁻¹ ^ t := by
  rw [getElem_merge]
  have hd : 0 < d := Nat.pos_of_ne_zero fun h => by subst h; exact absurd hs (Nat.not_lt_zero _)
  have h1 : (s + d * t) % d = s := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have h2 : (s + d * t) / d = t := by rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hs, Nat.zero_add]
  simp only [h1, h2]

include hr hγ hω hδ₀ hpts in
/-- Merging the reductions of `p` onto all the roots gives back `p`. -/
theorem merge_modBinomial (p : Poly F n) :
    merge r d hn δ (fun k => p.modBinomial r d (δ k) hn) = p := by
  have hδr : ∀ k, δ k ^ r = γ := fun k => by rw [hpts]; exact root_pow_eq hω hδ₀ _
  ext x hx
  have hd : 0 < d := pos_of_eq_mul hn hx
  have ht₀ : x / d < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn ▸ hx)
  rw [getElem_merge]
  have hsum : ∀ k : Fin r,
      (p.modBinomial r d (δ k) hn)[x % d]'(Nat.mod_lt _ hd) * (δ k)⁻¹ ^ (x / d) =
        ∑ t : Fin r, p[x % d + d * t.val]'(by rw [hn]; exact idx_lt (Nat.mod_lt _ hd) t.isLt) *
          (γ⁻¹ * δ k ^ (t.val + (r - x / d))) := by
    intro k
    rw [getElem_modBinomial, inv_pow_root (hδr k) hγ ht₀.le, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_add]
    ring
  simp only [hsum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_root_pow hω σ δ hpts]
  rw [Finset.sum_eq_single ⟨x / d, ht₀⟩]
  · simp only [Nat.add_sub_cancel' ht₀.le, hδ₀, Nat.mod_add_div x d, dvd_refl, ite_true]
    rw [inv_mul_cancel_left₀ hγ, mul_comm _ (r : F), inv_mul_cancel_left₀ hr]
  · intro t _ ht
    have hnd := not_dvd_of_ne t.isLt ht₀ fun h => ht (Fin.ext h)
    simp [hnd]
  · intro h
    exact absurd (Finset.mem_univ _) h

include hr hγ hω hδ₀ hpts in
/-- Reducing a merge onto one of the roots gives back that residue. -/
theorem modBinomial_merge (b : Fin r → Poly F d) (j : Fin r) :
    (merge r d hn δ b).modBinomial r d (δ j) hn = b j := by
  have hr0 : r ≠ 0 := fun h => hr (by simp [h])
  have hδ₀0 : δ₀ ≠ 0 := fun h => hγ (by rw [← hδ₀, h, zero_pow hr0])
  ext s hs
  rw [getElem_modBinomial]
  have hblk : ∀ t : Fin r, (merge r d hn δ b)[s + d * t.val]'(by rw [hn]; exact idx_lt hs t.isLt) =
      (r : F)⁻¹ * ∑ k : Fin r, (b k)[s] * (δ k)⁻¹ ^ t.val := fun t =>
    getElem_merge_block hn δ b s t hs t.isLt
  simp only [hblk]
  have key : ∀ (k : Fin r) (t : ℕ), (δ k)⁻¹ ^ t * δ j ^ t =
      (ω ^ ((σ j).val + (r - (σ k).val))) ^ t := by
    intro k t
    rw [← mul_pow]
    congr 1
    rw [hpts k, hpts j, mul_inv, ← inv_pow, inv_pow_root hω.pow_eq_one one_ne_zero (σ k).isLt.le,
      inv_one, one_mul, mul_mul_mul_comm, inv_mul_cancel₀ hδ₀0, one_mul, ← pow_add, Nat.add_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ (k : Fin r) (t : Fin r),
      (r : F)⁻¹ * ((b k)[s] * (δ k)⁻¹ ^ t.val) * δ j ^ t.val =
        (r : F)⁻¹ * (b k)[s] * (ω ^ ((σ j).val + (r - (σ k).val))) ^ t.val := by
    intro k t
    rw [← key, mul_assoc, mul_assoc, mul_assoc]
  simp only [hterm, ← Finset.mul_sum, sum_pow_pow hω]
  rw [Finset.sum_eq_single j]
  · simp only [dvd_self_of_le (σ j).isLt.le, ite_true]
    rw [mul_assoc, mul_comm _ (r : F), inv_mul_cancel_left₀ hr]
  · intro k _ hk
    have hnd := not_dvd_of_ne (σ j).isLt (σ k).isLt fun h => hk (σ.injective (Fin.ext h)).symm
    simp [hnd]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Merge

end Poly

/-! ### Layers on residues -/

namespace Residues

variable {F : Type*} {d m : ℕ} {γ : Fin m → F} {d' m' : ℕ} {γ' : Fin m' → F}

theorem block_div {r i k : ℕ} (hr : 0 < r) (hk : k < r) : (k + r * i) / r = i := by
  rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hk, Nat.zero_add]

section Quotient

variable [CommRing F] (r : ℕ) (a : Residues F d' m γ) (hd : d' = r * d) (hm : m' = m * r)
  (h : LayerPoints r γ γ' hm)

include h in
theorem split_mul [IsDomain F] (b : Residues F d' m γ) :
    split r (a * b) γ' hd hm = split r a γ' hd hm * split r b γ' hd hm := by
  ext j
  rw [mul_apply, split_apply, split_apply, split_apply, mul_apply, Poly.modBinomial_mulMod _ _ _ (h j)]

include h in
theorem split_one [IsDomain F] [NeZero r] [NeZero d] : split r (1 : Residues F d' m γ) γ' hd hm = 1 := by
  ext j
  rw [one_apply, split_apply, one_apply, Poly.modBinomial_one _ _ (h j)]

include h in
/-- Residue `j` of the layer is the image of residue `j / r` under the quotient map. -/
theorem split_toR [IsDomain F] (j : Fin m') :
    (split r a γ' hd hm).toR j = R.reduce r d hd (γ' j) (h j) (a.toR ⟨j / r, div_lt hm j.isLt⟩) := by
  rw [toR, toR, split_apply, Poly.toR_modBinomial]

include h in
theorem split_eq_iff_toR [IsDomain F] (b : Residues F d m' γ') :
    split r a γ' hd hm = b ↔
      ∀ j, b.toR j = R.reduce r d hd (γ' j) (h j) (a.toR ⟨j / r, div_lt hm j.isLt⟩) := by
  rw [Residues.ext_iff]
  exact forall_congr' fun j => by rw [split_apply, toR, toR, Poly.modBinomial_eq_iff_toR _ _ _ (h j)]

include h in
/-- Residue `j` of the layer is the residue whose representative differs from that of `a (j / r)`
by a multiple of `X^d - γ' j`. -/
theorem split_eq_iff_dvd [Nontrivial F] [NeZero d] (b : Residues F d m' γ') :
    split r a γ' hd hm = b ↔
      ∀ j, (X ^ d - C (γ' j) : F[X]) ∣ (a ⟨j / r, div_lt hm j.isLt⟩).toPoly - (b j).toPoly := by
  rw [Residues.ext_iff]
  exact forall_congr' fun j => by rw [split_apply, Poly.modBinomial_eq_iff_dvd _ _ _ (h j)]

end Quotient

section Inverse

variable [Field F] (r : ℕ) (hd : d' = r * d) (hm : m' = m * r) (h : SplitPoints r γ γ' hm)
  (hr : (r : F) ≠ 0)

include h hr in
theorem splitInv_split (a : Residues F d' m γ) : splitInv r (split r a γ' hd hm) γ hd hm = a := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h0 => hr (by simp [h0])
  refine Residues.ext fun i => ?_
  rw [splitInv_apply]
  obtain ⟨hγi, ω, δ₀, σ, hω, hδ₀, hpts⟩ := h i
  have hblock : ∀ k : Fin r, split r a γ' hd hm ⟨k + r * i, block_lt hm k.isLt i.isLt⟩ =
      (a i).modBinomial r d (γ' ⟨k + r * i, block_lt hm k.isLt i.isLt⟩) hd := fun k => by
    rw [split_apply, show (⟨(k + r * i) / r, div_lt hm (block_lt hm k.isLt i.isLt)⟩ : Fin m) = i
      from Fin.ext (block_div hr0 k.isLt)]
  simp only [hblock]
  exact Poly.merge_modBinomial hd hr hγi hω σ hδ₀ _ hpts _

include h hr in
theorem split_splitInv (b : Residues F d m' γ') : split r (splitInv r b γ hd hm) γ' hd hm = b := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h0 => hr (by simp [h0])
  refine Residues.ext fun j => ?_
  rw [split_apply, splitInv_apply]
  obtain ⟨hγi, ω, δ₀, σ, hω, hδ₀, hpts⟩ := h ⟨j / r, div_lt hm j.isLt⟩
  have := Poly.modBinomial_merge hd hr hγi hω σ hδ₀ _ hpts
    (fun k => b ⟨k + r * (j / r), block_lt hm k.isLt (div_lt hm j.isLt)⟩) ⟨j % r, Nat.mod_lt _ hr0⟩
  have hj : (⟨j % r + r * (j / r), block_lt hm (Nat.mod_lt _ hr0) (div_lt hm j.isLt)⟩ : Fin m') = j :=
    Fin.ext (Nat.mod_add_div _ _)
  rw [hj] at this
  exact this

include h hr in
theorem splitInv_eq_iff (b : Residues F d m' γ') (a : Residues F d' m γ) :
    splitInv r b γ hd hm = a ↔ split r a γ' hd hm = b :=
  ⟨fun e => e ▸ split_splitInv r hd hm h hr b, fun e => e ▸ splitInv_split r hd hm h hr a⟩

include h hr in
theorem split_bijective : Function.Bijective (fun a : Residues F d' m γ => split r a γ' hd hm) :=
  ⟨fun a b e => by
    have e' : split r a γ' hd hm = split r b γ' hd hm := e
    rw [← splitInv_split r hd hm h hr a, e', splitInv_split r hd hm h hr b],
   fun b => ⟨splitInv r b γ hd hm, split_splitInv r hd hm h hr b⟩⟩

end Inverse

end Residues

end Wychelean.PolyRing
