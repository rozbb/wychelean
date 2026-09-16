import Wychelean.PolyRing.Residues
import Wychelean.PolyRing.ModBinomial
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
One layer of a number-theoretic transform at any radix. `split r` reduces every residue modulo
`X^{r·d} - γ i` to its `r` residues modulo `X^d - γ' (k + r·i)`; when the `γ' (k + r·i)` are the
`r`-th roots of `γ i` this is the Chinese remainder map, and `splitInv r` inverts it. Layers
compose (`split_split`), so any schedule of radices computes the same residues as one layer.
-/

namespace Wychelean.PolyRing.Residues

variable {F : Type*} {d m : ℕ} {γ : Fin m → F}

theorem div_lt {r m m' j : ℕ} (hm : m' = m * r) (hj : j < m') : j / r < m :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hm ▸ hj)

theorem block_lt {r m m' s i : ℕ} (hm : m' = m * r) (hs : s < r) (hi : i < m) : s + r * i < m' := by
  rw [hm]; exact flat_idx_lt hs hi

/-- `γ' j` is an `r`-th root of `γ (j / r)`: residue `j` of the layer is a quotient of the residue
`j / r` above it (`split_mul`, `split_toR`). -/
def LayerPoints [Monoid F] (r : ℕ) {m' : ℕ} (γ : Fin m → F) (γ' : Fin m' → F) (hm : m' = m * r) :
    Prop :=
  ∀ j : Fin m', γ' j ^ r = γ ⟨j / r, div_lt hm j.isLt⟩

/-- Above each residue `i` the `r` points `γ' (k + r·i)` are all the `r`-th roots of `γ i ≠ 0`,
i.e. `δ·ω^(σ k)` for a primitive `r`-th root of unity `ω` and a permutation `σ`: the layer is the
Chinese remainder isomorphism (`splitInv_split`, `split_splitInv`). -/
def SplitPoints [CommRing F] (r : ℕ) {m' : ℕ} (γ : Fin m → F) (γ' : Fin m' → F) (hm : m' = m * r) :
    Prop :=
  ∀ i : Fin m, γ i ≠ 0 ∧ ∃ (ω δ : F) (σ : Fin r ≃ Fin r), IsPrimitiveRoot ω r ∧ δ ^ r = γ i ∧
    ∀ k : Fin r, γ' ⟨k + r * i, block_lt hm k.isLt i.isLt⟩ = δ * ω ^ (σ k).val

theorem radix_pos {r m m' : ℕ} (hm : m' = m * r) (j : Fin m') : 0 < r :=
  Nat.pos_of_ne_zero fun h => by have := j.isLt; simp [h] at hm; omega

theorem SplitPoints.layerPoints [CommRing F] {r m' : ℕ} {γ' : Fin m' → F} {hm : m' = m * r}
    (h : SplitPoints r γ γ' hm) : LayerPoints r γ γ' hm := by
  intro j
  obtain ⟨_, ω, δ, σ, hω, hδ, hpts⟩ := h ⟨j / r, div_lt hm j.isLt⟩
  have hk := hpts ⟨j % r, Nat.mod_lt _ (radix_pos hm j)⟩
  rw [show (⟨j % r + r * (j / r), _⟩ : Fin m') = j from Fin.ext (Nat.mod_add_div _ _)] at hk
  rw [hk, mul_pow, ← pow_mul, mul_comm _ r, pow_mul, hω.pow_eq_one, one_pow, mul_one, hδ]

section Split

variable [CommRing F] {d' m' : ℕ}

/-- One layer of radix `r`: residue `j` is `a (j / r) mod (X^d - γ' j)`. -/
def split (r : ℕ) (a : Residues F d' m γ) (γ' : Fin m' → F) (hd : d' = r * d) (hm : m' = m * r) :
    Residues F d m' γ' :=
  ofFn fun j => (a ⟨j / r, div_lt hm j.isLt⟩).modBinomial r d (γ' j) hd

variable (r : ℕ) (a : Residues F d' m γ) (γ' : Fin m' → F) (hd : d' = r * d) (hm : m' = m * r)

theorem split_apply (j : Fin m') :
    split r a γ' hd hm j = (a ⟨j / r, div_lt hm j.isLt⟩).modBinomial r d (γ' j) hd :=
  apply_ofFn ..

theorem getElem_split (j : Fin m') (s : ℕ) (hs : s < d) :
    (split r a γ' hd hm j)[s] = ∑ t : Fin r,
      (a ⟨j / r, div_lt hm j.isLt⟩)[s + d * t.val]'(by rw [hd]; exact Poly.idx_lt hs t.isLt) *
        γ' j ^ t.val := by
  rw [split_apply, Poly.getElem_modBinomial]

/-- Radix two is one Cooley–Tukey layer: residue `j` is `lo + γ' j · hi` for
`a (j / 2) = lo + X^d · hi`. -/
theorem getElem_split_two (h2d : d' = 2 * d) (h2m : m' = m * 2) (j : Fin m') (s : ℕ) (hs : s < d) :
    (split 2 a γ' h2d h2m j)[s] =
      (a ⟨j / 2, div_lt h2m j.isLt⟩)[s]'(by
          rw [h2d]; exact Nat.lt_of_lt_of_le hs (Nat.le_mul_of_pos_left d two_pos)) +
        γ' j * (a ⟨j / 2, div_lt h2m j.isLt⟩)[s + d]'(by
          rw [h2d, two_mul]; exact Nat.add_lt_add_right hs d) := by
  rw [split_apply, Poly.getElem_modBinomial_two]

theorem split_add (b : Residues F d' m γ) :
    split r (a + b) γ' hd hm = split r a γ' hd hm + split r b γ' hd hm := by
  ext j
  simp [split_apply, Poly.modBinomial_add]

theorem split_sub (b : Residues F d' m γ) :
    split r (a - b) γ' hd hm = split r a γ' hd hm - split r b γ' hd hm := by
  ext j
  simp [split_apply, Poly.modBinomial_sub]

theorem split_zero : split r (0 : Residues F d' m γ) γ' hd hm = 0 := by
  ext j
  simp [split_apply, Poly.modBinomial_zero]

/-- Two layers are one layer of the product radix when the second layer's points are roots of
the first's (the tower of quotients). -/
theorem split_split {d'' m₁ m₂ : ℕ} (r₁ r₂ : ℕ) (a : Residues F d'' m γ) (γ₁ : Fin m₁ → F)
    (γ₂ : Fin m₂ → F) (hd₁ : d'' = r₁ * d') (hm₁ : m₁ = m * r₁) (hd₂ : d' = r₂ * d)
    (hm₂ : m₂ = m₁ * r₂) (h : LayerPoints r₂ γ₁ γ₂ hm₂) (hd : d'' = (r₁ * r₂) * d)
    (hm : m₂ = m * (r₁ * r₂)) :
    split r₂ (split r₁ a γ₁ hd₁ hm₁) γ₂ hd₂ hm₂ = split (r₁ * r₂) a γ₂ hd hm := by
  refine ext fun j => ?_
  rw [split_apply, split_apply, split_apply, Poly.modBinomial_modBinomial _ r₁ r₂ hd₁ hd₂ (h j) hd,
    show (⟨j / r₂ / r₁, div_lt hm₁ (div_lt hm₂ j.isLt)⟩ : Fin m) = ⟨j / (r₁ * r₂), div_lt hm j.isLt⟩
      from Fin.ext (show j / r₂ / r₁ = j / (r₁ * r₂) by rw [Nat.div_div_eq_div_mul, Nat.mul_comm])]

/-- `split_split` with the product radix given by an equation. -/
theorem split_split' {d'' m₁ m₂ : ℕ} (r₁ r₂ : ℕ) (a : Residues F d'' m γ) (γ₁ : Fin m₁ → F)
    (γ₂ : Fin m₂ → F) (hd₁ : d'' = r₁ * d') (hm₁ : m₁ = m * r₁) (hd₂ : d' = r₂ * d)
    (hm₂ : m₂ = m₁ * r₂) (h : LayerPoints r₂ γ₁ γ₂ hm₂) {r : ℕ} (hr : r = r₁ * r₂)
    (hd : d'' = r * d) (hm : m₂ = m * r) :
    split r₂ (split r₁ a γ₁ hd₁ hm₁) γ₂ hd₂ hm₂ = split r a γ₂ hd hm := by
  subst hr
  exact split_split r₁ r₂ a γ₁ γ₂ hd₁ hm₁ hd₂ hm₂ h hd hm

end Split

section Inverse

variable [Field F] {d' m' : ℕ}

/-- The inverse layer: residue `i` is the polynomial with residues `b (k + r·i)` modulo
`X^d - γ' (k + r·i)`. -/
def splitInv (r : ℕ) (b : Residues F d m' γ') (γ : Fin m → F) (hd : d' = r * d) (hm : m' = m * r) :
    Residues F d' m γ :=
  ofFn fun i => Poly.merge r d hd (fun k => γ' ⟨k + r * i, block_lt hm k.isLt i.isLt⟩)
    fun k => b ⟨k + r * i, block_lt hm k.isLt i.isLt⟩

theorem splitInv_apply (r : ℕ) (b : Residues F d m' γ') (γ : Fin m → F) (hd : d' = r * d)
    (hm : m' = m * r) (i : Fin m) :
    splitInv r b γ hd hm i = Poly.merge r d hd
      (fun k => γ' ⟨k + r * i, block_lt hm k.isLt i.isLt⟩)
      fun k => b ⟨k + r * i, block_lt hm k.isLt i.isLt⟩ :=
  apply_ofFn ..

end Inverse

end Wychelean.PolyRing.Residues
