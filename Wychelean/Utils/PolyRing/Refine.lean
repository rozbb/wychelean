import Wychelean.Utils.PolyRing.Split

namespace Wychelean.Utils.PolyRing

open Polynomial

namespace Poly

variable {F : Type*} [CommRing F] {d : ℕ}

/-- The coefficient vector of `X^d + μ`, for computing with the modulus itself. -/
def monicVec (μ : Poly F d) : Poly F (d + 1) :=
  ofFn fun i => if h : i.val < d then μ[i.val] else 1

@[simp] theorem getElem_monicVec (μ : Poly F d) (i : ℕ) (hi : i < d + 1) :
    (monicVec μ)[i] = if h : i < d then μ[i] else 1 :=
  getElem_ofFn ..

theorem toPoly_monicVec (μ : Poly F d) : (monicVec μ).toPoly = monicPoly μ := by
  ext i
  rw [monicPoly, coeff_add, coeff_X_pow]
  rcases Nat.lt_trichotomy i d with hi | rfl | hi
  · rw [coeff_toPoly _ i (by omega), coeff_toPoly _ i hi]
    simp [getElem_monicVec, hi, hi.ne]
  · rw [coeff_toPoly _ i (by omega), coeff_toPoly_of_le _ i le_rfl]
    simp [getElem_monicVec]
  · rw [coeff_toPoly_of_le _ i (by omega), coeff_toPoly_of_le _ i hi.le]
    simp [hi.ne']

end Poly

namespace Residues

variable {F : Type*} [CommRing F] {d d' m m' : ℕ} {μ : Fin m → Poly F d'} {μ' : Fin m' → Poly F d}

/-- Component `j` of the layer divides component `j / r` above it. -/
def LayerDvd (r : ℕ) (μ : Fin m → Poly F d') (μ' : Fin m' → Poly F d) (hm : m' = m * r) : Prop :=
  ∀ j : Fin m', Poly.monicPoly (μ' j) ∣ Poly.monicPoly (μ ⟨j / r, div_lt hm j.isLt⟩)

/-- The computable form of `LayerDvd`: each new component divides the one above it iff the long
division of the latter by the former leaves no remainder. -/
theorem layerDvd_iff {r : ℕ} {hm : m' = m * r} : LayerDvd r μ μ' hm ↔
    ∀ j : Fin m', Poly.modMonic (μ' j) (Poly.monicVec (μ ⟨j / r, div_lt hm j.isLt⟩)) = 0 := by
  simp only [LayerDvd, Poly.modMonic_eq_zero_iff_dvd, Poly.toPoly_monicVec]

instance {r : ℕ} {hm : m' = m * r} [DecidableEq F] : Decidable (LayerDvd r μ μ' hm) :=
  decidable_of_iff _ layerDvd_iff.symm

/-- Binomial layers are divisibility layers. -/
theorem LayerPoints.layerDvd {r : ℕ} [NeZero r] {γ : Fin m → F} {γ' : Fin m' → F} {hm : m' = m * r}
    (hd : d' = r * d) (h : LayerPoints r γ γ' hm) :
    LayerDvd r (fun i => (Poly.binomial (γ i) : Poly F d')) (fun j => (Poly.binomial (γ' j) : Poly F d)) hm :=
  fun j => Poly.monicPoly_binomial_dvd hd (h j)

/-- One layer between arbitrary moduli: residue `j` is `a (j / r) mod (X^d + μ' j)`. -/
def refine (r : ℕ) (a : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    Residues F d m' μ' :=
  ofFn fun j => Poly.modMonic (μ' j) (a ⟨j / r, div_lt hm j.isLt⟩)

theorem refine_apply (r : ℕ) (a : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r)
    (j : Fin m') : refine r a μ' hm j = Poly.modMonic (μ' j) (a ⟨j / r, div_lt hm j.isLt⟩) :=
  apply_ofFn ..

theorem refine_add (r : ℕ) (a b : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    refine r (a + b) μ' hm = refine r a μ' hm + refine r b μ' hm := by
  ext j
  simp [refine_apply, Poly.modMonic_add]

theorem refine_sub (r : ℕ) (a b : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    refine r (a - b) μ' hm = refine r a μ' hm - refine r b μ' hm := by
  ext j
  simp [refine_apply, Poly.modMonic_sub]

theorem refine_neg (r : ℕ) (a : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    refine r (-a) μ' hm = -refine r a μ' hm := by
  ext j
  simp [refine_apply, Poly.modMonic_neg]

theorem refine_zero (r : ℕ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    refine r (0 : Residues F d' m μ) μ' hm = 0 := by
  ext j
  simp [refine_apply, Poly.modMonic_zero]

theorem refine_one [NeZero d] [NeZero d'] (r : ℕ) (μ' : Fin m' → Poly F d) (hm : m' = m * r) :
    refine r (1 : Residues F d' m μ) μ' hm = 1 := by
  ext j
  rw [one_apply, refine_apply, one_apply, Poly.modMonic_one]

/-- The binomial layer is the refinement at the binomials. -/
theorem split_eq_refine {r : ℕ} [NeZero r] {γ : Fin m → F} (a : Residues.Binomial F d' m γ)
    (γ' : Fin m' → F) (hd : d' = r * d) (hm : m' = m * r) :
    split r a γ' hd hm = refine r a (fun j => Poly.binomial (γ' j)) hm := by
  ext j
  rw [split_apply, refine_apply, Poly.modMonic_binomial (r := r) _ _ hd]

/-- Layers compose when the second layer's components divide the first's. -/
theorem refine_refine {d'' m₁ m₂ : ℕ} {μ₀ : Fin m → Poly F d''} (r₁ r₂ : ℕ) (a : Residues F d'' m μ₀)
    (μ₁ : Fin m₁ → Poly F d') (μ₂ : Fin m₂ → Poly F d) (hm₁ : m₁ = m * r₁) (hm₂ : m₂ = m₁ * r₂)
    (h : LayerDvd r₂ μ₁ μ₂ hm₂) (hm : m₂ = m * (r₁ * r₂)) :
    refine r₂ (refine r₁ a μ₁ hm₁) μ₂ hm₂ = refine (r₁ * r₂) a μ₂ hm := by
  ext j
  rw [refine_apply, refine_apply, refine_apply, Poly.modMonic_modMonic _ (h j),
    show (⟨j / r₂ / r₁, div_lt hm₁ (div_lt hm₂ j.isLt)⟩ : Fin m) = ⟨j / (r₁ * r₂), div_lt hm j.isLt⟩
      from Fin.ext (show j / r₂ / r₁ = j / (r₁ * r₂) by rw [Nat.div_div_eq_div_mul, Nat.mul_comm])]

section Divisible

variable (r : ℕ) (a : Residues F d' m μ) (μ' : Fin m' → Poly F d) (hm : m' = m * r)
  (h : LayerDvd r μ μ' hm)

include h in
/-- Residue `j` of the layer is the image of residue `j / r` under the quotient map. -/
theorem refine_toR (j : Fin m') :
    (refine r a μ' hm).toR j = R.reduce (h j) (a.toR ⟨j / r, div_lt hm j.isLt⟩) := by
  rw [toR, toR, refine_apply, Poly.toR_modMonic, Poly.toR_eq_mk, R.reduce_mk]

include h in
theorem refine_mul (b : Residues F d' m μ) :
    refine r (a * b) μ' hm = refine r a μ' hm * refine r b μ' hm := by
  ext j
  rw [mul_apply, refine_apply, refine_apply, refine_apply, mul_apply, Poly.modMonic_mulMonic _ (h j)]

include h in
theorem refine_eq_iff_toR [Nontrivial F] (b : Residues F d m' μ') :
    refine r a μ' hm = b ↔ ∀ j, b.toR j = R.reduce (h j) (a.toR ⟨j / r, div_lt hm j.isLt⟩) := by
  rw [Residues.ext_iff]
  refine forall_congr' fun j => ?_
  rw [refine_apply, toR, toR, ← (Poly.toR_injective (μ' j)).eq_iff, Poly.toR_modMonic,
    Poly.toR_eq_mk (μ _), R.reduce_mk, eq_comm]

/-- Residue `j` of the layer is the residue whose representative differs from that of `a (j / r)`
by a multiple of `X^d + μ' j`. -/
theorem refine_eq_iff_dvd (b : Residues F d m' μ') :
    refine r a μ' hm = b ↔
      ∀ j, Poly.monicPoly (μ' j) ∣ (a ⟨j / r, div_lt hm j.isLt⟩).toPoly - (b j).toPoly := by
  rw [Residues.ext_iff]
  exact forall_congr' fun j => by rw [refine_apply, Poly.modMonic_eq_iff_dvd]

end Divisible

end Residues

end Wychelean.Utils.PolyRing
