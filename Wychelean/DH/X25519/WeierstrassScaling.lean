import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Scaling isomorphisms between Weierstrass curves

This file is used by `Wychelean.DH.X25519.TwistIndependence`.

Two Weierstrass curves whose coefficients are related by `aᵢ' = sⁱ·aᵢ` for a nonzero `s` are
isomorphic: the map `(x, y) ↦ (s²x, s³y)` carries the affine points of one onto the affine points
of the other, and respects the group law. This is the variable change
`⟨u, r, s, t⟩ = ⟨s⁻¹, 0, 0, 0⟩` of `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`, but
phrased as a *relation* between two curves rather than as an operation producing one, so that
nothing has to be transported along an equality of curves.

Key definitions:
* `X25519.ScalesTo`, the relation `aᵢ' = sⁱ·aᵢ`
* `X25519.scale`, the induced group homomorphism, an isomorphism with inverse the scaling
  by `s⁻¹`

The lemmas here mirror the ones Mathlib proves for the map induced by a ring homomorphism
(`WeierstrassCurve.Affine.map_negY` and friends): each of `negY`, `slope`, `addX`, `negAddY` and
`addY` is homogeneous of the evident weight, and the group homomorphism is read off from that.
-/

namespace X25519

open WeierstrassCurve WeierstrassCurve.Affine

variable {F: Type*} [Field F] {W W': WeierstrassCurve F} {s: F}

/-- `ScalesTo W W' s` says that the coefficients of `W'` are those of `W` scaled by powers of a
nonzero `s`, i.e. that `W'` is the image of `W` under the variable change `(X, Y) ↦ (s²X, s³Y)`.

Note this is a genuine constraint on the pair of curves: for a given `W` and `s`, it determines `W'`
completely. -/
structure ScalesTo (W W': WeierstrassCurve F) (s: F): Prop where
  ne_zero: s ≠ 0
  a₁: W'.a₁ = s * W.a₁
  a₂: W'.a₂ = s ^ 2 * W.a₂
  a₃: W'.a₃ = s ^ 3 * W.a₃
  a₄: W'.a₄ = s ^ 4 * W.a₄
  a₆: W'.a₆ = s ^ 6 * W.a₆

/-- Scaling by `s` is invertible: it is undone by scaling by `s⁻¹`. -/
theorem ScalesTo.symm (h: ScalesTo W W' s): ScalesTo W' W s⁻¹ where
  ne_zero := inv_ne_zero h.ne_zero
  a₁ := by rw [h.a₁]; field_simp [h.ne_zero]
  a₂ := by rw [h.a₂]; field_simp [h.ne_zero]
  a₃ := by rw [h.a₃]; field_simp [h.ne_zero]
  a₄ := by rw [h.a₄]; field_simp [h.ne_zero]
  a₆ := by rw [h.a₆]; field_simp [h.ne_zero]

/-! ## The scaled point, and the curve equation -/

-- The scaled Weierstrass polynomial is s⁶ times the original, so the equation is preserved
theorem equation_scale (h: ScalesTo W W' s) {x y: F} (hxy: W.toAffine.Equation x y):
    W'.toAffine.Equation (s ^ 2 * x) (s ^ 3 * y) := by
  rw [equation_iff] at hxy ⊢
  simp only [h.a₁, h.a₂, h.a₃, h.a₄, h.a₆]
  linear_combination (s ^ 6) * hxy

-- The two partial derivatives scale by s⁴ and s³ respectively, so neither can newly vanish
theorem nonsingular_scale (h: ScalesTo W W' s) {x y: F} (hxy: W.toAffine.Nonsingular x y):
    W'.toAffine.Nonsingular (s ^ 2 * x) (s ^ 3 * y) := by
  have hs := h.ne_zero
  rw [nonsingular_iff'] at hxy ⊢
  refine ⟨equation_scale h hxy.1, ?_⟩
  rcases hxy.2 with hX | hY
  · refine Or.inl ?_
    rw [show W'.a₁ * (s ^ 3 * y) - (3 * (s ^ 2 * x) ^ 2 + 2 * W'.a₂ * (s ^ 2 * x) + W'.a₄)
        = s ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) by
      simp only [h.a₁, h.a₂, h.a₄]; ring]
    exact mul_ne_zero (pow_ne_zero 4 hs) hX
  · refine Or.inr ?_
    rw [show 2 * (s ^ 3 * y) + W'.a₁ * (s ^ 2 * x) + W'.a₃ = s ^ 3 * (2 * y + W.a₁ * x + W.a₃) by
      simp only [h.a₁, h.a₃]; ring]
    exact mul_ne_zero (pow_ne_zero 3 hs) hY

/-! ## The negation and addition formulae are homogeneous -/

theorem negY_scale (h: ScalesTo W W' s) (x y: F):
    W'.toAffine.negY (s ^ 2 * x) (s ^ 3 * y) = s ^ 3 * W.toAffine.negY x y := by
  simp only [negY, h.a₁, h.a₃]
  ring

-- Both slope formulae are a ratio of an s^(n+1)-homogeneous term by an s^n-homogeneous one
private theorem div_scale (hs: s ≠ 0) (n: ℕ) (a b: F):
    s ^ (n + 1) * a / (s ^ n * b) = s * (a / b) := by
  rw [show s ^ (n + 1) * a = s ^ n * (s * a) by ring, mul_div_mul_left _ _ (pow_ne_zero n hs),
    mul_div_assoc]

theorem slope_scale [DecidableEq F] (h: ScalesTo W W' s) (x₁ x₂ y₁ y₂: F):
    W'.toAffine.slope (s ^ 2 * x₁) (s ^ 2 * x₂) (s ^ 3 * y₁) (s ^ 3 * y₂)
      = s * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hs := h.ne_zero
  by_cases hx: x₁ = x₂
  · by_cases hy: y₁ = W.toAffine.negY x₂ y₂
    · rw [slope_of_Y_eq (by rw [hx]) (by rw [negY_scale h, hy]), slope_of_Y_eq hx hy, mul_zero]
    · have hy': s ^ 3 * y₁ ≠ W'.toAffine.negY (s ^ 2 * x₂) (s ^ 3 * y₂) := by
        rw [negY_scale h]
        exact fun hc => hy (mul_left_cancel₀ (pow_ne_zero 3 hs) hc)
      rw [slope_of_Y_ne (by rw [hx]) hy', slope_of_Y_ne hx hy, negY_scale h,
        show 3 * (s ^ 2 * x₁) ^ 2 + 2 * W'.a₂ * (s ^ 2 * x₁) + W'.a₄ - W'.a₁ * (s ^ 3 * y₁)
          = s ^ 4 * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) by
          simp only [h.a₁, h.a₂, h.a₄]; ring,
        show s ^ 3 * y₁ - s ^ 3 * W.toAffine.negY x₁ y₁ = s ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) by
          ring]
      exact div_scale hs 3 _ _
  · rw [slope_of_X_ne (fun hc => hx (mul_left_cancel₀ (pow_ne_zero 2 hs) hc)), slope_of_X_ne hx,
      show s ^ 3 * y₁ - s ^ 3 * y₂ = s ^ 3 * (y₁ - y₂) by ring,
      show s ^ 2 * x₁ - s ^ 2 * x₂ = s ^ 2 * (x₁ - x₂) by ring]
    exact div_scale hs 2 _ _

theorem addX_scale (h: ScalesTo W W' s) (x₁ x₂ ℓ: F):
    W'.toAffine.addX (s ^ 2 * x₁) (s ^ 2 * x₂) (s * ℓ) = s ^ 2 * W.toAffine.addX x₁ x₂ ℓ := by
  simp only [addX, h.a₁, h.a₂]
  ring

theorem negAddY_scale (h: ScalesTo W W' s) (x₁ x₂ y₁ ℓ: F):
    W'.toAffine.negAddY (s ^ 2 * x₁) (s ^ 2 * x₂) (s ^ 3 * y₁) (s * ℓ)
      = s ^ 3 * W.toAffine.negAddY x₁ x₂ y₁ ℓ := by
  simp only [negAddY, addX_scale h]
  ring

theorem addY_scale (h: ScalesTo W W' s) (x₁ x₂ y₁ ℓ: F):
    W'.toAffine.addY (s ^ 2 * x₁) (s ^ 2 * x₂) (s ^ 3 * y₁) (s * ℓ)
      = s ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ := by
  rw [addY, addX_scale h, negAddY_scale h, negY_scale h, addY]

/-! ## The induced group homomorphism -/

/-- The underlying function of `scale`: `(x, y) ↦ (s²x, s³y)`, and `0 ↦ 0`. -/
def scaleFun (h: ScalesTo W W' s): W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some _ _ hP => .some _ _ (nonsingular_scale h hP)

@[simp]
theorem scaleFun_zero (h: ScalesTo W W' s): scaleFun h (0: W.toAffine.Point) = 0 := rfl

@[simp]
theorem scaleFun_some (h: ScalesTo W W' s) {x y: F} (hP: W.toAffine.Nonsingular x y):
    scaleFun h (.some x y hP) = .some (s ^ 2 * x) (s ^ 3 * y) (nonsingular_scale h hP) := rfl

variable [DecidableEq F]

/-- The group homomorphism on nonsingular affine points induced by `ScalesTo W W' s`, namely
`(x, y) ↦ (s²x, s³y)`. It is an isomorphism: `scale_scale` composes it with the scaling by
`s⁻¹`, `ScalesTo.symm`, to get the identity. -/
def scale (h: ScalesTo W W' s): W.toAffine.Point →+ W'.toAffine.Point where
  toFun := scaleFun h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy: x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, scaleFun_some h h₁, scaleFun_some h h₂,
        Point.add_of_Y_eq (show s ^ 2 * x₁ = s ^ 2 * x₂ by rw [hxy.1])
          (show s ^ 3 * y₁ = W'.toAffine.negY (s ^ 2 * x₂) (s ^ 3 * y₂) by
            rw [negY_scale h, hxy.2])]
      rfl
    · have hxy': ¬(s ^ 2 * x₁ = s ^ 2 * x₂ ∧
          s ^ 3 * y₁ = W'.toAffine.negY (s ^ 2 * x₂) (s ^ 3 * y₂)) := by
        rw [negY_scale h]
        exact fun hc => hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 h.ne_zero) hc.1,
          mul_left_cancel₀ (pow_ne_zero 3 h.ne_zero) hc.2⟩
      rw [Point.add_some hxy]
      simp only [scaleFun_some]
      rw [Point.add_some hxy', Point.some.injEq, slope_scale h, addX_scale h, addY_scale h]
      exact ⟨rfl, rfl⟩

@[simp]
theorem scale_zero (h: ScalesTo W W' s): scale h 0 = 0 := rfl

@[simp]
theorem scale_some (h: ScalesTo W W' s) {x y: F} (hP: W.toAffine.Nonsingular x y):
    scale h (.some x y hP) = .some (s ^ 2 * x) (s ^ 3 * y) (nonsingular_scale h hP) := rfl

-- Scaling by s and then by s⁻¹ is the identity, so `scale` is an isomorphism onto `W'.Point`
theorem scale_scale (h: ScalesTo W W' s) (P: W.toAffine.Point): scale h.symm (scale h P) = P := by
  have hs := h.ne_zero
  cases P with
  | zero => rfl
  | some x y hP => rw [scale_some, scale_some, Point.some.injEq]; constructor <;> field_simp

end X25519
