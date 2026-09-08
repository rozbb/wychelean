import Wychelean.DH.X25519.Basic
import Wychelean.DH.X25519.WeierstrassScaling

open WeierstrassCurve

/-!
# Independence of the Curve25519 twisting parameter

`scalarMulGeneric` takes the nonresidue `d` to twist by as a parameter. This module proves the
choice is immaterial:
* `scalarMulGeneric_indep_d`, any two nonresidues compute the same function
* `x25519_eq`, so in particular `x25519`, which twists by 2, is `scalarMulGeneric` for every
  nonresidue

This is Theorem 2.1 of Bernstein's Curve25519 paper (proved in its Appendix A): for `E: y² = x³ +
Ax² + x` over `Fₚ` and `X₀: E(Fₚ²) → Fₚ²` the u-coordinate map, given `n` and `q ∈ Fₚ` there is a
*unique* `s ∈ Fₚ` with `X₀(nQ) = s` for every `Q ∈ E(Fₚ²)` with `X₀(Q) = q`. The paper puts the
curve and all of its twists inside `E(Fₚ²)` at once, so the choice of twist never appears; here the
twists are instead parametrised by the nonresidue `d`, and the corresponding statement is that
`scalarMulGeneric d hd` does not depend on `d`.

The mechanism is the isomorphism of `Wychelean.DH.X25519.WeierstrassScaling`. Writing
`d' = s²d` — any two nonresidues differ by a square — the map `(x, y) ↦ (s²x, s³y)` is a group
isomorphism from the twist by `d` to the twist by `d'`. It scales the Weierstrass X-coordinate by `s²`, which is exactly
the factor undone by dividing by `d` versus `d'` at the end, so the u-coordinate of `n·P` comes out
the same either way. The remaining slack, that `mkTwistPoint` may pick the other square root on one
twist than on the other, costs nothing: the two candidate points differ by a sign, and negation
leaves the u-coordinate alone.
-/

namespace X25519

-- Any two nonresidues differ by a square: the Legendre symbol is multiplicative, so d'/d has
-- symbol (-1)(-1) = 1
theorem exists_sq_mul_of_not_square {d d': BaseField} (hd: ¬ IsSquare d) (hd': ¬ IsSquare d'):
    ∃ s: BaseField, s ≠ 0 ∧ d' = s ^ 2 * d := by
  have hd0: d ≠ 0 := ne_zero_of_not_square hd
  have hd0': d' ≠ 0 := ne_zero_of_not_square hd'
  have hsq: IsSquare (d' * d⁻¹) := by
    rw [ZMod.euler_criterion p (mul_ne_zero hd0' (inv_ne_zero hd0)), mul_pow, inv_pow,
      euler_neg_one hd0 hd, euler_neg_one hd0' hd']
    norm_num
  obtain ⟨s, hs⟩ := hsq
  have hs0: s ≠ 0 := by
    rintro rfl
    exact hd0' (by simpa [hd0] using hs)
  exact ⟨s, hs0, by field_simp at hs; linear_combination hs⟩

-- The twist by d' is the twist by d scaled by s, whenever d' = s²d
theorem twist_scalesTo {d d' s: BaseField} (hs: s ≠ 0) (hdd: d' = s ^ 2 * d):
    ScalesTo (Twist d) (Twist d') s where
  ne_zero := hs
  a₁ := by simp [Twist]
  a₂ := by simp only [Twist, hdd]; ring
  a₃ := by simp [Twist]
  a₄ := by simp only [Twist, hdd]; ring
  a₆ := by simp [Twist]

-- Negation fixes the u-coordinate, since it only flips the sign of Y
theorem uCoord_neg {W: WeierstrassCurve BaseField} (P: W.toAffine.Point):
    uCoord (-P) = uCoord P := by
  cases P <;> rfl

-- Scaling multiplies the u-coordinate by s², at infinity as well as at affine points
theorem uCoord_scale {W W': WeierstrassCurve BaseField} {s: BaseField} (h: ScalesTo W W' s)
    (P: W.toAffine.Point): uCoord (scale h P) = s ^ 2 * uCoord P := by
  cases P with
  | zero => exact (mul_zero _).symm
  | some x y hP => rfl

-- If the twist point for u exists then `sqrtCandidate` really did return a square root there
theorem sqrtCandidate_twistRhs_sq {d: BaseField} (hd: d ≠ 0) {u: BaseField}
    (h: (mkTwistPoint d hd u).isSome):
    sqrtCandidate (twistRhs d (d * u)) ^ 2 = twistRhs d (d * u) := by
  by_contra hc
  simp only [mkTwistPoint, dite_eq_right hc, Option.isSome_none, Bool.false_eq_true] at h

theorem mkTwistPoint_eq_some {d: BaseField} (hd: d ≠ 0) {u: BaseField}
    (hy: sqrtCandidate (twistRhs d (d * u)) ^ 2 = twistRhs d (d * u)):
    mkTwistPoint d hd u
      = some (.some (d * u) (sqrtCandidate (twistRhs d (d * u))) (mem_twist hd hy)) := by
  simp only [mkTwistPoint, dite_eq_left hy]

-- The twist point for u, as an explicit pair of coordinates
theorem mkTwistPoint_get {d: BaseField} (hd: d ≠ 0) {u: BaseField}
    (h: (mkTwistPoint d hd u).isSome):
    (mkTwistPoint d hd u).get h
      = .some (d * u) (sqrtCandidate (twistRhs d (d * u)))
          (mem_twist hd (sqrtCandidate_twistRhs_sq hd h)) :=
  Option.get_of_eq_some h (mkTwistPoint_eq_some hd (sqrtCandidate_twistRhs_sq hd h))

-- The heart of the matter: multiplying the twist point for u by n and undoing the map X ↦ dX
-- gives a u-coordinate that does not depend on which nonresidue was used to twist by
theorem uCoord_nsmul_mkTwistPoint_div {d d' u: BaseField} (hd: ¬ IsSquare d) (hd': ¬ IsSquare d')
    (n: ℕ) (h: (mkTwistPoint d (ne_zero_of_not_square hd) u).isSome)
    (h': (mkTwistPoint d' (ne_zero_of_not_square hd') u).isSome):
    uCoord (n • (mkTwistPoint d (ne_zero_of_not_square hd) u).get h) / d
      = uCoord (n • (mkTwistPoint d' (ne_zero_of_not_square hd') u).get h') / d' := by
  have hd0: d ≠ 0 := ne_zero_of_not_square hd
  obtain ⟨s, hs, hdd⟩ := exists_sq_mul_of_not_square hd hd'
  have hscale := twist_scalesTo hs hdd
  -- Both points sit over the same u, so the scaled one and the one on the twist by d' agree up
  -- to the sign of their Y-coordinate
  rw [mkTwistPoint_get, mkTwistPoint_get]
  set P := (Affine.Point.some (d * u) (sqrtCandidate (twistRhs d (d * u)))
    (mem_twist hd0 (sqrtCandidate_twistRhs_sq hd0 h)): (Twist d).toAffine.Point)
  have hx: d' * u = s ^ 2 * (d * u) := by rw [hdd]; ring
  have hQ := (Affine.Point.X_eq_iff (h₁ := mem_twist (ne_zero_of_not_square hd')
    (sqrtCandidate_twistRhs_sq (ne_zero_of_not_square hd') h'))
    (h₂ := nonsingular_scale hscale (mem_twist hd0
      (sqrtCandidate_twistRhs_sq hd0 h)))).mp hx
  -- In either case the u-coordinate of n·Q is s² times that of n·P
  have key: ∀ Q: (Twist d').toAffine.Point, Q = scale hscale P ∨
      Q = -scale hscale P → uCoord (n • Q) = s ^ 2 * uCoord (n • P) := by
    rintro Q (rfl | rfl)
    · rw [← map_nsmul, uCoord_scale]
    · rw [neg_nsmul, uCoord_neg, ← map_nsmul, uCoord_scale]
  rw [key _ hQ, hdd, mul_div_mul_left _ _ (pow_ne_zero 2 hs)]

/-- `scalarMulGeneric` does not depend on the nonresidue it twists by: any two choices of `d`
compute the same function. -/
theorem scalarMulGeneric_indep_d {d d': BaseField} (hd: ¬ IsSquare d) (hd': ¬ IsSquare d')
    (scalar point: Vector UInt8 32):
    scalarMulGeneric d hd scalar point = scalarMulGeneric d' hd' scalar point := by
  unfold scalarMulGeneric
  refine congrArg encodeUCoordinate ?_
  by_cases hc: (mkCurvePoint (decodeUCoordinate point: BaseField)).isSome
  · simp only [dite_eq_left hc]
  · simp only [dite_eq_right hc]
    exact uCoord_nsmul_mkTwistPoint_div hd hd' _ _ _

/-- In particular `x25519`, which twists by 2, is `scalarMulGeneric` for every nonresidue. -/
theorem x25519_eq {d: BaseField} (hd: ¬ IsSquare d) (scalar point: Vector UInt8 32):
    x25519 scalar point = scalarMulGeneric d hd scalar point :=
  scalarMulGeneric_indep_d two_not_square hd scalar point

end X25519
