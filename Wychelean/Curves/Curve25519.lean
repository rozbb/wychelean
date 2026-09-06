import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Wychelean.Curves.Prime25519

open WeierstrassCurve

-- Field modulus and basepoint order from
--   https://www.rfc-editor.org/rfc/rfc7748.html#section-4.1
def p: Nat := 2^255 - 19
def basepointOrder: Nat := 2^252 + 0x14def9dea2f79cd65812631a5cf5d3ed
abbrev BaseField := ZMod p
abbrev ScalarField := ZMod basepointOrder

-- BaseField is a field because p is a prime
instance fact_prime_p: Fact (Nat.Prime p) := ⟨prime_two_pow_255_sub_19⟩
example: Field BaseField := inferInstance

-- Curve25519: Y² = x³ + 486662X² + X over BaseField
-- Mathlib Weierstrass equation: Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆
def Curve: WeierstrassCurve BaseField := {
    a₁ := 0,
    a₂ := 486662,
    a₃ := 0,
    a₄ := 1,
    a₆ := 0
}

-- Prove the curve is indeed an elliptic curve (i.e., nonsingular)
instance: Curve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simp only [Curve, Δ, b₂, b₄, b₆, b₈]
    decide

-- Base point coordinates from
--   https://www.rfc-editor.org/rfc/rfc7748.html#section-4.1
def BasePointU: BaseField := 9
def BasePointV: BaseField :=
  14781619447589544791020593568409986887264606134616475288964881837755586237401

-- Since `Curve` is elliptic, lying on the curve already implies nonsingularity
private theorem basePoint_nonsingular: Curve.toAffine.Nonsingular BasePointU BasePointV :=
  Affine.equation_iff_nonsingular.mp <| by
    rw [Affine.equation_iff']
    simp only [Curve, BasePointU, BasePointV]
    decide

def BasePoint: Curve.toAffine.Point :=
  Affine.Point.some BasePointU BasePointV basePoint_nonsingular

-- The parameter the curve is twisted by. It actually doesn't matter which d we use as long as it's
-- a nonresidue mod p
def d: BaseField := 2

-- d is a nonresidue mod p, so d·Y² = X³ + 486662X² + X is indeed a quadratic twist of Curve
set_option maxRecDepth 4000 in
private theorem d_not_square: ¬ IsSquare d := by
  rw [ZMod.euler_criterion p (by decide), pow_eq_binRec]
  decide

-- The quadratic twist d·Y² = X³ + 486662X² + X, put back into Weierstrass form by the invertible
-- map (X, Y) ↦ (X/d, Y/d²), which gives Y² = X³ + (d·486662)X² + d²X.
def Twist: WeierstrassCurve BaseField := {
    a₁ := 0,
    a₂ := d * 486662,
    a₃ := 0,
    a₄ := d ^ 2,
    a₆ := 0
}

-- The twist is elliptic too: its discriminant works out to d⁶ times that of `Curve`, so it is
-- nonzero for the same reason, and in a field that is the same as being a unit.
instance: Twist.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simp only [Twist, Δ, b₂, b₄, b₆, b₈, d]
    decide

example: AddCommGroup Twist.toAffine.Point := inferInstance

/-! ## Scalar decoding (RFC 7748 §5) -/

-- decodeLittleEndian from
--   https://www.rfc-editor.org/rfc/rfc7748.html#section-5
-- Except we read _all_ bytes
def decodeLittleEndian (bytes: List UInt8): Nat :=
  bytes.foldr (fun b acc => acc <<< 8 + b.toNat) 0

-- decodeScalar25519 from
--    https://www.rfc-editor.org/rfc/rfc7748.html#section-5
-- Clear the low 3 bits of the first byte, clear the top bit of the last byte and set the
-- second-highest, then decode little-endian.
def decodeScalar (k: Vector UInt8 32): Nat :=
  let low := k[0] &&& 0b1111_1000
  let high := (k[31] &&& 0b0111_1111) ||| 0b0100_0000
  let clamped := (k.set 0 low).set 31 high
  decodeLittleEndian clamped.toList

-- decodeUCoordinate
--    https://www.rfc-editor.org/rfc/rfc7748.html#section-5
-- With bits = 255 the only unused bit is the top one of the last byte, which is masked off before
-- decoding.
def decodeUCoordinate (u: Vector UInt8 32): Nat :=
  let masked := u.set 31 (u[31] &&& 0b0111_1111)
  decodeLittleEndian masked.toList

-- encodeUCoordinate from
--    https://www.rfc-editor.org/rfc/rfc7748.html#section-5
-- Encodes a u coordinate as little-endian bytes
def encodeUCoordinate (u: BaseField): Vector UInt8 32 :=
  Vector.ofFn fun i => UInt8.ofNat (u.val >>> (8 * i.val))

-- The two X25519 input scalars from RFC 7748 §5.2, against the decimal values given there
example: decodeScalar #v[165, 70, 227, 107, 240, 82, 124, 157, 59, 22, 21, 75, 130, 70, 94, 221,
    98, 20, 76, 10, 193, 252, 90, 24, 80, 106, 34, 68, 186, 68, 154, 196] =
    31029842492115040904895560451863089656472772604678260265531221036453811406496 := by decide

example: decodeScalar #v[75, 102, 233, 212, 209, 180, 103, 60, 90, 210, 38, 145, 149, 125, 106, 245,
    193, 27, 100, 33, 224, 234, 1, 212, 44, 164, 22, 158, 121, 24, 186, 13] =
    35156891815674817266734212754503633747128614016119564763269015315466259359304 := by decide

-- The first input u-coordinate from RFC 7748 §5.2
example: decodeUCoordinate #v[230, 219, 104, 103, 88, 48, 48, 219, 53, 148, 193, 164, 36, 177, 95,
    124, 114, 102, 36, 236, 38, 179, 53, 59, 16, 169, 3, 166, 208, 171, 28, 76] =
    34426434033919594451155107781188821651316167215306631574996226621102155684838 := by decide

/-! ## Scalar multiplication -/

-- Right-hand sides of the two curve equations, as decidable arithmetic in BaseField
def curveRhs (u: BaseField): BaseField := u ^ 3 + 486662 * u ^ 2 + u
def twistRhs (x: BaseField): BaseField := x ^ 3 + d * 486662 * x ^ 2 + d ^ 2 * x

-- Shows that (u, y) is a nonsingular point when they satisfy the curve equation
private theorem mem_curve {u y: BaseField} (h: y ^ 2 = curveRhs u):
    Curve.toAffine.Nonsingular u y :=
  Affine.equation_iff_nonsingular.mp <| by
    rw [Affine.equation_iff']
    simp only [Curve, curveRhs] at *
    linear_combination h

-- Shows that (x, y) is a nonsingular point when they satisfy the twist equation
private theorem mem_twist {x y: BaseField} (h: y ^ 2 = twistRhs x):
    Twist.toAffine.Nonsingular x y :=
  Affine.equation_iff_nonsingular.mp <| by
    rw [Affine.equation_iff']
    simp only [Twist, twistRhs] at *
    linear_combination h

-- p ≡ 5 mod 8, so a square root is one exponentiation, corrected by √-1 = 2^((p-1)/4) when needed
def sqrtCandidate (a: BaseField): BaseField :=
  let r := a ^ ((p + 3) / 8)
  if r ^ 2 = a then r else r * (2 : BaseField) ^ ((p - 1) / 4)

-- Construct the curve point with the given u, if it exists
def mkCurvePoint (u: BaseField): Option Curve.toAffine.Point :=
  let y := sqrtCandidate (curveRhs u)
  if h: y ^ 2 = curveRhs u then
    some (Affine.Point.some u y (mem_curve h))
  else none

-- Construct the twist point with the given u, if it exists
def mkTwistPoint (u: BaseField): Option Twist.toAffine.Point :=
  -- Do the invertible map X ↦ dX so we can operate over the Weierstrass form of the twist
  let x := d * u
  let y := sqrtCandidate (twistRhs x)
  if h: y ^ 2 = twistRhs x then
    some (Affine.Point.some x y (mem_twist h))
  else none

-- a^(p/2) is ±1 for nonzero a, since its square is a^(p-1) = 1
private theorem euler_pm {a: BaseField} (ha: a ≠ 0): a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  have h1: (a ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show p / 2 * 2 = p - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one ha
  have h2: (a ^ (p / 2) - 1) * (a ^ (p / 2) + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

private theorem euler_neg_one {a: BaseField} (ha: a ≠ 0) (h: ¬ IsSquare a):
    a ^ (p / 2) = -1 := by
  rcases euler_pm ha with h1 | h1
  · exact absurd ((ZMod.euler_criterion p ha).mpr h1) h
  · exact h1

-- 2^((p-1)/4) is a square root of -1, since 2 is a nonresidue
private theorem sqrtNegOne_sq: ((2 : BaseField) ^ ((p - 1) / 4)) ^ 2 = -1 := by
  rw [← pow_mul, show (p - 1) / 4 * 2 = p / 2 by decide]
  exact euler_neg_one (by decide) d_not_square

-- The p ≡ 5 mod 8 square root formula really does produce a square root, on squares
private theorem sqrtCandidate_sq {a: BaseField} (h: IsSquare a): sqrtCandidate a ^ 2 = a := by
  rw [sqrtCandidate]
  split
  · assumption
  · rename_i hr
    have ha: a ≠ 0 := by
      rintro rfl
      exact hr (by rw [zero_pow (by decide : (p + 3) / 8 ≠ 0)]; ring)
    have hr2: (a ^ ((p + 3) / 8)) ^ 2 = a * a ^ ((p - 1) / 4) := by
      rw [← pow_mul, show (p + 3) / 8 * 2 = (p - 1) / 4 + 1 by decide, pow_succ]
      ring
    have hsq: (a ^ ((p - 1) / 4)) ^ 2 = 1 := by
      rw [← pow_mul, show (p - 1) / 4 * 2 = p / 2 by decide]
      exact (ZMod.euler_criterion p ha).mp h
    have ht: a ^ ((p - 1) / 4) = 1 ∨ a ^ ((p - 1) / 4) = -1 := by
      have h2: (a ^ ((p - 1) / 4) - 1) * (a ^ ((p - 1) / 4) + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl (sub_eq_zero.mp h3)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
    rcases ht with h1 | h1
    · exact absurd (by rw [hr2, h1, mul_one]) hr
    · rw [mul_pow, hr2, h1, sqrtNegOne_sq]; ring

-- The twist's right-hand side at d*u is d³ times the curve's at u
private theorem twistRhs_eq (u: BaseField): twistRhs (d * u) = d ^ 3 * curveRhs u := by
  simp only [twistRhs, curveRhs]; ring

-- If u misses the curve then curveRhs u is a nonresidue, and so is d³, so their product is a square
private theorem isSquare_twistRhs {u: BaseField} (h: ¬ IsSquare (curveRhs u)):
    IsSquare (twistRhs (d * u)) := by
  have hd: (d : BaseField) ≠ 0 := by decide
  have hf: curveRhs u ≠ 0 := fun h0 => h (h0 ▸ ⟨0, by ring⟩)
  have hne: twistRhs (d * u) ≠ 0 := by
    rw [twistRhs_eq]; exact mul_ne_zero (pow_ne_zero 3 hd) hf
  rw [ZMod.euler_criterion p hne, twistRhs_eq, mul_pow, ← pow_mul, mul_comm 3 (p / 2), pow_mul,
    euler_neg_one hd d_not_square, euler_neg_one hf h]
  ring

private theorem mkCurvePoint_isSome {u: BaseField} (h: IsSquare (curveRhs u)):
    (mkCurvePoint u).isSome := by
  simp only [mkCurvePoint, sqrtCandidate_sq h, dite_true, Option.isSome_some]

private theorem mkTwistPoint_isSome {u: BaseField} (h: IsSquare (twistRhs (d * u))):
    (mkTwistPoint u).isSome := by
  simp only [mkTwistPoint, sqrtCandidate_sq h, dite_true, Option.isSome_some]

-- Every u-coordinate lies on the curve or on the twist, so `scalarMul` needs no fallback
private theorem mkTwistPoint_isSome_of_not_curve {u: BaseField} (h: ¬ (mkCurvePoint u).isSome):
    (mkTwistPoint u).isSome :=
  mkTwistPoint_isSome (isSquare_twistRhs (fun hs => h (mkCurvePoint_isSome hs)))

-- The point at infinity is given u-coordinate 0 in
--   https://www.rfc-editor.org/rfc/rfc7748.html#section-6.1
def uCoord {W: WeierstrassCurve BaseField} (P: W.toAffine.Point): BaseField :=
  match P with
  | .zero => 0
  | .some x _ _ => x

-- Multiplies a point, given by a 32-byte little-endian representation of its u-coordinate, by a
-- scalar, given by a 32-byte little-endian representation of the integer. If the point is on the
-- curve, then multiplication is done on the curve. If it's on the twist, then multiplication is
-- done on the twist. The output is the 32-byte little-endian representation of the resulting
-- u-coordinate. Note that, per the specification, scalars are _clamped_, meaning some bits are
-- set/cleared before parsing as an integer.
def scalarMul (point scalar: Vector UInt8 32): Vector UInt8 32 :=
  let u: BaseField := decodeUCoordinate point
  let n := decodeScalar scalar
  let outU := if h: (mkCurvePoint u).isSome then
    uCoord (n • (mkCurvePoint u).get h)
  else
    -- Undo the invertible map X ↦ dX to get the twist coordinate of the non-Weierstrass form
    uCoord (n • (mkTwistPoint u).get (mkTwistPoint_isSome_of_not_curve h)) / d

  encodeUCoordinate outU

-- Multiplies the Curve25519 basepoint by a scalar, given by a 32-byte little-endian
-- representation of the integer Note that, per the specification, scalars are _clamped_,
-- meaning some bits are set/cleared before parsing as an integer.
def basepointMul (scalar: Vector UInt8 32): Vector UInt8 32 :=
  scalarMul (encodeUCoordinate BasePointU) scalar

-- The §5.2 output u-coordinate, c3da5537…, as produced from the number `scalarMul` returns
example: encodeUCoordinate
    37325765543539916631701301279660700968428932651319597985674090122993663859395 =
    #v[195, 218, 85, 55, 157, 233, 198, 144, 142, 148, 234, 77, 242, 141, 8, 79,
       50, 236, 207, 3, 73, 28, 113, 247, 84, 180, 7, 85, 119, 162, 133, 82] := by decide

-- Decoding inverts encoding
example: decodeUCoordinate (encodeUCoordinate
    37325765543539916631701301279660700968428932651319597985674090122993663859395) =
    37325765543539916631701301279660700968428932651319597985674090122993663859395 := by decide
