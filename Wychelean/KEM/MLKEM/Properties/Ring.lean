import Wychelean.KEM.MLKEM.NTT
import Wychelean.Utils.PolyRing.NTT

/-!
# `R_q` as a ring

The specification represents `f ∈ R_q` by its coefficient array and never multiplies in `R_q`
(FIPS 203 §2.4.5). For the proofs, `Polynomial` is identified with `ℤ_q[X]/(X^256 + 1)` of
`Wychelean.Utils.PolyRing`, whose product is the negacyclic convolution, and `ζ` with a
primitive 256-th root of unity.
-/

namespace Wychelean.KEM.MLKEM

open Utils.PolyRing

/-- ζ = 17 is a primitive 256-th root of unity, from `ζ^128 = -1` (§4.3). -/
def ζRoot : PrimitiveRoot Zq (2 ^ 8) :=
  PrimitiveRoot.ofPowEqNegOne ζ (by decide +kernel) (by decide)

@[simp] theorem ζRoot_val : ζRoot.val = ζ := rfl

instance : Fact (2 ^ 7 ∣ 256) := ⟨by decide⟩

namespace Polynomial

/-- The element of `ℤ_q[X]/(X^256 + 1)` with the coefficients of `f`. -/
def toPolyMod (f : Polynomial) : PolyMod Zq 256 (-1) := PolyMod.ofCoeffs f.coeffs

def ofPolyMod (a : PolyMod Zq 256 (-1)) : Polynomial := ⟨a.coeffs⟩

@[simp] theorem getElem_toPolyMod (f : Polynomial) (i : ℕ) (hi : i < 256) :
    f.toPolyMod[i] = f[i] := rfl

@[simp] theorem getElem_ofPolyMod (a : PolyMod Zq 256 (-1)) (i : ℕ) (hi : i < 256) :
    (ofPolyMod a)[i] = a[i] := rfl

@[simp] theorem coeffs_toPolyMod (f : Polynomial) : f.toPolyMod.coeffs = f.coeffs := rfl

@[simp] theorem ofPolyMod_toPolyMod (f : Polynomial) : ofPolyMod f.toPolyMod = f := rfl

@[simp] theorem toPolyMod_ofPolyMod (a : PolyMod Zq 256 (-1)) : (ofPolyMod a).toPolyMod = a :=
  PolyQuot.ext fun _ _ => rfl

theorem toPolyMod_injective : Function.Injective toPolyMod :=
  Function.LeftInverse.injective ofPolyMod_toPolyMod

@[simp] theorem getElem_zero (i : ℕ) (hi : i < 256) : (0 : Polynomial)[i] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_add (f g : Polynomial) (i : ℕ) (hi : i < 256) :
    (f + g)[i] = f[i] + g[i] := Vector.getElem_zipWith ..

@[simp] theorem getElem_sub (f g : Polynomial) (i : ℕ) (hi : i < 256) :
    (f - g)[i] = f[i] - g[i] := Vector.getElem_zipWith ..

@[simp] theorem getElem_neg (f : Polynomial) (i : ℕ) (hi : i < 256) :
    (-f)[i] = -f[i] := Vector.getElem_map ..

/-- The product of `R_q`, used only to state the properties of the transform. -/
instance : Mul Polynomial := ⟨fun f g => ofPolyMod (f.toPolyMod * g.toPolyMod)⟩
instance : One Polynomial := ⟨ofPolyMod 1⟩
instance : SMul Zq Polynomial := ⟨fun c f => ofPolyMod (c • f.toPolyMod)⟩

@[simp] theorem toPolyMod_zero : (0 : Polynomial).toPolyMod = 0 := by
  ext i hi; simp
@[simp] theorem toPolyMod_one : (1 : Polynomial).toPolyMod = 1 := toPolyMod_ofPolyMod 1
@[simp] theorem toPolyMod_add (f g : Polynomial) :
    (f + g).toPolyMod = f.toPolyMod + g.toPolyMod := by
  ext i hi; simp
@[simp] theorem toPolyMod_sub (f g : Polynomial) :
    (f - g).toPolyMod = f.toPolyMod - g.toPolyMod := by
  ext i hi; simp
@[simp] theorem toPolyMod_neg (f : Polynomial) : (-f).toPolyMod = -f.toPolyMod := by
  ext i hi; simp
@[simp] theorem toPolyMod_mul (f g : Polynomial) :
    (f * g).toPolyMod = f.toPolyMod * g.toPolyMod := toPolyMod_ofPolyMod _
@[simp] theorem toPolyMod_smul (c : Zq) (f : Polynomial) :
    (c • f).toPolyMod = c • f.toPolyMod := toPolyMod_ofPolyMod _

local macro "transport_law" : tactic =>
  `(tactic| (apply toPolyMod_injective
             simp only [toPolyMod_add, toPolyMod_mul, toPolyMod_sub,
               toPolyMod_neg, toPolyMod_zero, toPolyMod_one]
             ring))

/-- The ring laws transported along the coefficient identification. -/
instance : CommRing Polynomial where
  add_assoc _ _ _ := by transport_law
  zero_add _ := by transport_law
  add_zero _ := by transport_law
  add_comm _ _ := by transport_law
  neg_add_cancel _ := by transport_law
  sub_eq_add_neg _ _ := by transport_law
  left_distrib _ _ _ := by transport_law
  right_distrib _ _ _ := by transport_law
  zero_mul _ := by transport_law
  mul_zero _ := by transport_law
  mul_assoc _ _ _ := by transport_law
  one_mul _ := by transport_law
  mul_one _ := by transport_law
  mul_comm _ _ := by transport_law
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The coefficient arrays of `R_q` and PolyRing's quotient ring. -/
def ringEquiv : Polynomial ≃+* PolyMod Zq 256 (-1) where
  toFun := toPolyMod
  invFun := ofPolyMod
  left_inv := ofPolyMod_toPolyMod
  right_inv := toPolyMod_ofPolyMod
  map_mul' := toPolyMod_mul
  map_add' := toPolyMod_add

end Polynomial

end Wychelean.KEM.MLKEM
