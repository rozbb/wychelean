import Wychelean.KEM.MLKEM.Properties.Loops
import Wychelean.KEM.MLKEM.Properties.Ring

/-!
# `T_q` as a ring

The coefficient array of `f̂ ∈ T_q` read as its 128 residues modulo `X² - ζ^(2·BitRev₇(i)+1)`
(FIPS 203 Eq. 4.12–4.13), and the ring structure of `T_q` transported from that product ring.
-/

namespace Wychelean.KEM.MLKEM

open Utils.PolyRing

abbrev AbstractTq := Residues.Binomial Zq 2 128 (Utils.PolyRing.NTT.points ζ 7)

namespace Tq

/-- The residue `f̂[2i] + f̂[2i+1]·X` modulo `X² - ζ^(2·BitRev₇(i)+1)` (Eq. 4.13). -/
def component (a : Tq) (i : Fin 128) : Poly Zq 2 :=
  Poly.ofFn fun r => a[r.val + 2 * i.val]'(by omega)

instance : CoeFun Tq (fun _ => Fin 128 → Poly Zq 2) := ⟨component⟩

instance : One Tq := ⟨⟨Vector.ofFn fun i => if i.val % 2 = 0 then 1 else 0⟩⟩
instance : SMul Zq Tq := ⟨fun c a => ⟨a.coeffs.map (c * ·)⟩⟩

/-- Interpret adjacent coefficients as the ordered quadratic residues. -/
def toAbstract (a : Tq) : AbstractTq := Residues.ofFlat a.coeffs

def ofAbstract (a : AbstractTq) : Tq := ⟨a.flatten⟩

@[simp] theorem toAbstract_apply (a : Tq) (i : Fin 128) : toAbstract a i = a i := by
  change Residues.ofFn _ i = component a i
  rw [Residues.apply_ofFn]
  rfl

@[simp] theorem ofAbstract_toAbstract (a : Tq) : ofAbstract (toAbstract a) = a := by
  cases a
  simp [ofAbstract, toAbstract]

@[simp] theorem toAbstract_ofAbstract (a : AbstractTq) : toAbstract (ofAbstract a) = a :=
  Residues.ofFlat_flatten a

theorem toAbstract_injective : Function.Injective toAbstract :=
  Function.LeftInverse.injective ofAbstract_toAbstract

def abstractEquiv : Tq ≃ AbstractTq where
  toFun := toAbstract
  invFun := ofAbstract
  left_inv := ofAbstract_toAbstract
  right_inv := toAbstract_ofAbstract

@[simp] theorem component_getElem (a : Tq) (i : Fin 128) (j : ℕ) (hj : j < 2) :
    (a i)[j] = a[j + 2 * i.val]'(by omega) := Poly.getElem_ofFn ..

@[simp] theorem getElem_zero (j : ℕ) (hj : j < 256) : (0 : Tq)[j] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_one (j : ℕ) (hj : j < 256) :
    (1 : Tq)[j] = if j % 2 = 0 then 1 else 0 := Vector.getElem_ofFn ..

@[simp] theorem getElem_add (a b : Tq) (j : ℕ) (hj : j < 256) :
    (a + b)[j] = a[j] + b[j] := Vector.getElem_zipWith ..

@[simp] theorem getElem_sub (a b : Tq) (j : ℕ) (hj : j < 256) :
    (a - b)[j] = a[j] - b[j] := Vector.getElem_zipWith ..

@[simp] theorem getElem_neg (a : Tq) (j : ℕ) (hj : j < 256) :
    (-a)[j] = -a[j] := Vector.getElem_map ..

@[simp] theorem getElem_smul (c : Zq) (a : Tq) (j : ℕ) (hj : j < 256) :
    (c • a)[j] = c * a[j] := Vector.getElem_map ..

@[simp] theorem toAbstract_zero : toAbstract 0 = 0 := by
  ext i j hj
  simp

@[simp] theorem toAbstract_one : toAbstract 1 = 1 := by
  ext i j hj
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

@[simp] theorem toAbstract_add (a b : Tq) : toAbstract (a + b) = toAbstract a + toAbstract b := by
  ext i j hj
  simp

@[simp] theorem toAbstract_sub (a b : Tq) : toAbstract (a - b) = toAbstract a - toAbstract b := by
  ext i j hj
  simp

@[simp] theorem toAbstract_neg (a : Tq) : toAbstract (-a) = -toAbstract a := by
  ext i j hj
  simp

@[simp] theorem toAbstract_smul (c : Zq) (a : Tq) : toAbstract (c • a) = c • toAbstract a := by
  ext i j hj
  simp [mul_comm]

/-- Algorithms 11–12 agree with multiplication modulo each quadratic binomial. -/
@[simp] theorem toAbstract_mul (a b : Tq) : toAbstract (a * b) = toAbstract a * toAbstract b := by
  rw [mul_eq_multiply]
  apply Residues.ext
  intro i
  rw [Residues.mul_two]
  apply Poly.ext
  intro j hj
  rw [toAbstract_apply, component_getElem]
  change ((Vector.ofFn fun i : Fin 128 =>
    MLKEM.NTT.baseCaseMultiply a[2 * i.val] a[2 * i.val + 1]
      b[2 * i.val] b[2 * i.val + 1] (ζ ^ (2 * bitRev 7 i.val + 1))).flatten)[j + 2 * i.val] = _
  rw [Vector.getElem_flatten, Vector.getElem_ofFn]
  have hdiv : (j + 2 * i.val) / 2 = i.val := by omega
  have hmod : (j + 2 * i.val) % 2 = j := by omega
  simp only [hdiv, hmod, toAbstract_apply, component_getElem]
  interval_cases j <;> simp [MLKEM.NTT.baseCaseMultiply, Nat.add_comm,
    Poly.getElem_mk, Utils.PolyRing.NTT.points, Utils.PolyRing.NTT.point]

local macro "abstract_law" : tactic =>
  `(tactic| (apply toAbstract_injective
             simp only [toAbstract_add, toAbstract_mul, toAbstract_sub,
               toAbstract_neg, toAbstract_zero, toAbstract_one]
             ring))

/-- The ring laws transported along the coefficient interpretation; all operations stay concrete. -/
instance : CommRing Tq where
  add_assoc _ _ _ := by abstract_law
  zero_add _ := by abstract_law
  add_zero _ := by abstract_law
  add_comm _ _ := by abstract_law
  neg_add_cancel _ := by abstract_law
  sub_eq_add_neg _ _ := by abstract_law
  left_distrib _ _ _ := by abstract_law
  right_distrib _ _ _ := by abstract_law
  zero_mul _ := by abstract_law
  mul_zero _ := by abstract_law
  mul_assoc _ _ _ := by abstract_law
  one_mul _ := by abstract_law
  mul_one _ := by abstract_law
  mul_comm _ _ := by abstract_law
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The concrete coefficient ring and the abstract ordered product of quadratic quotients. -/
def abstractRingEquiv : Tq ≃+* AbstractTq where
  __ := abstractEquiv
  map_add' := toAbstract_add
  map_mul' := toAbstract_mul


end Tq

end Wychelean.KEM.MLKEM
