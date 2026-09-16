import Wychelean.PolyRing.Quotient

/-!
The product ring `∏ᵢ F[X]/(X^d - γᵢ)`: a vector of polynomials of degree below `d`, one residue
per component ideal `(X^d - γᵢ)`. The components are the type index; the ring `F[X]/(X^n - c)`
itself is the one-component case `PolyMod F n c`.
-/

namespace Wychelean.PolyRing

/-- Residues modulo the components `X^d - γᵢ`: `a i` is the residue modulo `X^d - γ i`. -/
structure Residues (F : Type*) (d m : ℕ) (γ : Fin m → F) where
  entries : Vector (Poly F d) m
deriving DecidableEq

/-- The ring `F[X]/(X^n - c)` as the one-component product. -/
abbrev PolyMod (F : Type*) (n : ℕ) (c : F) := Residues F n 1 (fun _ => c)

namespace Residues

variable {F : Type*} {d m : ℕ} {γ : Fin m → F}

/-- Residue `i`, modulo `X^d - γ i`. -/
def residue (a : Residues F d m γ) (i : Fin m) : Poly F d := a.entries[i]

instance : CoeFun (Residues F d m γ) (fun _ => Fin m → Poly F d) := ⟨residue⟩

@[simp] theorem apply_mk (v : Vector (Poly F d) m) (i : Fin m) : (⟨v⟩ : Residues F d m γ) i = v[i] :=
  rfl

/-- The element with residues `f`. -/
def ofFn (f : Fin m → Poly F d) : Residues F d m γ := ⟨Vector.ofFn f⟩

@[simp] theorem apply_ofFn (f : Fin m → Poly F d) (i : Fin m) : (ofFn f : Residues F d m γ) i = f i :=
  Vector.getElem_ofFn ..

@[ext] theorem ext {a b : Residues F d m γ} (h : ∀ i, a i = b i) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext fun i hi => h ⟨i, hi⟩

/-- The coefficients in sequence, residue `i` at `d·i, …, d·i + d - 1` (FIPS 203 §2.4.6). -/
def flatten (a : Residues F d m γ) : Vector F (m * d) := (a.entries.map Poly.coeffs).flatten

theorem flat_idx_lt {r i : ℕ} (hr : r < d) (hi : i < m) : r + d * i < m * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m d]
  omega

def ofFlat (v : Vector F (m * d)) : Residues F d m γ :=
  ofFn fun i => Poly.ofFn fun r => v[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt)

section Ring

variable [CommRing F]

instance : Zero (Residues F d m γ) where zero := ofFn fun _ => 0
instance : One (Residues F d m γ) where one := ofFn fun _ => 1
instance : Add (Residues F d m γ) where add a b := ofFn fun i => a i + b i
instance : Sub (Residues F d m γ) where sub a b := ofFn fun i => a i - b i
instance : Neg (Residues F d m γ) where neg a := ofFn fun i => -a i
/-- Residue by residue, modulo its own component. -/
instance : Mul (Residues F d m γ) where mul a b := ofFn fun i => Poly.mulMod (γ i) (a i) (b i)
instance : SMul F (Residues F d m γ) where smul c a := ofFn fun i => c • a i

@[simp] theorem zero_apply (i : Fin m) : (0 : Residues F d m γ) i = 0 := apply_ofFn _ i
@[simp] theorem one_apply (i : Fin m) : (1 : Residues F d m γ) i = 1 := apply_ofFn _ i
@[simp] theorem add_apply (a b : Residues F d m γ) (i : Fin m) : (a + b) i = a i + b i := apply_ofFn _ i
@[simp] theorem sub_apply (a b : Residues F d m γ) (i : Fin m) : (a - b) i = a i - b i := apply_ofFn _ i
@[simp] theorem neg_apply (a : Residues F d m γ) (i : Fin m) : (-a) i = -a i := apply_ofFn _ i
@[simp] theorem mul_apply (a b : Residues F d m γ) (i : Fin m) :
    (a * b) i = Poly.mulMod (γ i) (a i) (b i) :=
  apply_ofFn _ i
@[simp] theorem smul_apply (c : F) (a : Residues F d m γ) (i : Fin m) : (c • a) i = c • a i :=
  apply_ofFn _ i

/-- Residue `i` in Mathlib's `F[X]/(X^d - γ i)`. -/
noncomputable def toR (a : Residues F d m γ) (i : Fin m) : R F d (γ i) := Poly.toR (γ i) (a i)

theorem toR_injective [IsDomain F] : Function.Injective (toR : Residues F d m γ → ∀ i, R F d (γ i)) :=
  fun _ _ h => ext fun i => Poly.toR_injective (γ i) (congrFun h i)

/-- A ring law, residue by residue through the quotient rings. -/
local macro "residue_law" : tactic =>
  `(tactic| (apply toR_injective; funext i; simp only [toR, add_apply, mul_apply, neg_apply,
      sub_apply, zero_apply, one_apply, Poly.toR_add, Poly.toR_mulMod, Poly.toR_neg,
      Poly.toR_sub, Poly.toR_zero, Poly.toR_one]; ring))

/-- The product ring structure (`F` a domain, `d ≥ 1`); the operations are the computable ones. -/
instance instCommRing [IsDomain F] [NeZero d] : CommRing (Residues F d m γ) where
  add_assoc _ _ _ := by residue_law
  zero_add _ := by residue_law
  add_zero _ := by residue_law
  add_comm _ _ := by residue_law
  neg_add_cancel _ := by residue_law
  sub_eq_add_neg _ _ := by residue_law
  left_distrib _ _ _ := by residue_law
  right_distrib _ _ _ := by residue_law
  zero_mul _ := by residue_law
  mul_zero _ := by residue_law
  mul_assoc _ _ _ := by residue_law
  one_mul _ := by residue_law
  mul_one _ := by residue_law
  mul_comm _ _ := by residue_law
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Residue `i` of a product, in degree two (FIPS 203 Algorithms 11–12). -/
theorem mul_two {γ : Fin m → F} (a b : Residues F 2 m γ) (i : Fin m) :
    (a * b) i = ⟨#v[(a i)[0] * (b i)[0] + (a i)[1] * (b i)[1] * γ i,
                   (a i)[0] * (b i)[1] + (a i)[1] * (b i)[0]]⟩ := by
  rw [mul_apply, Poly.mulMod_two]

/-- Residue `i` of a product, in degree one: the product of the values (FIPS 204 §7.6). -/
theorem getElem_mul_one {γ : Fin m → F} (a b : Residues F 1 m γ) (i : Fin m) :
    ((a * b) i)[0] = (a i)[0] * (b i)[0] := by
  rw [mul_apply, Poly.getElem_mulMod_one]

end Ring

end Residues

/-! ### The one-component case `F[X]/(X^n - c)` -/

namespace PolyMod

variable {F : Type*} {n : ℕ} {c : F}

/-- The class of the polynomial `f`. -/
def mk (f : Poly F n) : PolyMod F n c := ⟨#v[f]⟩

/-- The representative of degree below `n`. -/
def poly (a : PolyMod F n c) : Poly F n := a 0

@[simp] theorem poly_mk (f : Poly F n) : (mk f : PolyMod F n c).poly = f := rfl

@[simp] theorem mk_poly (a : PolyMod F n c) : mk a.poly = a := by
  ext i
  rw [Fin.fin_one_eq_zero i]
  rfl

@[simp] theorem apply_eq_poly (a : PolyMod F n c) (i : Fin 1) : a i = a.poly := by
  rw [Fin.fin_one_eq_zero i]; rfl

theorem mk_injective : Function.Injective (mk : Poly F n → PolyMod F n c) :=
  fun f g h => by simpa using congrArg poly h

/-- The class of the coefficient vector `v`. -/
def ofCoeffs (v : Vector F n) : PolyMod F n c := mk ⟨v⟩

def ofFn (f : Fin n → F) : PolyMod F n c := mk (Poly.ofFn f)

/-- The coefficients of the representative of degree below `n`. -/
def coeffs (a : PolyMod F n c) : Vector F n := a.poly.coeffs

instance : GetElem (PolyMod F n c) ℕ F fun _ i => i < n where
  getElem a i h := a.poly[i]

@[simp] theorem getElem_mk (f : Poly F n) (i : ℕ) (hi : i < n) : (mk f : PolyMod F n c)[i] = f[i] :=
  rfl

@[simp] theorem getElem_ofFn (f : Fin n → F) (i : ℕ) (hi : i < n) :
    (ofFn f : PolyMod F n c)[i] = f ⟨i, hi⟩ :=
  Poly.getElem_ofFn ..

@[simp] theorem getElem_ofCoeffs (v : Vector F n) (i : ℕ) (hi : i < n) :
    (ofCoeffs v : PolyMod F n c)[i] = v[i] :=
  rfl

@[simp] theorem coeffs_getElem (a : PolyMod F n c) (i : ℕ) (hi : i < n) : a.coeffs[i] = a[i] := rfl

@[simp] theorem poly_getElem (a : PolyMod F n c) (i : ℕ) (hi : i < n) : a.poly[i] = a[i] := rfl

@[ext] theorem ext {a b : PolyMod F n c} (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  rw [← mk_poly a, ← mk_poly b]
  congr 1
  exact Poly.ext h

section Ring

variable [CommRing F]

@[simp] theorem getElem_zero (i : ℕ) (hi : i < n) : (0 : PolyMod F n c)[i] = 0 := by
  show (Residues.residue (0 : Residues F n 1 _) 0)[i] = 0
  rw [Residues.zero_apply, Poly.getElem_zero]
@[simp] theorem getElem_one (i : ℕ) (hi : i < n) : (1 : PolyMod F n c)[i] = if i = 0 then 1 else 0 := by
  show (Residues.residue (1 : Residues F n 1 _) 0)[i] = _
  rw [Residues.one_apply, Poly.getElem_one]
@[simp] theorem getElem_add (a b : PolyMod F n c) (i : ℕ) (hi : i < n) : (a + b)[i] = a[i] + b[i] := by
  show (Residues.residue (a + b) 0)[i] = _
  rw [Residues.add_apply, Poly.getElem_add]; rfl
@[simp] theorem getElem_sub (a b : PolyMod F n c) (i : ℕ) (hi : i < n) : (a - b)[i] = a[i] - b[i] := by
  show (Residues.residue (a - b) 0)[i] = _
  rw [Residues.sub_apply, Poly.getElem_sub]; rfl
@[simp] theorem getElem_neg (a : PolyMod F n c) (i : ℕ) (hi : i < n) : (-a)[i] = -a[i] := by
  show (Residues.residue (-a) 0)[i] = _
  rw [Residues.neg_apply, Poly.getElem_neg]; rfl
@[simp] theorem getElem_smul (x : F) (a : PolyMod F n c) (i : ℕ) (hi : i < n) : (x • a)[i] = a[i] * x := by
  show (Residues.residue (x • a) 0)[i] = _
  rw [Residues.smul_apply, Poly.getElem_smul]; rfl

theorem poly_mul (a b : PolyMod F n c) : (a * b).poly = Poly.mulMod c a.poly b.poly :=
  Residues.mul_apply a b 0

theorem mk_mulMod (f g : Poly F n) : (mk (Poly.mulMod c f g) : PolyMod F n c) = mk f * mk g := by
  rw [← mk_poly (mk f * mk g), poly_mul, poly_mk, poly_mk]

end Ring

end PolyMod

/-- Vectors of `k` ring elements (FIPS 203 §2.4.4). -/
abbrev PolyVec (F : Type*) (n : ℕ) (c : F) (k : ℕ) := Vector (PolyMod F n c) k

end Wychelean.PolyRing
