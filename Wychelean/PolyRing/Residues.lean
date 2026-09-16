import Wychelean.PolyRing.Quotient

namespace Wychelean.PolyRing

/-- The product ring `∏ᵢ F[X]/(X^d - γᵢ)` for the evaluation points `γ`: residue `i`, read as
`a i`, is the polynomial with coefficients `coeffs[i]` modulo `X^d - γᵢ`. -/
structure Residues (F : Type*) (d m : ℕ) (γ : Fin m → F) where
  coeffs : Vector (Vector F d) m
deriving DecidableEq

namespace Residues

variable {F : Type*} {d m : ℕ} {γ : Fin m → F}

def residue (a : Residues F d m γ) (i : Fin m) : Poly F d (γ i) := ⟨a.coeffs[i]⟩

instance : CoeFun (Residues F d m γ) (fun _ => (i : Fin m) → Poly F d (γ i)) := ⟨residue⟩

@[simp] theorem getElem_apply (a : Residues F d m γ) (i : Fin m) (r : ℕ) (hr : r < d) :
    (a i)[r] = a.coeffs[i][r] := rfl

/-- The element with residues `f`. -/
def ofFn (f : (i : Fin m) → Poly F d (γ i)) : Residues F d m γ :=
  ⟨Vector.ofFn fun i => (f i).coeffs⟩

@[simp] theorem apply_ofFn (f : (i : Fin m) → Poly F d (γ i)) (i : Fin m) : ofFn f i = f i := by
  ext r hr
  simp [ofFn, getElem_apply]

@[ext] theorem ext {a b : Residues F d m γ} (h : ∀ i, a i = b i) : a = b := by
  cases a; cases b
  congr 1
  apply Vector.ext
  intro i hi
  simpa [residue] using h ⟨i, hi⟩

/-- `f` itself, as the single residue modulo `X^n - c`. -/
def ofPoly {n : ℕ} {c : F} (f : Poly F n c) : Residues F n 1 (fun _ => c) := ⟨#v[f.coeffs]⟩

@[simp] theorem ofPoly_apply {n : ℕ} {c : F} (f : Poly F n c) (i : Fin 1) : ofPoly f i = f := by
  ext r hr
  simp [ofPoly, getElem_apply, Fin.fin_one_eq_zero i]

section Ring

variable [CommRing F]

instance : Zero (Residues F d m γ) where zero := ofFn fun _ => 0
instance : One (Residues F d m γ) where one := ofFn fun _ => 1
instance : Add (Residues F d m γ) where add a b := ofFn fun i => a i + b i
instance : Sub (Residues F d m γ) where sub a b := ofFn fun i => a i - b i
instance : Neg (Residues F d m γ) where neg a := ofFn fun i => -a i
instance : Mul (Residues F d m γ) where mul a b := ofFn fun i => a i * b i
instance : SMul F (Residues F d m γ) where smul c a := ofFn fun i => c • a i

@[simp] theorem zero_apply (i : Fin m) : (0 : Residues F d m γ) i = 0 := apply_ofFn _ i
@[simp] theorem one_apply (i : Fin m) : (1 : Residues F d m γ) i = 1 := apply_ofFn _ i
@[simp] theorem add_apply (a b : Residues F d m γ) (i : Fin m) : (a + b) i = a i + b i := apply_ofFn _ i
@[simp] theorem sub_apply (a b : Residues F d m γ) (i : Fin m) : (a - b) i = a i - b i := apply_ofFn _ i
@[simp] theorem neg_apply (a : Residues F d m γ) (i : Fin m) : (-a) i = -a i := apply_ofFn _ i
@[simp] theorem mul_apply (a b : Residues F d m γ) (i : Fin m) : (a * b) i = a i * b i := apply_ofFn _ i
@[simp] theorem smul_apply (c : F) (a : Residues F d m γ) (i : Fin m) : (c • a) i = c • a i :=
  apply_ofFn _ i

@[simp] theorem ofPoly_add {n : ℕ} {c : F} (f g : Poly F n c) : ofPoly (f + g) = ofPoly f + ofPoly g := by
  ext i; simp
@[simp] theorem ofPoly_mul {n : ℕ} {c : F} (f g : Poly F n c) : ofPoly (f * g) = ofPoly f * ofPoly g := by
  ext i; simp

/-- The product ring structure, residue by residue (`F` a domain, `d ≥ 1`). -/
instance instCommRing [IsDomain F] [NeZero d] : CommRing (Residues F d m γ) where
  add_assoc _ _ _ := by ext i; simp [add_assoc]
  zero_add _ := by ext i; simp
  add_zero _ := by ext i; simp
  add_comm _ _ := by ext i; simp [add_comm]
  neg_add_cancel _ := by ext i; simp
  sub_eq_add_neg _ _ := by ext i; simp [sub_eq_add_neg]
  left_distrib _ _ _ := by ext i; simp [left_distrib]
  right_distrib _ _ _ := by ext i; simp [right_distrib]
  zero_mul _ := by ext i; simp
  mul_zero _ := by ext i; simp
  mul_assoc _ _ _ := by ext i; simp [mul_assoc]
  one_mul _ := by ext i; simp
  mul_one _ := by ext i; simp
  mul_comm _ _ := by ext i; simp [mul_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Residue `i` of a product, in degree two (FIPS 203 Algorithms 11–12). -/
theorem mul_two {γ : Fin m → F} (a b : Residues F 2 m γ) (i : Fin m) :
    (a * b) i = ⟨#v[(a i)[0] * (b i)[0] + (a i)[1] * (b i)[1] * γ i,
                   (a i)[0] * (b i)[1] + (a i)[1] * (b i)[0]]⟩ := by
  rw [mul_apply, Poly.mul_two]

/-- Residue `i` of a product, in degree one: the product of the values (FIPS 204 §7.6). -/
theorem getElem_mul_one {γ : Fin m → F} (a b : Residues F 1 m γ) (i : Fin m) :
    ((a * b) i)[0] = (a i)[0] * (b i)[0] := by
  rw [mul_apply, Poly.getElem_mul_one]

end Ring

/-- The coefficients in sequence, residue `i` at `d·i, …, d·i + d - 1` (FIPS 203 §2.4.6). -/
def flatten (a : Residues F d m γ) : Vector F (m * d) := a.coeffs.flatten

theorem flat_idx_lt {r i : ℕ} (hr : r < d) (hi : i < m) : r + d * i < m * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m d]
  omega

def ofFlat (v : Vector F (m * d)) : Residues F d m γ :=
  ⟨Vector.ofFn fun i => Vector.ofFn fun r => v[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt)⟩

/-- One Cooley–Tukey layer. Residue `j` is `lo + γ' j · hi` for `a (j/2) = lo + X^d · hi`,
which is `a (j/2) mod (X^d - γ' j)` when `(γ' j)^2 = γ (j/2)`. -/
def split [CommRing F] {d' m' : ℕ} (a : Residues F d' m γ) (γ' : Fin m' → F) (hd : d' = 2 * d)
    (hm : m' = m * 2) : Residues F d m' γ' :=
  ofFn fun j =>
    let p := a ⟨j.val / 2, by omega⟩
    Poly.ofFn fun r => p[r.val]'(by omega) + γ' j * p[r.val + d]'(by omega)

theorem getElem_split [CommRing F] {d' m' : ℕ} (a : Residues F d' m γ) (γ' : Fin m' → F)
    (hd : d' = 2 * d) (hm : m' = m * 2) (j : Fin m') (r : ℕ) (hr : r < d) :
    (split a γ' hd hm j)[r] =
      (a ⟨j.val / 2, by omega⟩)[r]'(by omega) + γ' j * (a ⟨j.val / 2, by omega⟩)[r + d]'(by omega) := by
  simp [split]

end Residues

end Wychelean.PolyRing
