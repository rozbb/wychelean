import Wychelean.Utils.PolyRing.ModMonicProperties

namespace Wychelean.Utils.PolyRing

/-- Residues modulo the components `X^d + μᵢ`: `a i` is the residue modulo `X^d + μ i`. -/
structure Residues (F : Type*) (d m : ℕ) (μ : Fin m → Poly F d) where
  entries : Vector (Poly F d) m
deriving DecidableEq

/-- The components `X^d - γᵢ`. -/
abbrev Residues.Binomial (F : Type*) [CommRing F] (d m : ℕ) (γ : Fin m → F) :=
  Residues F d m fun i => Poly.binomial (γ i)

/-- The ring `F[X]/(X^n + μ)` as the one-component product. -/
abbrev PolyQuot (F : Type*) (n : ℕ) (μ : Poly F n) := Residues F n 1 fun _ => μ

/-- The ring `F[X]/(X^n - c)`. -/
abbrev PolyMod (F : Type*) [CommRing F] (n : ℕ) (c : F) := PolyQuot F n (Poly.binomial c)

namespace Residues

variable {F : Type*} {d m : ℕ} {μ : Fin m → Poly F d}

/-- Residue `i`, modulo `X^d + μ i`. -/
def residue (a : Residues F d m μ) (i : Fin m) : Poly F d := a.entries[i]

instance : CoeFun (Residues F d m μ) (fun _ => Fin m → Poly F d) := ⟨residue⟩

@[simp] theorem apply_mk (v : Vector (Poly F d) m) (i : Fin m) : (⟨v⟩ : Residues F d m μ) i = v[i] :=
  rfl

/-- The element with residues `f`. -/
def ofFn (f : Fin m → Poly F d) : Residues F d m μ := ⟨Vector.ofFn f⟩

@[simp] theorem apply_ofFn (f : Fin m → Poly F d) (i : Fin m) : (ofFn f : Residues F d m μ) i = f i :=
  Vector.getElem_ofFn ..

@[ext] theorem ext {a b : Residues F d m μ} (h : ∀ i, a i = b i) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext fun i hi => h ⟨i, hi⟩

instance [Subsingleton F] : Subsingleton (Residues F d m μ) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

instance {μ : Fin m → Poly F 0} : Subsingleton (Residues F 0 m μ) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

/-- The coefficients in sequence, residue `i` at `d·i, …, d·i + d - 1` (FIPS 203 §2.4.6). -/
def flatten (a : Residues F d m μ) : Vector F (m * d) := (a.entries.map Poly.coeffs).flatten

theorem flat_idx_lt {r i : ℕ} (hr : r < d) (hi : i < m) : r + d * i < m * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m d]
  omega

def ofFlat (v : Vector F (m * d)) : Residues F d m μ :=
  ofFn fun i => Poly.ofFn fun r => v[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt)

@[simp] theorem getElem_flatten (a : Residues F d m μ) (i : Fin m) (r : Fin d) :
    a.flatten[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt) = (a i)[r.val] := by
  have hd : 0 < d := Nat.zero_lt_of_lt r.isLt
  simp only [flatten, Vector.getElem_flatten, Vector.getElem_map]
  have hdiv : (r.val + d * i.val) / d = i.val := by
    rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
  have hmod : (r.val + d * i.val) % d = r.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  simp only [hdiv, hmod]
  rfl

@[simp] theorem ofFlat_flatten (a : Residues F d m μ) : ofFlat a.flatten = a := by
  apply ext
  intro i
  apply Poly.ext
  intro r hr
  simp only [ofFlat, apply_ofFn, Poly.getElem_ofFn, getElem_flatten a i ⟨r, hr⟩]

@[simp] theorem flatten_ofFlat (v : Vector F (m * d)) :
    (ofFlat v : Residues F d m μ).flatten = v := by
  apply Vector.ext
  intro j hj
  have hd : 0 < d := Nat.pos_of_lt_mul_left hj
  have hi : j / d < m := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hj)
  have hr : j % d < d := Nat.mod_lt _ hd
  have heq : j % d + d * (j / d) = j := Nat.mod_add_div _ _
  have h := getElem_flatten (ofFlat v : Residues F d m μ) ⟨j / d, hi⟩ ⟨j % d, hr⟩
  simp only [ofFlat, apply_ofFn, Poly.getElem_ofFn] at h
  simpa only [heq, ofFlat] using h

section Ring

variable [CommRing F]

instance : Zero (Residues F d m μ) where zero := ofFn fun _ => 0
instance : One (Residues F d m μ) where one := ofFn fun _ => 1
instance : Add (Residues F d m μ) where add a b := ofFn fun i => a i + b i
instance : Sub (Residues F d m μ) where sub a b := ofFn fun i => a i - b i
instance : Neg (Residues F d m μ) where neg a := ofFn fun i => -a i
/-- Residue by residue, modulo its own component. -/
instance : Mul (Residues F d m μ) where mul a b := ofFn fun i => Poly.mulMonic (μ i) (a i) (b i)
instance : SMul F (Residues F d m μ) where smul c a := ofFn fun i => c • a i

@[simp] theorem zero_apply (i : Fin m) : (0 : Residues F d m μ) i = 0 := apply_ofFn _ i
@[simp] theorem one_apply (i : Fin m) : (1 : Residues F d m μ) i = 1 := apply_ofFn _ i
@[simp] theorem add_apply (a b : Residues F d m μ) (i : Fin m) : (a + b) i = a i + b i := apply_ofFn _ i
@[simp] theorem sub_apply (a b : Residues F d m μ) (i : Fin m) : (a - b) i = a i - b i := apply_ofFn _ i
@[simp] theorem neg_apply (a : Residues F d m μ) (i : Fin m) : (-a) i = -a i := apply_ofFn _ i
@[simp] theorem mul_apply (a b : Residues F d m μ) (i : Fin m) :
    (a * b) i = Poly.mulMonic (μ i) (a i) (b i) :=
  apply_ofFn _ i
@[simp] theorem smul_apply (c : F) (a : Residues F d m μ) (i : Fin m) : (c • a) i = c • a i :=
  apply_ofFn _ i

/-- At binomial components the product is the wrap-around product. -/
theorem mul_apply_binomial {γ : Fin m → F} (a b : Residues.Binomial F d m γ) (i : Fin m) :
    (a * b) i = Poly.mulMod (γ i) (a i) (b i) := by
  rw [mul_apply, Poly.mulMonic_binomial]

/-- Residue `i` in Mathlib's `F[X]/(X^d + μ i)`. -/
noncomputable def toR (a : Residues F d m μ) (i : Fin m) : R F d (μ i) := Poly.toR (μ i) (a i)

theorem toR_injective [Nontrivial F] :
    Function.Injective (toR : Residues F d m μ → ∀ i, R F d (μ i)) :=
  fun _ _ h => ext fun i => Poly.toR_injective _ (congrFun h i)

/-- Equality through the quotient rings, for any coefficient ring and degree. -/
theorem eq_of_toR {a b : Residues F d m μ} (h : ∀ [Nontrivial F] [NeZero d], a.toR = b.toR) :
    a = b := by
  rcases subsingleton_or_nontrivial F with _ | _
  · exact Subsingleton.elim _ _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  have : NeZero d := ⟨hd.ne'⟩
  exact toR_injective h

/-- A ring law, residue by residue through the quotient rings. -/
local macro "residue_law" : tactic =>
  `(tactic| (apply eq_of_toR; intro _ _; funext i; simp only [toR, add_apply, mul_apply, neg_apply,
      sub_apply, zero_apply, one_apply, Poly.toR_add, Poly.toR_mulMonic, Poly.toR_neg,
      Poly.toR_sub, Poly.toR_zero, Poly.toR_one]; ring))

/-- The product ring structure; the operations are the computable ones. -/
instance instCommRing : CommRing (Residues F d m μ) where
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
theorem mul_two {γ : Fin m → F} (a b : Residues.Binomial F 2 m γ) (i : Fin m) :
    (a * b) i = ⟨#v[(a i)[0] * (b i)[0] + (a i)[1] * (b i)[1] * γ i,
                   (a i)[0] * (b i)[1] + (a i)[1] * (b i)[0]]⟩ := by
  rw [mul_apply_binomial, Poly.mulMod_two]

/-- Residue `i` of a product, in degree one: the product of the values (FIPS 204 §7.6). -/
theorem getElem_mul_one {γ : Fin m → F} (a b : Residues.Binomial F 1 m γ) (i : Fin m) :
    ((a * b) i)[0] = (a i)[0] * (b i)[0] := by
  rw [mul_apply_binomial, Poly.getElem_mulMod_one]

end Ring

end Residues

/-! ### The one-component case `F[X]/(X^n + μ)` -/

namespace PolyQuot

variable {F : Type*} {n : ℕ} {μ : Poly F n}

/-- The class of the polynomial `f`. -/
def mk (f : Poly F n) : PolyQuot F n μ := ⟨#v[f]⟩

/-- The representative of degree below `n`. -/
def poly (a : PolyQuot F n μ) : Poly F n := a 0

@[simp] theorem poly_mk (f : Poly F n) : (mk f : PolyQuot F n μ).poly = f := rfl

@[simp] theorem mk_poly (a : PolyQuot F n μ) : mk a.poly = a := by
  ext i
  rw [Fin.fin_one_eq_zero i]
  rfl

@[simp] theorem apply_eq_poly (a : PolyQuot F n μ) (i : Fin 1) : a i = a.poly := by
  rw [Fin.fin_one_eq_zero i]; rfl

theorem mk_injective : Function.Injective (mk : Poly F n → PolyQuot F n μ) :=
  fun f g h => by simpa using congrArg poly h

/-- The class of the coefficient vector `v`. -/
def ofCoeffs (v : Vector F n) : PolyQuot F n μ := mk ⟨v⟩

def ofFn (f : Fin n → F) : PolyQuot F n μ := mk (Poly.ofFn f)

/-- The coefficients of the representative of degree below `n`. -/
def coeffs (a : PolyQuot F n μ) : Vector F n := a.poly.coeffs

instance : GetElem (PolyQuot F n μ) ℕ F fun _ i => i < n where
  getElem a i h := a.poly[i]

@[simp] theorem getElem_mk (f : Poly F n) (i : ℕ) (hi : i < n) : (mk f : PolyQuot F n μ)[i] = f[i] :=
  rfl

@[simp] theorem getElem_ofFn (f : Fin n → F) (i : ℕ) (hi : i < n) :
    (ofFn f : PolyQuot F n μ)[i] = f ⟨i, hi⟩ :=
  Poly.getElem_ofFn ..

@[simp] theorem getElem_ofCoeffs (v : Vector F n) (i : ℕ) (hi : i < n) :
    (ofCoeffs v : PolyQuot F n μ)[i] = v[i] :=
  rfl

@[simp] theorem coeffs_getElem (a : PolyQuot F n μ) (i : ℕ) (hi : i < n) : a.coeffs[i] = a[i] := rfl

@[simp] theorem poly_getElem (a : PolyQuot F n μ) (i : ℕ) (hi : i < n) : a.poly[i] = a[i] := rfl

@[ext] theorem ext {a b : PolyQuot F n μ} (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  rw [← mk_poly a, ← mk_poly b]
  congr 1
  exact Poly.ext h

section Ring

variable [CommRing F]

@[simp] theorem getElem_zero (i : ℕ) (hi : i < n) : (0 : PolyQuot F n μ)[i] = 0 := by
  show (Residues.residue (0 : Residues F n 1 _) 0)[i] = 0
  rw [Residues.zero_apply, Poly.getElem_zero]
@[simp] theorem getElem_one (i : ℕ) (hi : i < n) : (1 : PolyQuot F n μ)[i] = if i = 0 then 1 else 0 := by
  show (Residues.residue (1 : Residues F n 1 _) 0)[i] = _
  rw [Residues.one_apply, Poly.getElem_one]
@[simp] theorem getElem_add (a b : PolyQuot F n μ) (i : ℕ) (hi : i < n) : (a + b)[i] = a[i] + b[i] := by
  show (Residues.residue (a + b) 0)[i] = _
  rw [Residues.add_apply, Poly.getElem_add]; rfl
@[simp] theorem getElem_sub (a b : PolyQuot F n μ) (i : ℕ) (hi : i < n) : (a - b)[i] = a[i] - b[i] := by
  show (Residues.residue (a - b) 0)[i] = _
  rw [Residues.sub_apply, Poly.getElem_sub]; rfl
@[simp] theorem getElem_neg (a : PolyQuot F n μ) (i : ℕ) (hi : i < n) : (-a)[i] = -a[i] := by
  show (Residues.residue (-a) 0)[i] = _
  rw [Residues.neg_apply, Poly.getElem_neg]; rfl
@[simp] theorem getElem_smul (x : F) (a : PolyQuot F n μ) (i : ℕ) (hi : i < n) : (x • a)[i] = a[i] * x := by
  show (Residues.residue (x • a) 0)[i] = _
  rw [Residues.smul_apply, Poly.getElem_smul]; rfl

theorem poly_mul (a b : PolyQuot F n μ) : (a * b).poly = Poly.mulMonic μ a.poly b.poly :=
  Residues.mul_apply a b 0

theorem mk_mulMonic (f g : Poly F n) : (mk (Poly.mulMonic μ f g) : PolyQuot F n μ) = mk f * mk g := by
  rw [← mk_poly (mk f * mk g), poly_mul, poly_mk, poly_mk]

theorem poly_mul_binomial {c : F} (a b : PolyMod F n c) : (a * b).poly = Poly.mulMod c a.poly b.poly :=
  Residues.mul_apply_binomial a b 0

theorem mk_mulMod (c : F) (f g : Poly F n) : (mk (Poly.mulMod c f g) : PolyMod F n c) = mk f * mk g := by
  rw [← Poly.mulMonic_binomial, mk_mulMonic]

end Ring

end PolyQuot

namespace PolyMod

variable {F : Type*} [CommRing F] {n : ℕ} {c : F}

abbrev mk (f : Poly F n) : PolyMod F n c := PolyQuot.mk f
abbrev poly (a : PolyMod F n c) : Poly F n := PolyQuot.poly a
abbrev ofCoeffs (v : Vector F n) : PolyMod F n c := PolyQuot.ofCoeffs v
abbrev ofFn (f : Fin n → F) : PolyMod F n c := PolyQuot.ofFn f
abbrev coeffs (a : PolyMod F n c) : Vector F n := PolyQuot.coeffs a

end PolyMod

/-- Vectors of `k` ring elements (FIPS 203 §2.4.4). -/
abbrev PolyVec (F : Type*) [CommRing F] (n : ℕ) (c : F) (k : ℕ) := Vector (PolyMod F n c) k

end Wychelean.Utils.PolyRing
