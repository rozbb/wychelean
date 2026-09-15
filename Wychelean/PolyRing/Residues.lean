import Wychelean.PolyRing.Poly

namespace Wychelean.PolyRing

/-- The product ring `∏ᵢ ℤ_q[X]/(X^d - γᵢ)` for the evaluation points `γ`, stored as the residues'
coefficients in sequence, residue `i` at `d·i, …, d·i + d - 1` (the order of FIPS 203 §2.4.6);
`a i` reads residue `i`. -/
structure Residues (q d m : ℕ) (γ : Fin m → ZMod q) where
  flat : Vector (ZMod q) (m * d)
deriving DecidableEq

namespace Residues

variable {q d m : ℕ} {γ : Fin m → ZMod q}

theorem flat_idx_lt {r i : ℕ} (hr : r < d) (hi : i < m) : r + d * i < m * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m d]
  omega

def residue (a : Residues q d m γ) (i : Fin m) : Poly (ZMod q) d (γ i) :=
  Poly.ofFn fun r => a.flat[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt)

instance : CoeFun (Residues q d m γ) (fun _ => (i : Fin m) → Poly (ZMod q) d (γ i)) := ⟨residue⟩

@[simp] theorem getElem_apply (a : Residues q d m γ) (i : Fin m) (r : ℕ) (hr : r < d) :
    (a i)[r] = a.flat[r + d * i.val]'(flat_idx_lt hr i.isLt) :=
  Poly.getElem_ofFn ..

/-- The element with residues `f`. -/
def ofFn (f : (i : Fin m) → Poly (ZMod q) d (γ i)) : Residues q d m γ :=
  ⟨(Vector.ofFn fun i => (f i).coeffs).flatten⟩

@[simp] theorem apply_ofFn (f : (i : Fin m) → Poly (ZMod q) d (γ i)) (i : Fin m) : ofFn f i = f i := by
  ext r hr
  have h1 : (r + d * i.val) / d = i.val := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have h2 : (r + d * i.val) % d = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  simp [ofFn, getElem_apply, Vector.getElem_flatten, h1, h2]

@[ext] theorem ext {a b : Residues q d m γ} (h : ∀ i, a i = b i) : a = b := by
  cases a; cases b
  congr 1
  apply Vector.ext
  intro k hk
  have hd : 0 < d := Nat.pos_of_lt_mul_left hk
  have := congrArg (fun p => p[k % d]'(Nat.mod_lt _ hd))
    (h ⟨k / d, (Nat.div_lt_iff_lt_mul hd).2 hk⟩)
  simpa [getElem_apply, Nat.mod_add_div] using this

instance : Zero (Residues q d m γ) where zero := ofFn fun _ => 0
instance : Add (Residues q d m γ) where add a b := ofFn fun i => a i + b i
instance : Sub (Residues q d m γ) where sub a b := ofFn fun i => a i - b i
instance : Mul (Residues q d m γ) where mul a b := ofFn fun i => a i * b i

@[simp] theorem zero_apply (i : Fin m) : (0 : Residues q d m γ) i = 0 := apply_ofFn _ i
@[simp] theorem add_apply (a b : Residues q d m γ) (i : Fin m) : (a + b) i = a i + b i := apply_ofFn _ i
@[simp] theorem sub_apply (a b : Residues q d m γ) (i : Fin m) : (a - b) i = a i - b i := apply_ofFn _ i
@[simp] theorem mul_apply (a b : Residues q d m γ) (i : Fin m) : (a * b) i = a i * b i := apply_ofFn _ i

/-- Residue `i` of a product, in degree two (FIPS 203 Algorithms 11–12). -/
theorem mul_two {γ : Fin m → ZMod q} (a b : Residues q 2 m γ) (i : Fin m) :
    (a * b) i = ⟨#v[(a i)[0] * (b i)[0] + (a i)[1] * (b i)[1] * γ i,
                   (a i)[0] * (b i)[1] + (a i)[1] * (b i)[0]]⟩ := by
  rw [mul_apply, Poly.mul_two]

/-- One Cooley–Tukey layer. Residue `j` is `lo + γ' j · hi` for `a (j/2) = lo + X^d · hi`,
which is `a (j/2) mod (X^d - γ' j)` when `(γ' j)^2 = γ (j/2)`. -/
def split {d' m' : ℕ} (a : Residues q d' m γ) (γ' : Fin m' → ZMod q) (hd : d' = 2 * d)
    (hm : m' = m * 2) : Residues q d m' γ' :=
  ofFn fun j =>
    let p := a ⟨j.val / 2, by omega⟩
    Poly.ofFn fun r => p[r.val]'(by omega) + γ' j * p[r.val + d]'(by omega)

theorem getElem_split {d' m' : ℕ} (a : Residues q d' m γ) (γ' : Fin m' → ZMod q) (hd : d' = 2 * d)
    (hm : m' = m * 2) (j : Fin m') (r : ℕ) (hr : r < d) :
    (split a γ' hd hm j)[r] =
      (a ⟨j.val / 2, by omega⟩)[r]'(by omega) + γ' j * (a ⟨j.val / 2, by omega⟩)[r + d]'(by omega) := by
  simp [split]

end Residues

end Wychelean.PolyRing
