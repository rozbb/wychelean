import Wychelean.Utils.PolyRing.Poly

namespace Wychelean.Utils.PolyRing.Poly

variable {A : Type*} [CommRing A] {d k n : ℕ}

/-- `f · g` as a polynomial of degree below `a + b`. -/
def conv {a b : ℕ} (f : Poly A a) (g : Poly A b) : Poly A (a + b) :=
  ofFn fun k => ∑ i : Fin a,
    if h : i.val ≤ k.val ∧ k.val - i.val < b then f[i] * g[k.val - i.val]'h.2 else 0

@[simp] theorem getElem_conv {a b : ℕ} (f : Poly A a) (g : Poly A b) (k : ℕ) (hk : k < a + b) :
    (conv f g)[k] = ∑ i : Fin a,
      if h : i.val ≤ k ∧ k - i.val < b then f[i] * g[k - i.val]'h.2 else 0 :=
  getElem_ofFn ..

/-- One step of long division by `X^d + μ`: `f[d+k]·X^(d+k) ≡ -f[d+k]·X^k·μ`. -/
def reduceTop (μ : Poly A d) (f : Poly A (d + k + 1)) : Poly A (d + k) :=
  ofFn fun i => f[i.val]'(Nat.lt_succ_of_lt i.isLt) - f[d + k] * (shift k μ)[i]

@[simp] theorem getElem_reduceTop (μ : Poly A d) (f : Poly A (d + k + 1)) (i : ℕ) (hi : i < d + k) :
    (reduceTop μ f)[i] = f[i]'(Nat.lt_succ_of_lt hi) - f[d + k] * (shift k μ)[i] :=
  getElem_ofFn ..

/-- `f mod (X^d + μ)` for `f` of degree below `d + k`: peel the top coefficient `k` times. -/
def modMonicAux (μ : Poly A d) : (k : ℕ) → Poly A (d + k) → Poly A d
  | 0, f => f
  | k + 1, f => modMonicAux μ k (reduceTop μ f)

/-- `f mod (X^d + μ)`. -/
def modMonic (μ : Poly A d) (f : Poly A n) : Poly A d := modMonicAux μ n (pad d f)

/-- The product in `A[X]/(X^d + μ)`. -/
def mulMonic (μ : Poly A d) (f g : Poly A d) : Poly A d := modMonicAux μ d (conv f g)

variable (μ : Poly A d)

theorem reduceTop_add (f g : Poly A (d + k + 1)) :
    reduceTop μ (f + g) = reduceTop μ f + reduceTop μ g := by
  ext i hi
  simp only [getElem_reduceTop, getElem_add]
  ring

theorem reduceTop_sub (f g : Poly A (d + k + 1)) :
    reduceTop μ (f - g) = reduceTop μ f - reduceTop μ g := by
  ext i hi
  simp only [getElem_reduceTop, getElem_sub]
  ring

theorem reduceTop_neg (f : Poly A (d + k + 1)) : reduceTop μ (-f) = -reduceTop μ f := by
  ext i hi
  simp only [getElem_reduceTop, getElem_neg]
  ring

theorem reduceTop_smul (a : A) (f : Poly A (d + k + 1)) : reduceTop μ (a • f) = a • reduceTop μ f := by
  ext i hi
  simp only [getElem_reduceTop, getElem_smul]
  ring

theorem reduceTop_zero : reduceTop μ (0 : Poly A (d + k + 1)) = 0 := by
  ext i hi
  simp

theorem modMonicAux_add : ∀ (k : ℕ) (f g : Poly A (d + k)),
    modMonicAux μ k (f + g) = modMonicAux μ k f + modMonicAux μ k g
  | 0, _, _ => rfl
  | k + 1, f, g => by rw [modMonicAux, reduceTop_add, modMonicAux_add k]; rfl

theorem modMonicAux_neg : ∀ (k : ℕ) (f : Poly A (d + k)),
    modMonicAux μ k (-f) = -modMonicAux μ k f
  | 0, _ => rfl
  | k + 1, f => by rw [modMonicAux, reduceTop_neg, modMonicAux_neg k]; rfl

theorem modMonicAux_smul : ∀ (k : ℕ) (a : A) (f : Poly A (d + k)),
    modMonicAux μ k (a • f) = a • modMonicAux μ k f
  | 0, _, _ => rfl
  | k + 1, a, f => by rw [modMonicAux, reduceTop_smul, modMonicAux_smul k]; rfl

theorem modMonicAux_zero : ∀ k : ℕ, modMonicAux μ k (0 : Poly A (d + k)) = 0
  | 0 => rfl
  | k + 1 => by rw [modMonicAux, reduceTop_zero, modMonicAux_zero k]

theorem modMonicAux_sub : ∀ (k : ℕ) (f g : Poly A (d + k)),
    modMonicAux μ k (f - g) = modMonicAux μ k f - modMonicAux μ k g
  | 0, _, _ => rfl
  | k + 1, f, g => by rw [modMonicAux, reduceTop_sub, modMonicAux_sub k]; rfl

theorem pad_add (f g : Poly A n) : pad d (f + g) = pad d f + pad d g := by
  ext i hi
  simp only [getElem_pad, getElem_add]
  split_ifs <;> simp

theorem pad_sub (f g : Poly A n) : pad d (f - g) = pad d f - pad d g := by
  ext i hi
  simp only [getElem_pad, getElem_sub]
  split_ifs <;> simp

theorem pad_neg (f : Poly A n) : pad d (-f) = -pad d f := by
  ext i hi
  simp only [getElem_pad, getElem_neg]
  split_ifs <;> simp

theorem pad_smul (a : A) (f : Poly A n) : pad d (a • f) = a • pad d f := by
  ext i hi
  simp only [getElem_pad, getElem_smul]
  split_ifs <;> simp

theorem pad_zero : pad d (0 : Poly A n) = 0 := by
  ext i hi
  simp only [getElem_pad, getElem_zero]
  split_ifs <;> rfl

theorem modMonic_add (f g : Poly A n) : modMonic μ (f + g) = modMonic μ f + modMonic μ g := by
  rw [modMonic, modMonic, modMonic, pad_add, modMonicAux_add]

theorem modMonic_neg (f : Poly A n) : modMonic μ (-f) = -modMonic μ f := by
  rw [modMonic, modMonic, pad_neg, modMonicAux_neg]

theorem modMonic_sub (f g : Poly A n) : modMonic μ (f - g) = modMonic μ f - modMonic μ g := by
  rw [modMonic, modMonic, modMonic, pad_sub, modMonicAux_sub]

theorem modMonic_smul (a : A) (f : Poly A n) : modMonic μ (a • f) = a • modMonic μ f := by
  rw [modMonic, modMonic, pad_smul, modMonicAux_smul]

theorem modMonic_zero : modMonic μ (0 : Poly A n) = 0 := by
  rw [modMonic, pad_zero, modMonicAux_zero]

end Wychelean.Utils.PolyRing.Poly
