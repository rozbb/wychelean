import Wychelean.Utils.PolyRing.Poly

namespace Wychelean.Utils.PolyRing.Poly

variable {A : Type*} [CommRing A] {n : ℕ}

theorem idx_lt {s d t r : ℕ} (hs : s < d) (ht : t < r) : s + d * t < r * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt ht)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm r d]
  omega

/-- `p mod (X^d - δ)` for `p` of degree below `n = r·d`: coefficient `x` is `∑ₜ p[x + d·t] δ^t`. -/
def modBinomial (r d : ℕ) (p : Poly A n) (δ : A) (hn : n = r * d) : Poly A d :=
  Poly.ofFn fun s => ∑ t : Fin r, p[s.val + d * t.val]'(by rw [hn]; exact idx_lt s.isLt t.isLt) * δ ^ t.val

variable {r d : ℕ} (p : Poly A n) (δ : A) (hn : n = r * d)

@[simp] theorem getElem_modBinomial (s : ℕ) (hs : s < d) :
    (p.modBinomial r d δ hn)[s] =
      ∑ t : Fin r, p[s + d * t.val]'(by rw [hn]; exact idx_lt hs t.isLt) * δ ^ t.val :=
  Poly.getElem_ofFn ..

theorem modBinomial_add (q : Poly A n) :
    (p + q).modBinomial r d δ hn = p.modBinomial r d δ hn + q.modBinomial r d δ hn := by
  ext s hs
  simp [add_mul, Finset.sum_add_distrib]

theorem modBinomial_sub (q : Poly A n) :
    (p - q).modBinomial r d δ hn = p.modBinomial r d δ hn - q.modBinomial r d δ hn := by
  ext s hs
  simp [sub_mul, Finset.sum_sub_distrib]

theorem modBinomial_neg : (-p).modBinomial r d δ hn = -p.modBinomial r d δ hn := by
  ext s hs
  simp [Finset.sum_neg_distrib]

theorem modBinomial_zero : (0 : Poly A n).modBinomial r d δ hn = 0 := by
  ext s hs
  simp

theorem modBinomial_smul (a : A) :
    (a • p).modBinomial r d δ hn = a • p.modBinomial r d δ hn := by
  ext s hs
  simp [Finset.sum_mul, mul_right_comm]

/-- Radix one: the reduction is the identity on coefficients. -/
theorem getElem_modBinomial_one (h1 : n = 1 * d) (s : ℕ) (hs : s < d) :
    (p.modBinomial 1 d δ h1)[s] = p[s]'(by rw [h1, Nat.one_mul]; exact hs) := by
  simp

/-- Radix two: `lo + δ · hi` for `p = lo + X^d · hi` (one Cooley–Tukey butterfly). -/
theorem getElem_modBinomial_two (h2 : n = 2 * d) (s : ℕ) (hs : s < d) :
    (p.modBinomial 2 d δ h2)[s] =
      p[s]'(by rw [h2]; exact Nat.lt_of_lt_of_le hs (Nat.le_mul_of_pos_left d two_pos)) +
        δ * p[s + d]'(by rw [h2, two_mul]; exact Nat.add_lt_add_right hs d) := by
  simp [Fin.sum_univ_two, mul_comm]

/-- Reducing modulo `X^(r₂·d) - δ₁` and then modulo `X^d - δ₂` with `δ₂^r₂ = δ₁` is reducing
modulo `X^d - δ₂`: the tower of quotients. -/
theorem modBinomial_modBinomial {n₁ : ℕ} (r₁ r₂ : ℕ) (hn : n = r₁ * n₁) (hn₁ : n₁ = r₂ * d)
    {δ₁ δ₂ : A} (h₂ : δ₂ ^ r₂ = δ₁) (hn' : n = (r₁ * r₂) * d) :
    (p.modBinomial r₁ n₁ δ₁ hn).modBinomial r₂ d δ₂ hn₁ = p.modBinomial (r₁ * r₂) d δ₂ hn' := by
  ext s hs
  simp only [getElem_modBinomial, Finset.sum_mul]
  refine Eq.trans ?_ (Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl)
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun t₁ _ => ?_
  simp only [finProdFinEquiv_apply_val]
  have h : s + d * (t₂.val + r₂ * t₁.val) = s + d * t₂.val + n₁ * t₁.val := by
    rw [hn₁]; ring
  simp only [h]
  rw [pow_add, pow_mul, h₂]
  ring

/-! ### The inverse of a reduction onto all `r`-th roots -/

section Field

variable {A : Type*} [Field A] {n r d : ℕ}

theorem pos_of_eq_mul {x : ℕ} (hn : n = r * d) (hx : x < n) : 0 < d :=
  Nat.pos_of_ne_zero fun h => by simp [hn, h] at hx

/-- The polynomial with residues `b k` modulo `X^d - δ k`, when the `δ k` are the `r` roots of
some `X^r - γ`: `f[x] = r⁻¹ ∑ₖ (b k)[x mod d] · (δ k)⁻¹ ^ (x / d)` (the inverse of `modBinomial`,
`modBinomial_merge`). -/
def merge (r d : ℕ) (hn : n = r * d) (δ : Fin r → A) (b : Fin r → Poly A d) : Poly A n :=
  Poly.ofFn fun x => (r : A)⁻¹ *
    ∑ k : Fin r, (b k)[x.val % d]'(Nat.mod_lt _ (pos_of_eq_mul hn x.isLt)) * (δ k)⁻¹ ^ (x.val / d)

@[simp] theorem getElem_merge (hn : n = r * d) (δ : Fin r → A) (b : Fin r → Poly A d) (x : ℕ)
    (hx : x < n) :
    (merge r d hn δ b)[x] = (r : A)⁻¹ *
      ∑ k : Fin r, (b k)[x % d]'(Nat.mod_lt _ (pos_of_eq_mul hn hx)) * (δ k)⁻¹ ^ (x / d) :=
  Poly.getElem_ofFn ..

end Field

end Wychelean.Utils.PolyRing.Poly
