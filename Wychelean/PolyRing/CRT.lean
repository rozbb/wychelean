import Wychelean.PolyRing.SplitProperties
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.KummerExtension

/-!
The Chinese remainder reading of a layer. A component `(d, γᵢ)` is the ideal `(X^d - γᵢ)`; the
modulus of `Residues.Binomial F d m γ` is the product of its components, a layer refines the
factorisation without changing the product (`modulus_split`), and the canonical map from the
root ring to the product of the component quotients is a ring isomorphism (`crtEquiv`) tracked
by the computable transform (`crtHom_toR`).
-/

namespace Wychelean.PolyRing

open Polynomial

noncomputable section

namespace Residues

variable {F : Type*} [CommRing F] {d m : ℕ}

/-! ### The modulus of a product of components -/

/-- The product of the component ideals' generators, `∏ᵢ (X^d - γᵢ)`. -/
def modulus (d : ℕ) (γ : Fin m → F) : F[X] := ∏ i, (X ^ d - C (γ i))

@[simp] theorem modulus_one (n : ℕ) (c : F) : modulus n (fun _ : Fin 1 => c) = X ^ n - C c := by
  rw [modulus, Fin.prod_univ_one]

/-- The `r` components above a residue multiply to that residue's component:
`∏ₖ (X^d - δ ω^(σ k)) = X^{r·d} - δ^r`. -/
theorem prod_block [IsDomain F] {r : ℕ} (hr : 0 < r) {ω δ γ : F} (hω : IsPrimitiveRoot ω r)
    (hδ : δ ^ r = γ) (σ : Fin r ≃ Fin r) :
    ∏ k : Fin r, (X ^ d - C (δ * ω ^ (σ k).val)) = X ^ (r * d) - C γ := by
  have h := congrArg (expand F d) (X_pow_sub_C_eq_prod hω hr hδ)
  simp only [map_sub, map_pow, map_prod, expand_X, expand_C, ← pow_mul] at h
  calc ∏ k : Fin r, (X ^ d - C (δ * ω ^ (σ k).val))
      = ∏ k : Fin r, (X ^ d - C (ω ^ k.val * δ)) := by
        rw [← Equiv.prod_comp σ (fun k : Fin r => X ^ d - C (ω ^ k.val * δ))]
        exact Finset.prod_congr rfl fun k _ => by rw [mul_comm]
    _ = ∏ i ∈ Finset.range r, (X ^ d - C (ω ^ i * δ)) :=
        Fin.prod_univ_eq_prod_range (fun i => X ^ d - C (ω ^ i * δ)) r
    _ = X ^ (r * d) - C γ := by rw [mul_comm r d, h]

/-- A layer refines the factorisation of the same modulus. -/
theorem modulus_split [IsDomain F] {r m' d' : ℕ} {γ : Fin m → F} {γ' : Fin m' → F}
    (hd : d' = r * d) (hm : m' = m * r) (h : SplitPoints r γ γ' hm) (hr : 0 < r) :
    modulus d γ' = modulus d' γ := by
  subst hm
  rw [modulus, modulus, ← Fintype.prod_equiv finProdFinEquiv
    (fun p : Fin m × Fin r => X ^ d - C (γ' (finProdFinEquiv p))) _ (fun _ => rfl),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨_, ω, δ, σ, hω, hδ, hpts⟩ := h i
  rw [hd, ← prod_block hr hω hδ σ]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hpts k]
  rfl

end Residues

/-! ### The canonical map to the product of the component quotients -/

namespace Residues

section Hom

variable {F : Type*} [CommRing F] {n d m : ℕ} {c : F} {γ : Fin m → F}

/-- `F[X]/(X^n - c) → ∏ᵢ F[X]/(X^d - γᵢ)` when `n = m·d` and each `γᵢ` is an `m`-th root of `c`. -/
def crtHom [NeZero m] (hn : n = m * d) (h : LayerPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    R F n (Poly.binomial c) →+* ∀ i, R F d (Poly.binomial (γ i)) :=
  RingHom.pi fun i => R.reduceBinomial m d hn (γ i) (h i)

/-- The computable one-shot layer tracks the canonical map. -/
theorem crtHom_toR [NeZero m] (hn : n = m * d)
    (h : LayerPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) (f : PolyMod F n c) :
    crtHom hn h (Poly.toR (Poly.binomial c) f.poly) = (split m f γ hn (Nat.one_mul _).symm).toR := by
  funext i
  rw [crtHom, RingHom.pi_apply, toR, split_apply, PolyQuot.apply_eq_poly, Poly.toR_modBinomial]

end Hom

section Equiv

variable {F : Type*} [Field F] {n d m : ℕ} {c : F} {γ : Fin m → F}

theorem crtHom_bijective [NeZero n] [NeZero d] [NeZero m] (hn : n = m * d) (hm : (m : F) ≠ 0)
    (h : SplitPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    Function.Bijective (crtHom hn h.layerPoints) := by
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := Poly.toR_surjective (Poly.binomial c) x
    obtain ⟨g, rfl⟩ := Poly.toR_surjective (Poly.binomial c) y
    rw [← PolyQuot.poly_mk (μ := Poly.binomial c) f, ← PolyQuot.poly_mk (μ := Poly.binomial c) g, crtHom_toR, crtHom_toR] at hxy
    have hmk : (PolyQuot.mk f : PolyMod F n c) = PolyQuot.mk g := by
      rw [← splitInv_split m hn _ h hm (PolyQuot.mk f), toR_injective hxy,
        splitInv_split m hn _ h hm]
    rw [PolyQuot.mk_injective hmk]
  · intro y
    have hb : ∀ i, ∃ b : Poly F d, Poly.toR (Poly.binomial (γ i)) b = y i :=
      fun i => Poly.toR_surjective _ (y i)
    choose b hb using hb
    refine ⟨Poly.toR (Poly.binomial c) (PolyQuot.poly (splitInv m (ofFn b : Residues.Binomial F d m γ) (fun _ => c) hn
      (Nat.one_mul _).symm)), ?_⟩
    rw [crtHom_toR, split_splitInv m hn _ h hm]
    funext i
    rw [toR, apply_ofFn, hb]

/-- The Chinese remainder isomorphism `F[X]/(X^n - c) ≃+* ∏ᵢ F[X]/(X^d - γᵢ)`. -/
def crtEquiv [NeZero n] [NeZero d] [NeZero m] (hn : n = m * d) (hm : (m : F) ≠ 0)
    (h : SplitPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    R F n (Poly.binomial c) ≃+* ∀ i, R F d (Poly.binomial (γ i)) :=
  RingEquiv.ofBijective _ (crtHom_bijective hn hm h)

end Equiv

end Residues

end

end Wychelean.PolyRing
