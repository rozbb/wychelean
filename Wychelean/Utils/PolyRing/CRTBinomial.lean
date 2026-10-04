import Wychelean.Utils.PolyRing.CRT
import Wychelean.Utils.PolyRing.SplitProperties
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.KummerExtension

namespace Wychelean.Utils.PolyRing.Residues.Binomial

open Polynomial

noncomputable section

variable {F : Type*} [CommRing F] {d m : ℕ}

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

/-- A split layer's blocks multiply to the binomials above them. -/
theorem splitPoints_blockProd [IsDomain F] {r m' d' : ℕ} {γ : Fin m → F} {γ' : Fin m' → F}
    (hd : d' = r * d) (hm : m' = m * r) (h : SplitPoints r γ γ' hm) (hr : 0 < r) :
    BlockProd r (fun i => (Poly.binomial (γ i) : Poly F d')) (fun j => (Poly.binomial (γ' j) : Poly F d))
      hm := by
  intro i
  obtain ⟨_, ω, δ, σ, hω, hδ, hpts⟩ := h i
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · have hd' : d' = 0 := by omega
    subst hd'
    simp [Poly.monicPoly_zero_deg]
  · have : NeZero d := ⟨hd0.ne'⟩
    have : NeZero d' := ⟨hd ▸ Nat.mul_ne_zero hr.ne' hd0.ne'⟩
    simp only [Poly.monicPoly_binomial]
    rw [hd, ← prod_block hr hω hδ σ]
    exact Finset.prod_congr rfl fun k _ => by rw [hpts k]

/-- A layer refines the factorisation of the same modulus. -/
theorem modulus_split [IsDomain F] {r m' d' : ℕ} {γ : Fin m → F} {γ' : Fin m' → F}
    (hd : d' = r * d) (hm : m' = m * r) (h : SplitPoints r γ γ' hm) (hr : 0 < r) :
    modulus (fun j => (Poly.binomial (γ' j) : Poly F d)) = modulus (fun i => (Poly.binomial (γ i) : Poly F d')) :=
  modulus_refine (splitPoints_blockProd hd hm h hr)

variable {n : ℕ} {c : F} {γ : Fin m → F}

/-- `F[X]/(X^n - c) → ∏ᵢ F[X]/(X^d - γᵢ)` when the `γᵢ` are `m`-th roots of `c`. -/
def crtHom [NeZero m] (hn : n = m * d) (h : LayerPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    R F n (Poly.binomial c) →+* ∀ i, R F d (Poly.binomial (γ i)) :=
  Residues.crtHom (μ₀ := Poly.binomial c) (μ := fun i => Poly.binomial (γ i))
    fun i => Poly.monicPoly_binomial_dvd hn (h i)

/-- The computable one-shot layer tracks the canonical map. -/
theorem crtHom_toR [NeZero m] (hn : n = m * d)
    (h : LayerPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) (f : PolyMod F n c) :
    crtHom hn h (Poly.toR (Poly.binomial c) f.poly) = (split m f γ hn (Nat.one_mul _).symm).toR := by
  rw [crtHom, Residues.crtHom_toR, split_eq_refine]

end

section Equiv

variable {F : Type*} [Field F] {n d m : ℕ} {c : F} {γ : Fin m → F}

theorem crtHom_bijective [NeZero n] [NeZero d] [NeZero m] (hn : n = m * d) (hm : (m : F) ≠ 0)
    (h : SplitPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    Function.Bijective (crtHom hn h.layerPoints) := by
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := Poly.toR_surjective (Poly.binomial c) x
    obtain ⟨g, rfl⟩ := Poly.toR_surjective (Poly.binomial c) y
    rw [← PolyQuot.poly_mk (μ := Poly.binomial c) f, ← PolyQuot.poly_mk (μ := Poly.binomial c) g,
      crtHom_toR, crtHom_toR] at hxy
    have hmk : (PolyQuot.mk f : PolyMod F n c) = PolyQuot.mk g := by
      rw [← splitInv_split m hn _ h hm (PolyQuot.mk f), toR_injective hxy,
        splitInv_split m hn _ h hm]
    rw [PolyQuot.mk_injective hmk]
  · intro y
    have hb : ∀ i, ∃ b : Poly F d, Poly.toR (Poly.binomial (γ i)) b = y i :=
      fun i => Poly.toR_surjective _ (y i)
    choose b hb using hb
    refine ⟨Poly.toR (Poly.binomial c) (PolyQuot.poly (splitInv m (ofFn b : Residues.Binomial F d m γ)
      (fun _ => c) hn (Nat.one_mul _).symm)), ?_⟩
    rw [crtHom_toR, split_splitInv m hn _ h hm]
    funext i
    rw [toR, apply_ofFn, hb]

/-- The Chinese remainder isomorphism `F[X]/(X^n - c) ≃+* ∏ᵢ F[X]/(X^d - γᵢ)`. -/
noncomputable def crtEquiv [NeZero n] [NeZero d] [NeZero m] (hn : n = m * d) (hm : (m : F) ≠ 0)
    (h : SplitPoints m (fun _ : Fin 1 => c) γ (Nat.one_mul _).symm) :
    R F n (Poly.binomial c) ≃+* ∀ i, R F d (Poly.binomial (γ i)) :=
  RingEquiv.ofBijective _ (crtHom_bijective hn hm h)

end Equiv

end Wychelean.Utils.PolyRing.Residues.Binomial
