import Wychelean.Utils.PolyRing.Refine

namespace Wychelean.Utils.PolyRing.Residues

open Polynomial

noncomputable section

variable {F : Type*} [CommRing F] {d m : ℕ}

/-! ### The modulus of a product of components -/

/-- The product of the component ideals' generators, `∏ᵢ (X^d + μᵢ)`. -/
def modulus (μ : Fin m → Poly F d) : F[X] := ∏ i, Poly.monicPoly (μ i)

@[simp] theorem modulus_one {n : ℕ} (μ₀ : Poly F n) : modulus (fun _ : Fin 1 => μ₀) = Poly.monicPoly μ₀ :=
  Fin.prod_univ_one _

variable {d' m' : ℕ} {μ : Fin m → Poly F d'} {μ' : Fin m' → Poly F d}

/-- The `r` components above residue `i` multiply to its component: the factorisation data of a
layer. -/
def BlockProd (r : ℕ) (μ : Fin m → Poly F d') (μ' : Fin m' → Poly F d) (hm : m' = m * r) : Prop :=
  ∀ i : Fin m, ∏ k : Fin r, Poly.monicPoly (μ' ⟨k + r * i, block_lt hm k.isLt i.isLt⟩) =
    Poly.monicPoly (μ i)

theorem BlockProd.layerDvd {r : ℕ} {hm : m' = m * r} (h : BlockProd r μ μ' hm) : LayerDvd r μ μ' hm := by
  intro j
  have hr : 0 < r := radix_pos hm j
  let i : Fin m := ⟨j.val / r, div_lt hm j.isLt⟩
  let k : Fin r := ⟨j.val % r, Nat.mod_lt _ hr⟩
  have hj : (⟨k.val + r * i.val, block_lt hm k.isLt i.isLt⟩ : Fin m') = j :=
    Fin.ext (Nat.mod_add_div _ _)
  have hdvd : Poly.monicPoly (μ' ⟨k.val + r * i.val, block_lt hm k.isLt i.isLt⟩) ∣
      ∏ t : Fin r, Poly.monicPoly (μ' ⟨t.val + r * i.val, block_lt hm t.isLt i.isLt⟩) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  rw [hj, h i] at hdvd
  exact hdvd

/-- A layer refines the factorisation of the same modulus. -/
theorem modulus_refine {r : ℕ} {hm : m' = m * r} (h : BlockProd r μ μ' hm) : modulus μ' = modulus μ := by
  subst hm
  rw [modulus, modulus, ← Fintype.prod_equiv finProdFinEquiv
    (fun p : Fin m × Fin r => Poly.monicPoly (μ' (finProdFinEquiv p))) _ (fun _ => rfl),
    Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun i _ => h i

/-! ### The canonical map to the product of the component quotients -/

variable {n : ℕ} {μ₀ : Poly F n} {μ : Fin m → Poly F d}

/-- `F[X]/(X^n + μ₀) → ∏ᵢ F[X]/(X^d + μᵢ)` when each component divides the modulus. -/
def crtHom (h : ∀ i, Poly.monicPoly (μ i) ∣ Poly.monicPoly μ₀) : R F n μ₀ →+* ∀ i, R F d (μ i) :=
  RingHom.pi fun i => R.reduce (h i)

/-- The computable one-shot layer tracks the canonical map. -/
theorem crtHom_toR (h : ∀ i, Poly.monicPoly (μ i) ∣ Poly.monicPoly μ₀) (f : PolyQuot F n μ₀) :
    crtHom h (Poly.toR μ₀ f.poly) = (refine m f μ (Nat.one_mul _).symm).toR := by
  funext i
  change R.reduce (h i) (Poly.toR μ₀ f.poly) = _
  rw [toR, refine_apply, PolyQuot.apply_eq_poly, Poly.toR_modMonic,
    Poly.toR_eq_mk, R.reduce_mk]

/-- The canonical map is bijective when the components are pairwise coprime and multiply to the
modulus. -/
theorem crtHom_bijective_of_coprime (hcop : Pairwise (fun i j : Fin m => IsCoprime (Poly.monicPoly (μ i)) (Poly.monicPoly (μ j))))
    (hprod : ∏ i, Poly.monicPoly (μ i) = Poly.monicPoly μ₀) :
    Function.Bijective (crtHom fun i => hprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using AdjoinRoot.induction_on with
    | ih g =>
      rw [AdjoinRoot.mk_eq_zero, ← hprod]
      refine Fintype.prod_dvd_of_coprime hcop fun i => ?_
      have := congrFun hx i
      rw [crtHom, RingHom.pi_apply, R.reduce_mk, Pi.zero_apply, AdjoinRoot.mk_eq_zero] at this
      exact this
  · intro y
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective
      (I := fun i => Ideal.span {Poly.monicPoly (μ i)})
      (fun i j hij => (Ideal.isCoprime_span_singleton_iff _ _).2 (hcop hij)) y
    refine ⟨AdjoinRoot.mk _ r, funext fun i => ?_⟩
    rw [crtHom, RingHom.pi_apply, R.reduce_mk]
    exact hr i

/-- The Chinese remainder isomorphism `F[X]/(X^n + μ₀) ≃+* ∏ᵢ F[X]/(X^d + μᵢ)` for pairwise
coprime components. -/
def crtEquivOfCoprime (hcop : Pairwise (fun i j : Fin m => IsCoprime (Poly.monicPoly (μ i)) (Poly.monicPoly (μ j))))
    (hprod : ∏ i, Poly.monicPoly (μ i) = Poly.monicPoly μ₀) : R F n μ₀ ≃+* ∀ i, R F d (μ i) :=
  RingEquiv.ofBijective _ (crtHom_bijective_of_coprime hcop hprod)

end

end Wychelean.Utils.PolyRing.Residues
