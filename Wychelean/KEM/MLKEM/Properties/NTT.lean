import Wychelean.KEM.MLKEM.Properties.NTTEquivalence

/-! FIPS 203 §4.3: the NTT is a ring isomorphism `R_q ≃ T_q` computing the residues (4.12). -/

namespace Wychelean.KEM.MLKEM

open Wychelean.Utils.PolyRing
open _root_.Wychelean.KEM.MLKEM.Polynomial (NTT)
open Tq (NTTInv)

-- The FIPS loops are related to the folds by `Properties/Loops.lean`, never by unfolding.
attribute [local irreducible] Polynomial.NTT Tq.NTTInv MultiplyNTTs

/-- Algorithm 9 computes the ordered residues modulo `X² - ζ^(2·BitRev₇(i) + 1)`. -/
theorem ntt_eq_nttSpec (f : Polynomial) : Tq.toAbstract (NTT f) =
    Utils.PolyRing.NTT.nttSpec ζRoot f.toPolyMod (by decide) :=
  (toAbstract_ntt f).trans (Utils.PolyRing.NTT.ntt_eq_nttSpec 7 ζRoot f.toPolyMod (by decide))

/-- FIPS 203 §4.3: multiplication in `T_q` (Algorithms 11–12) implements multiplication in `R_q`. -/
theorem nttInv_mul (f g : Polynomial) : NTTInv (NTT f * NTT g) = f * g :=
  by rw [← nttEquiv_apply f, ← nttEquiv_apply g, ← map_mul, nttEquiv_apply, nttInv_ntt]

/-- FIPS 203 Algorithms 11–12: residue `i` of `f̂ · ĝ` is the base-case product at
`γ = ζ^(2·BitRev₇(i) + 1)`. -/
theorem mul_residue («f̂» «ĝ» : Tq) (i : Fin 128) :
    («f̂» * «ĝ») i = ⟨#v[(«f̂» i)[0] * («ĝ» i)[0] + («f̂» i)[1] * («ĝ» i)[1] * ζ ^ (2 * bitRev 7 i + 1),
                       («f̂» i)[0] * («ĝ» i)[1] + («f̂» i)[1] * («ĝ» i)[0]]⟩ :=
  by
    have h := congrArg (fun a : AbstractTq => a i) (Tq.toAbstract_mul «f̂» «ĝ»)
    have hm := Residues.mul_two (Tq.toAbstract «f̂») (Tq.toAbstract «ĝ») i
    have hc := h.trans hm
    have e (a : Tq) (i : Fin 128) : Residues.residue a.toAbstract i = a i := Tq.toAbstract_apply a i
    simp only [Utils.PolyRing.NTT.points, Utils.PolyRing.NTT.point] at hc
    simp only [← e]
    exact hc

/-- Characterisation of NTT outputs by coefficient sums. -/
theorem ntt_eq_iff (f : Polynomial) (a : Tq) :
    NTT f = a ↔ ∀ (i : Fin 128) (x : ℕ) (hx : x < 2),
      (a i)[x]'hx = ∑ t : Fin 128,
        f[x + 2 * t.val]'(by omega) * (ζ ^ (2 * bitRev 7 i + 1)) ^ t.val :=
  by
    have h : NTT f = a ↔ Tq.toAbstract (NTT f) = Tq.toAbstract a :=
      Tq.toAbstract_injective.eq_iff.symm
    rw [toAbstract_ntt] at h
    refine h.trans ?_
    have hc := Utils.PolyRing.NTT.ntt_eq_iff' (n := 256) (levels := 7) ζRoot (d := 2)
      rfl f.toPolyMod (by decide) (Tq.toAbstract a)
    have e (i : Fin 128) : Residues.residue a.toAbstract i = a i := Tq.toAbstract_apply a i
    simp only [e, Polynomial.getElem_toPolyMod, Utils.PolyRing.NTT.point, ζRoot_val] at hc
    exact hc

theorem nttInv_eq_iff (a : Tq) (f : Polynomial) : NTTInv a = f ↔ NTT f = a :=
  by
    constructor
    · intro h; rw [← h, ntt_nttInv]
    · intro h; rw [← h, nttInv_ntt]

/-- Quotient characterization: each ordered component is the image under the quotient map. -/
theorem ntt_eq_iff_toR (f : Polynomial) (a : Tq) :
    NTT f = a ↔ ∀ i : Fin 128, a.toAbstract.toR i =
      R.reduceBinomial 128 2 (by decide) (Utils.PolyRing.NTT.point ζ 7 i.val)
        (Utils.PolyRing.NTT.root_layerPoints ζRoot i)
        (Poly.toR (Poly.binomial (-1)) f.toPolyMod.poly) := by
  have h : NTT f = a ↔ Tq.toAbstract (NTT f) = Tq.toAbstract a :=
    Tq.toAbstract_injective.eq_iff.symm
  rw [toAbstract_ntt] at h
  exact h.trans (Utils.PolyRing.NTT.ntt_eq_iff_toR (n := 256) (levels := 7) ζRoot f.toPolyMod
    (by decide) a.toAbstract)

@[simp] theorem ntt_add (f g : Polynomial) : NTT (f + g) = NTT f + NTT g := by
  have h := map_add nttEquiv f g
  rw [nttEquiv_apply, nttEquiv_apply, nttEquiv_apply] at h
  exact h
@[simp] theorem ntt_sub (f g : Polynomial) : NTT (f - g) = NTT f - NTT g := by
  have h := map_sub nttEquiv f g
  rw [nttEquiv_apply, nttEquiv_apply, nttEquiv_apply] at h
  exact h
@[simp] theorem ntt_neg (f : Polynomial) : NTT (-f) = -NTT f := by
  have h := map_neg nttEquiv f
  rw [nttEquiv_apply, nttEquiv_apply] at h
  exact h
@[simp] theorem ntt_zero : NTT 0 = 0 := by
  have h := map_zero nttEquiv
  rw [nttEquiv_apply] at h
  exact h
@[simp] theorem ntt_one : NTT 1 = 1 := by
  have h := map_one nttEquiv
  rw [nttEquiv_apply] at h
  exact h
@[simp] theorem ntt_mul (f g : Polynomial) : NTT (f * g) = NTT f * NTT g := by
  have h := map_mul nttEquiv f g
  rw [nttEquiv_apply, nttEquiv_apply, nttEquiv_apply] at h
  exact h

theorem ntt_smul (c : Zq) (f : Polynomial) : NTT (c • f) = c • NTT f := by
  apply Tq.toAbstract_injective
  simp only [toAbstract_ntt, Tq.toAbstract_smul, abstractNTT, Polynomial.toPolyMod_smul,
    Utils.PolyRing.NTT.ntt_eq_nttSpec, Utils.PolyRing.NTT.nttSpec]
  exact Residues.split_smul ..

end Wychelean.KEM.MLKEM
