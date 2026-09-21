import Wychelean.KEM.MLKEM.Basic
import Wychelean.KEM.MLKEM.NTTEquivalence

namespace Wychelean.KEM.MLKEM

open Wychelean.Utils.PolyRing

/-- Algorithm 9 computes the ordered residues modulo `X² - ζ^(2·BitRev₇(i) + 1)`. -/
theorem ntt_eq_nttSpec (f : Polynomial) : Tq.toAbstract f.ntt =
    Utils.PolyRing.NTT.nttSpec ζ f (by decide) :=
  (toAbstract_ntt f).trans (Utils.PolyRing.NTT.ntt_eq_nttSpec 7 ζ f (by decide))

/-- FIPS 203 §4.3: multiplication in `T_q` (Algorithms 11–12) implements multiplication in `R_q`. -/
theorem nttInv_mul (f g : Polynomial) : (f.ntt * g.ntt : Tq).nttInv = f * g :=
  by rw [← nttEquiv_apply f, ← nttEquiv_apply g, ← map_mul, nttEquiv_apply, nttInv_ntt]

/-- FIPS 203 Algorithms 11–12: residue `i` of `f̂ · ĝ` is the base-case product at
`γ = ζ^(2·BitRev₇(i) + 1)`. -/
theorem mul_residue («f̂» «ĝ» : Tq) (i : Fin 128) :
    («f̂» * «ĝ») i = ⟨#v[(«f̂» i)[0] * («ĝ» i)[0] + («f̂» i)[1] * («ĝ» i)[1] * ζ.val ^ (2 * bitRev 7 i + 1),
                       («f̂» i)[0] * («ĝ» i)[1] + («f̂» i)[1] * («ĝ» i)[0]]⟩ :=
  by
    have h := congrArg (fun a : AbstractTq => a i) (Tq.toAbstract_mul «f̂» «ĝ»)
    have hm := Residues.mul_two (Tq.toAbstract «f̂») (Tq.toAbstract «ĝ») i
    have hc := h.trans hm
    simp only [Tq.toAbstract_apply] at hc
    exact hc

/-- Characterisation of NTT outputs by coefficient sums. -/
theorem ntt_eq_iff (f : Polynomial) (a : Tq) :
    f.ntt = a ↔ ∀ (i : Fin 128) (x : ℕ) (hx : x < 2),
      (a i)[x]'hx = ∑ t : Fin 128,
        f[x + 2 * t.val]'(by omega) * (ζ.val ^ (2 * bitRev 7 i + 1)) ^ t.val :=
  by
    have h : f.ntt = a ↔ Tq.toAbstract f.ntt = Tq.toAbstract a :=
      Tq.toAbstract_injective.eq_iff.symm
    rw [toAbstract_ntt] at h
    refine h.trans ?_
    have hc := Utils.PolyRing.NTT.ntt_eq_iff' (n := 256) (levels := 7) ζ (d := 2)
      rfl f (by decide) (Tq.toAbstract a)
    simp only [Tq.toAbstract_apply] at hc
    exact hc

theorem nttInv_eq_iff (a : Tq) (f : Polynomial) : a.nttInv = f ↔ f.ntt = a :=
  by
    constructor
    · intro h; rw [← h, ntt_nttInv]
    · intro h; rw [← h, nttInv_ntt]

/-- Quotient characterization: each ordered component is the image under the quotient map. -/
theorem ntt_eq_iff_toR (f : Polynomial) (a : Tq) :
    f.ntt = a ↔ ∀ i : Fin 128, a.toAbstract.toR i =
      R.reduceBinomial 128 2 (by decide) (Utils.PolyRing.NTT.point ζ.val 7 i.val)
        (Utils.PolyRing.NTT.root_layerPoints ζ i) (Poly.toR (Poly.binomial (-1)) f.poly) := by
  have h : f.ntt = a ↔ Tq.toAbstract f.ntt = Tq.toAbstract a :=
    Tq.toAbstract_injective.eq_iff.symm
  rw [toAbstract_ntt] at h
  exact h.trans (Utils.PolyRing.NTT.ntt_eq_iff_toR (n := 256) (levels := 7) ζ f (by decide) a.toAbstract)

@[simp] theorem ntt_add (f g : Polynomial) : (f + g).ntt = f.ntt + g.ntt := nttEquiv.map_add f g
@[simp] theorem ntt_sub (f g : Polynomial) : (f - g).ntt = f.ntt - g.ntt := nttEquiv.map_sub f g
@[simp] theorem ntt_neg (f : Polynomial) : (-f).ntt = -f.ntt := nttEquiv.map_neg f
@[simp] theorem ntt_zero : (0 : Polynomial).ntt = 0 := nttEquiv.map_zero
@[simp] theorem ntt_one : (1 : Polynomial).ntt = 1 := nttEquiv.map_one
@[simp] theorem ntt_mul (f g : Polynomial) : (f * g).ntt = f.ntt * g.ntt := nttEquiv.map_mul f g

theorem ntt_smul (c : Zq) (f : Polynomial) : (c • f).ntt = c • f.ntt := by
  apply Tq.toAbstract_injective
  simp only [toAbstract_ntt, Tq.toAbstract_smul, abstractNTT,
    Utils.PolyRing.NTT.ntt_eq_nttSpec, Utils.PolyRing.NTT.nttSpec]
  exact Residues.split_smul ..

end Wychelean.KEM.MLKEM
