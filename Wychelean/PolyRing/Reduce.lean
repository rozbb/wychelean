import Wychelean.PolyRing.Poly
import Mathlib.Data.ZMod.ValMinAbs

/-!
Reduction modulo `q` and the centred lift between `ℤ[X]` and `ℤ_q[X]` coefficient vectors
(FIPS 204 §2.3, `mod±`). Both respect the wrap-around product, so they connect
`ℤ[X]/(X^n - c)` with `ℤ_q[X]/(X^n - c)`.
-/

namespace Wychelean.PolyRing.Poly

variable {n : ℕ} (q : ℕ)

/-- Coefficient-wise reduction modulo `q`. -/
def reduce (f : Poly ℤ n) : Poly (ZMod q) n := ⟨f.coeffs.map Int.cast⟩

@[simp] theorem getElem_reduce (f : Poly ℤ n) (i : ℕ) (hi : i < n) :
    (reduce q f)[i] = (f[i] : ZMod q) :=
  Vector.getElem_map ..

theorem reduce_add (f g : Poly ℤ n) : reduce q (f + g) = reduce q f + reduce q g := by
  ext i hi; simp

theorem reduce_mulMod (c : ℤ) (f g : Poly ℤ n) :
    reduce q (mulMod c f g) = mulMod (c : ZMod q) (reduce q f) (reduce q g) := by
  ext i hi
  simp only [getElem_reduce, getElem_mulMod, Fin.getElem_fin]
  push_cast
  rfl

theorem reduce_surjective [NeZero q] : Function.Surjective (reduce q : Poly ℤ n → Poly (ZMod q) n) :=
  fun g => ⟨⟨g.coeffs.map fun x => x.val⟩, by
    ext i hi
    simp only [getElem_reduce, getElem_mk, Vector.getElem_map, Int.cast_natCast]
    exact ZMod.natCast_zmod_val _⟩

/-- The kernel of `reduce q` is the multiples of `q`. -/
theorem reduce_eq_zero_iff (f : Poly ℤ n) :
    reduce q f = 0 ↔ ∀ (i : ℕ) (hi : i < n), (q : ℤ) ∣ f[i] := by
  constructor
  · intro h i hi
    have := congrArg (fun p : Poly (ZMod q) n => p[i]) h
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  · intro h
    ext i hi
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h i hi

/-- The centred lift, coefficient-wise `mod±`: representatives in `(-q/2, q/2]`. -/
def lift (f : Poly (ZMod q) n) : Poly ℤ n := ⟨f.coeffs.map ZMod.valMinAbs⟩

@[simp] theorem getElem_lift (f : Poly (ZMod q) n) (i : ℕ) (hi : i < n) :
    (lift q f)[i] = f[i].valMinAbs :=
  Vector.getElem_map ..

theorem reduce_lift (f : Poly (ZMod q) n) : reduce q (lift q f) = f := by
  ext i hi
  simp [ZMod.coe_valMinAbs]

theorem lift_injective : Function.Injective (lift q : Poly (ZMod q) n → Poly ℤ n) :=
  fun f g h => by rw [← reduce_lift q f, h, reduce_lift]

theorem lift_zero : lift q (0 : Poly (ZMod q) n) = 0 := by
  ext i hi
  simp [ZMod.valMinAbs_zero]

/-- Every lifted coefficient has absolute value at most `q / 2`. -/
theorem natAbs_getElem_lift_le [NeZero q] (f : Poly (ZMod q) n) (i : ℕ) (hi : i < n) :
    (lift q f)[i].natAbs ≤ q / 2 := by
  rw [getElem_lift]
  exact ZMod.natAbs_valMinAbs_le _

end Wychelean.PolyRing.Poly
