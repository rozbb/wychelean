import Wychelean.PolyRing.NTTProperties

/-!
The cyclic ring `F[X]/(X^n - 1)`: its complete split at a primitive `2^levels`-th root of unity
`ζ` has the points `ζ^BitRev(i)`, an instance of the same layer machinery as the negacyclic
transform of FIPS 203/204.
-/

namespace Wychelean.PolyRing.NTT.Cyclic

variable {F : Type*} [CommRing F] {n levels : ℕ}

/-- The `i`-th point, `ζ^BitRev(i)`. -/
def point (ζ : F) (levels i : ℕ) : F := ζ ^ bitRev levels i

abbrev points (ζ : F) (levels : ℕ) : Fin (2 ^ levels) → F := fun i => point ζ levels i

/-- The points are `2^levels`-th roots of unity. -/
theorem layerPoints (ζ : PrimitiveRoot F (2 ^ levels)) :
    Residues.LayerPoints (2 ^ levels) (fun _ : Fin 1 => (1 : F)) (points ζ.val levels)
      (Nat.one_mul _).symm := by
  intro j
  show point ζ.val levels j ^ 2 ^ levels = 1
  rw [point, ← pow_mul, mul_comm, pow_mul, ζ.2.pow_eq_one, one_pow]

/-- The points are all the `2^levels`-th roots of unity, in bit-reversed order. -/
theorem splitPoints [IsDomain F] (ζ : PrimitiveRoot F (2 ^ levels)) :
    Residues.SplitPoints (2 ^ levels) (fun _ : Fin 1 => (1 : F)) (points ζ.val levels)
      (Nat.one_mul _).symm := by
  intro i
  refine ⟨one_ne_zero, ζ.val, 1, bitRevPerm levels, ζ.2, one_pow _, fun k => ?_⟩
  show point ζ.val levels (k + 2 ^ levels * i) = 1 * ζ.val ^ (bitRevPerm levels k).val
  rw [Fin.fin_one_eq_zero i]
  simp only [point, bitRevPerm_apply_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, one_mul]

/-- The residues of `f` modulo the `X - ζ^BitRev(i)` (`n = 2^levels`) or the
`X^d - ζ^BitRev(i)` in general. -/
def ntt (ζ : PrimitiveRoot F (2 ^ levels)) (f : PolyMod F n 1) (hL : 2 ^ levels ∣ n) :
    Residues F (n / 2 ^ levels) (2 ^ levels) (points ζ.val levels) :=
  Residues.split (2 ^ levels) f (points ζ.val levels) (blockSize_mul hL) (Nat.one_mul _).symm

theorem ntt_mul [IsDomain F] (ζ : PrimitiveRoot F (2 ^ levels)) (f g : PolyMod F n 1)
    (hL : 2 ^ levels ∣ n) : ntt ζ (f * g) hL = ntt ζ f hL * ntt ζ g hL :=
  Residues.split_mul (2 ^ levels) f (blockSize_mul hL) (Nat.one_mul _).symm (layerPoints ζ) g

end Wychelean.PolyRing.NTT.Cyclic

namespace Wychelean.PolyRing.NTT.Cyclic

variable {F : Type*} [Field F] {n levels : ℕ}

def nttInv (ζ : PrimitiveRoot F (2 ^ levels))
    (a : Residues F (n / 2 ^ levels) (2 ^ levels) (points ζ.val levels)) (hL : 2 ^ levels ∣ n) :
    PolyMod F n 1 :=
  Residues.splitInv (2 ^ levels) a (fun _ => 1) (blockSize_mul hL) (Nat.one_mul _).symm

theorem nttInv_ntt (ζ : PrimitiveRoot F (2 ^ levels)) (h2 : ((2 ^ levels : ℕ) : F) ≠ 0)
    (f : PolyMod F n 1) (hL : 2 ^ levels ∣ n) : nttInv ζ (ntt ζ f hL) hL = f :=
  Residues.splitInv_split (2 ^ levels) (blockSize_mul hL) (Nat.one_mul _).symm (splitPoints ζ) h2 f

theorem ntt_nttInv (ζ : PrimitiveRoot F (2 ^ levels)) (h2 : ((2 ^ levels : ℕ) : F) ≠ 0)
    (a : Residues F (n / 2 ^ levels) (2 ^ levels) (points ζ.val levels)) (hL : 2 ^ levels ∣ n) :
    ntt ζ (nttInv ζ a hL) hL = a :=
  Residues.split_splitInv (2 ^ levels) (blockSize_mul hL) (Nat.one_mul _).symm (splitPoints ζ) h2 a

end Wychelean.PolyRing.NTT.Cyclic
