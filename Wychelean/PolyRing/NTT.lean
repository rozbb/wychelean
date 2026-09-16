import Wychelean.PolyRing.Split
import Wychelean.Utils.Bits
import Mathlib.GroupTheory.OrderOfElement

/-!
The number-theoretic transform of FIPS 203 §4.3 and FIPS 204 §7.5 on the negacyclic ring
`F[X]/(X^n + 1)`: `levels` radix-2 layers whose points are `ζ^(2·BitRev(i) + 1)` for a primitive
`2^(levels+1)`-th root of unity `ζ` (`ζ = 17` with seven layers for ML-KEM, `ζ = 1753` with eight
for ML-DSA). The root is carried with its proof, so the transform cannot be instantiated at an
arbitrary element. `ntt` is the Cooley–Tukey recursion (FIPS 203 Algorithm 9 / FIPS 204
Algorithm 41 as a fold of `Residues.split 2`), `nttSpec` the closed form (one layer of radix
`2^levels`), `nttSched` any schedule of radices `2^b`; `NTTProperties` proves them equal.
-/

namespace Wychelean.PolyRing

/-- A primitive `k`-th root of unity with its proof. -/
abbrev PrimitiveRoot (F : Type*) [CommMonoid F] (k : ℕ) := {ζ : F // IsPrimitiveRoot ζ k}

namespace PrimitiveRoot

variable {F : Type*} [CommRing F] {l : ℕ}

/-- `ζ²` is a primitive `2^l`-th root of unity when `ζ` is a primitive `2^(l+1)`-th one. -/
def sq (ζ : PrimitiveRoot F (2 ^ (l + 1))) : PrimitiveRoot F (2 ^ l) :=
  ⟨ζ.val ^ 2, ζ.2.pow (Nat.two_pow_pos _) (pow_succ' 2 l)⟩

@[simp] theorem sq_val (ζ : PrimitiveRoot F (2 ^ (l + 1))) : ζ.sq.val = ζ.val ^ 2 := rfl

/-- `ζ^(2^b)` is a primitive `2^k`-th root of unity when `ζ` is a primitive `2^(k+b)`-th one. -/
def pow2 {k' : ℕ} (b : ℕ) (ζ : PrimitiveRoot F (2 ^ k')) (k : ℕ) (h : k' = k + b) :
    PrimitiveRoot F (2 ^ k) :=
  ⟨ζ.val ^ 2 ^ b, ζ.2.pow (Nat.two_pow_pos _) (by rw [h, Nat.pow_add, Nat.mul_comm])⟩

@[simp] theorem pow2_val {k' : ℕ} (b : ℕ) (ζ : PrimitiveRoot F (2 ^ k')) (k : ℕ) (h : k' = k + b) :
    (ζ.pow2 b k h).val = ζ.val ^ 2 ^ b := rfl

theorem pow_ne_one (ζ : PrimitiveRoot F (2 ^ (l + 1))) : ζ.val ^ 2 ^ l ≠ 1 :=
  ζ.2.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos l))
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self l))

theorem pow_eq_neg_one [IsDomain F] (ζ : PrimitiveRoot F (2 ^ (l + 1))) : ζ.val ^ 2 ^ l = -1 :=
  (ζ.2.pow (Nat.two_pow_pos _) (pow_succ 2 l)).eq_neg_one_of_two_right

theorem neg_one_ne_one [IsDomain F] (ζ : PrimitiveRoot F (2 ^ (l + 1))) : (-1 : F) ≠ 1 :=
  ζ.pow_eq_neg_one ▸ ζ.pow_ne_one

theorem two_ne_zero [IsDomain F] (ζ : PrimitiveRoot F (2 ^ (l + 1))) : (2 : F) ≠ 0 := fun h =>
  ζ.neg_one_ne_one (by rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h])

theorem natCast_two_pow_ne_zero [IsDomain F] (ζ : PrimitiveRoot F (2 ^ (l + 1))) (b : ℕ) :
    ((2 ^ b : ℕ) : F) ≠ 0 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero _ ζ.two_ne_zero

theorem ne_zero [Nontrivial F] {k : ℕ} (ζ : PrimitiveRoot F k) (hk : k ≠ 0) : ζ.val ≠ 0 :=
  ζ.2.ne_zero hk

/-- A primitive `2^(l+1)`-th root of unity from `ζ^(2^l) = -1` and `-1 ≠ 1`: the check FIPS 203
Appendix A leaves to the reader for `ζ = 17`. -/
def ofPowEqNegOne (ζ : F) (h : ζ ^ 2 ^ l = -1) (h1 : (-1 : F) ≠ 1) :
    PrimitiveRoot F (2 ^ (l + 1)) :=
  ⟨ζ, by
    have hnot : ¬ ζ ^ 2 ^ l = 1 := by rw [h]; exact h1
    have hfin : ζ ^ 2 ^ (l + 1) = 1 := by rw [pow_succ, pow_mul, h, neg_one_sq]
    have := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime_pow hnot hfin] at this⟩

end PrimitiveRoot

namespace NTT

variable {F : Type*} [CommRing F] {n levels : ℕ}

/-- The `i`-th evaluation point after `levels` layers, `ζ^(2·BitRev(i) + 1)` (FIPS 203 §4.3). -/
def point (ζ : F) (levels i : ℕ) : F := ζ ^ (2 * bitRev levels i + 1)

abbrev points (ζ : F) (levels : ℕ) : Fin (2 ^ levels) → F := fun i => point ζ levels i

/-! ### Block sizes: `n / 2^levels` coefficients per residue -/

theorem blockSize_mul (hL : 2 ^ levels ∣ n) : n = 2 ^ levels * (n / 2 ^ levels) :=
  (Nat.mul_div_cancel' hL).symm

theorem blockSize_add {k k' b : ℕ} (h : k' = k + b) (hL : 2 ^ k' ∣ n) :
    n / 2 ^ k = 2 ^ b * (n / 2 ^ k') := by
  obtain ⟨q, rfl⟩ := hL
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), h, Nat.pow_add, Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

theorem blockSize_succ {l : ℕ} (hL : 2 ^ (l + 1) ∣ n) : n / 2 ^ l = 2 * (n / 2 ^ (l + 1)) := by
  rw [blockSize_add rfl hL, pow_one]

theorem two_pow_add {k k' b : ℕ} (h : k' = k + b) : 2 ^ k' = 2 ^ k * 2 ^ b := by
  rw [h, Nat.pow_add]

theorem dvd_of_le {k k' : ℕ} (h : k ≤ k') (hL : 2 ^ k' ∣ n) : 2 ^ k ∣ n :=
  (pow_dvd_pow 2 h).trans hL

theorem dvd_of_succ {l : ℕ} (hL : 2 ^ (l + 1) ∣ n) : 2 ^ l ∣ n :=
  dvd_of_le (Nat.le_succ l) hL

end NTT

/-- The NTT domain `T_q` after `levels` layers: `2^levels` residues of degree `n / 2^levels` at
the points `ζ^(2·BitRev(i) + 1)` (FIPS 203 §2.4.6 with `levels = 7`, FIPS 204 §7.5 with `8`). -/
abbrev NTTDomain {F : Type*} [CommRing F] (levels : ℕ) (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (n : ℕ) :=
  Residues F (n / 2 ^ levels) (2 ^ levels) (NTT.points ζ.val levels)

namespace NTT

variable {F : Type*} {n : ℕ}

section Forward

variable [CommRing F]

/-- The closed form: residue `i` is `f mod (X^d - point i)`, one layer of radix `2^levels`. -/
def nttSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (f : PolyMod F n (-1))
    (hL : 2 ^ levels ∣ n) : NTTDomain levels ζ n :=
  Residues.split (2 ^ levels) f (points ζ.val levels) (blockSize_mul hL) (Nat.one_mul _).symm

/-- FIPS 203 Algorithm 9 / FIPS 204 Algorithm 41 as `levels` Cooley–Tukey layers: layer `l + 1`
splits the residues of the transform at `ζ²` with `l` layers, at the points of `ζ`. -/
def ntt : (levels : ℕ) → (ζ : PrimitiveRoot F (2 ^ (levels + 1))) → (f : PolyMod F n (-1)) →
    2 ^ levels ∣ n → NTTDomain levels ζ n
  | 0, ζ, f, hL => nttSpec ζ f hL
  | l + 1, ζ, f, hL =>
    Residues.split 2 (ntt l ζ.sq f (dvd_of_succ hL)) (points ζ.val (l + 1)) (blockSize_succ hL)
      (pow_succ 2 l)

/-- Any schedule: after `l` levels in one shot, one layer of radix `2^b` for each `b` in `bs`
(innermost first). `nttSched [] levels` is `nttSpec`; `nttSched [1, …, 1] 0` is `ntt`. -/
def nttSched : (bs : List ℕ) → (l : ℕ) → (ζ : PrimitiveRoot F (2 ^ (l + bs.sum + 1))) →
    (f : PolyMod F n (-1)) → 2 ^ (l + bs.sum) ∣ n → NTTDomain (l + bs.sum) ζ n
  | [], _, ζ, f, hL => nttSpec ζ f hL
  | b :: bs, l, ζ, f, hL =>
    Residues.split (2 ^ b)
      (nttSched bs l (ζ.pow2 b (l + bs.sum + 1) (by simp only [List.sum_cons]; omega)) f
        (dvd_of_le (by simp only [List.sum_cons]; omega) hL))
      (points ζ.val (l + (b :: bs).sum)) (blockSize_add (by simp only [List.sum_cons]; omega) hL)
      (two_pow_add (by simp only [List.sum_cons]; omega))

end Forward

section Inverse

variable [Field F]

/-- The inverse of the closed form. -/
def nttInvSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (a : NTTDomain levels ζ n)
    (hL : 2 ^ levels ∣ n) : PolyMod F n (-1) :=
  Residues.splitInv (2 ^ levels) a (fun _ => -1) (blockSize_mul hL) (Nat.one_mul _).symm

/-- FIPS 203 Algorithm 10 / FIPS 204 Algorithm 42 as `levels` Gentleman–Sande layers. -/
def nttInv : (levels : ℕ) → (ζ : PrimitiveRoot F (2 ^ (levels + 1))) →
    NTTDomain levels ζ n → 2 ^ levels ∣ n → PolyMod F n (-1)
  | 0, ζ, a, hL => nttInvSpec ζ a hL
  | l + 1, ζ, a, hL =>
    nttInv l ζ.sq
      (Residues.splitInv 2 a (points ζ.sq.val l) (blockSize_succ hL) (pow_succ 2 l))
      (dvd_of_succ hL)

/-- The inverse of a schedule, layer by layer. -/
def nttInvSched : (bs : List ℕ) → (l : ℕ) → (ζ : PrimitiveRoot F (2 ^ (l + bs.sum + 1))) →
    NTTDomain (l + bs.sum) ζ n → 2 ^ (l + bs.sum) ∣ n → PolyMod F n (-1)
  | [], _, ζ, a, hL => nttInvSpec ζ a hL
  | b :: bs, l, ζ, a, hL =>
    nttInvSched bs l (ζ.pow2 b (l + bs.sum + 1) (by simp only [List.sum_cons]; omega))
      (Residues.splitInv (2 ^ b) a (points (ζ.val ^ 2 ^ b) (l + bs.sum))
        (blockSize_add (by simp only [List.sum_cons]; omega) hL)
        (two_pow_add (by simp only [List.sum_cons]; omega)))
      (dvd_of_le (by simp only [List.sum_cons]; omega) hL)

end Inverse

end NTT

section Methods

variable {F : Type*} {n levels : ℕ}

section Forward

variable [CommRing F] {ζ : PrimitiveRoot F (2 ^ (levels + 1))}

/-- `f.ntt`, the transform with the root and depth of the target type. -/
abbrev PolyMod.ntt (f : PolyMod F n (-1)) [h : Fact (2 ^ levels ∣ n)] : NTTDomain levels ζ n :=
  NTT.ntt levels ζ f h.out

/-- A vector of `k` NTT-domain elements (FIPS 203 §2.4.7). -/
abbrev NTTVec (levels : ℕ) (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (n k : ℕ) :=
  Vector (NTTDomain levels ζ n) k

/-- The transform of every entry. -/
def PolyVec.ntt {k : ℕ} (v : PolyVec F n (-1) k) [Fact (2 ^ levels ∣ n)] : NTTVec levels ζ n k :=
  v.map (·.ntt)

end Forward

section Inverse

variable [Field F] {ζ : PrimitiveRoot F (2 ^ (levels + 1))}

/-- `f̂.nttInv : PolyMod F n (-1)`, the inverse transform. -/
abbrev NTTDomain.nttInv [h : Fact (2 ^ levels ∣ n)] (a : NTTDomain levels ζ n) : PolyMod F n (-1) :=
  NTT.nttInv levels ζ a h.out

def NTTVec.nttInv {k : ℕ} [Fact (2 ^ levels ∣ n)] (v : NTTVec levels ζ n k) : PolyVec F n (-1) k :=
  v.map (·.nttInv)

end Inverse

end Methods

end Wychelean.PolyRing
