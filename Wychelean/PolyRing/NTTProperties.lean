import Wychelean.PolyRing.NTT
import Wychelean.PolyRing.SplitProperties

/-!
The bit-reversed point tables of FIPS 203 §4.3 satisfy the layer hypotheses, so the Cooley–Tukey
recursion `ntt` and every schedule `nttSched` equal the closed form `nttSpec`, which is
multiplicative and inverted by `nttInvSpec`/`nttInv`. The `ntt_eq_iff` family characterises the
transform for a consumer holding a candidate output: coefficient sums, divisibility of
representatives, images in the quotient rings, or evaluation when the split is complete.
-/

namespace Wychelean.PolyRing.NTT

open Polynomial Residues

variable {F : Type*} {n : ℕ}

/-! ### The point tables as layers -/

section Points

variable [CommRing F]

/-- The points of a radix-`2^b` layer are `2^b`-th roots of the points above:
`point ζ (l+b) j ^ (2^b) = point (ζ^(2^b)) l (j / 2^b)`. -/
theorem point_pow_layer {l b : ℕ} (ζ : PrimitiveRoot F (2 ^ (l + b + 1))) (j : ℕ) :
    point ζ.val (l + b) j ^ 2 ^ b = point (ζ.val ^ 2 ^ b) l (j / 2 ^ b) := by
  simp only [point, ← pow_mul, bitRev_add]
  rw [show (2 * (bitRev l (j / 2 ^ b) + 2 ^ l * bitRev b (j % 2 ^ b)) + 1) * 2 ^ b =
      2 ^ b * (2 * bitRev l (j / 2 ^ b) + 1) + 2 ^ (l + b + 1) * bitRev b (j % 2 ^ b) by ring,
    pow_add, pow_mul, pow_mul, ζ.2.pow_eq_one, one_pow, mul_one]

theorem points_layerPoints {l b k : ℕ} (h : k = l + b) (ζ : PrimitiveRoot F (2 ^ (k + 1))) :
    LayerPoints (2 ^ b) (points (ζ.val ^ 2 ^ b) l) (points ζ.val k) (two_pow_add h) := by
  subst h
  exact fun j => point_pow_layer ζ j

theorem points_layerPoints_succ {l : ℕ} (ζ : PrimitiveRoot F (2 ^ (l + 1 + 1))) :
    LayerPoints 2 (points ζ.sq.val l) (points ζ.val (l + 1)) (pow_succ 2 l) := by
  have := points_layerPoints (b := 1) rfl ζ
  simp only [pow_one] at this
  exact this

/-- The root ring `F[X]/(X^n + 1)` as the one-component product: its points are `2^levels`-th
roots of `-1`. -/
theorem root_layerPoints [IsDomain F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) :
    LayerPoints (2 ^ levels) (fun _ : Fin 1 => (-1 : F)) (points ζ.val levels) (Nat.one_mul _).symm := by
  intro j
  show point ζ.val levels j ^ 2 ^ levels = -1
  rw [point, ← pow_mul, mul_comm, pow_mul, ζ.pow_eq_neg_one]
  exact Odd.neg_one_pow ⟨_, rfl⟩

/-- The bit-reversal permutation of `Fin (2^b)`. -/
def bitRevPerm (b : ℕ) : Fin (2 ^ b) ≃ Fin (2 ^ b) :=
  Function.Involutive.toPerm (fun i => ⟨bitRev b i, bitRev_lt _ _⟩)
    fun i => Fin.ext (bitRev_bitRev _ _ i.isLt)

@[simp] theorem bitRevPerm_apply_val (b : ℕ) (i : Fin (2 ^ b)) : (bitRevPerm b i).val = bitRev b i := rfl

theorem points_splitPoints [IsDomain F] {l b k : ℕ} (h : k = l + b)
    (ζ : PrimitiveRoot F (2 ^ (k + 1))) :
    SplitPoints (2 ^ b) (points (ζ.val ^ 2 ^ b) l) (points ζ.val k) (two_pow_add h) := by
  subst h
  intro i
  refine ⟨?_, ζ.val ^ 2 ^ (l + 1), point ζ.val (l + b) (2 ^ b * i), bitRevPerm b, ?_, ?_, ?_⟩
  · exact pow_ne_zero _ (pow_ne_zero _ (ζ.ne_zero (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))))
  · exact ζ.2.pow (Nat.two_pow_pos _) (by rw [← Nat.pow_add]; congr 1; omega)
  · rw [point_pow_layer ζ, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  · intro k
    show point ζ.val (l + b) (k + 2 ^ b * i) =
      point ζ.val (l + b) (2 ^ b * i) * (ζ.val ^ 2 ^ (l + 1)) ^ (bitRevPerm b k).val
    simp only [point, bitRevPerm_apply_val, bitRev_add, block_div (Nat.two_pow_pos b) k.isLt,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt, Nat.mul_div_cancel_left _ (Nat.two_pow_pos b),
      Nat.mul_mod_right, bitRev_zero_right, ← pow_mul, ← pow_add]
    congr 1
    ring

theorem points_splitPoints_succ [IsDomain F] {l : ℕ} (ζ : PrimitiveRoot F (2 ^ (l + 1 + 1))) :
    SplitPoints 2 (points ζ.sq.val l) (points ζ.val (l + 1)) (pow_succ 2 l) := by
  have := points_splitPoints (b := 1) rfl ζ
  simp only [pow_one] at this
  exact this

theorem root_splitPoints [IsDomain F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) :
    SplitPoints (2 ^ levels) (fun _ : Fin 1 => (-1 : F)) (points ζ.val levels) (Nat.one_mul _).symm := by
  intro i
  refine ⟨neg_ne_zero.2 one_ne_zero, ζ.val ^ 2, ζ.val, bitRevPerm levels,
    ζ.2.pow (Nat.two_pow_pos _) (pow_succ' 2 levels), ζ.pow_eq_neg_one, fun k => ?_⟩
  show point ζ.val levels (k + 2 ^ levels * i) = ζ.val * (ζ.val ^ 2) ^ (bitRevPerm levels k).val
  rw [Fin.fin_one_eq_zero i]
  simp only [point, bitRevPerm_apply_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
  rw [pow_succ, ← pow_mul, mul_comm]

end Points

/-! ### The recursion and every schedule compute the closed form -/

section Forward

variable [CommRing F]

theorem ntt_eq_nttSpec : ∀ (levels : ℕ) (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n), ntt levels ζ f hL = nttSpec ζ f hL
  | 0, _, _, _ => rfl
  | l + 1, ζ, f, hL => by
    rw [ntt, ntt_eq_nttSpec l ζ.sq f (dvd_of_succ hL), nttSpec, nttSpec]
    exact split_split' _ _ _ _ _ _ _ _ _ (points_layerPoints_succ ζ) (pow_succ 2 l) _ _

theorem nttSched_eq_nttSpec : ∀ (bs : List ℕ) (l : ℕ) (ζ : PrimitiveRoot F (2 ^ (l + bs.sum + 1)))
    (f : PolyMod F n (-1)) (hL : 2 ^ (l + bs.sum) ∣ n), nttSched bs l ζ f hL = nttSpec ζ f hL
  | [], _, _, _, _ => rfl
  | b :: bs, l, ζ, f, hL => by
    rw [nttSched, nttSched_eq_nttSpec bs l _ f _, nttSpec, nttSpec]
    exact split_split' _ _ _ _ _ _ _ _ _
      (points_layerPoints (l := l + bs.sum) (b := b) (by simp only [List.sum_cons]; omega) ζ)
      (by rw [← Nat.pow_add]; congr 1; simp only [List.sum_cons]; omega) _ _

theorem nttSpec_apply {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (f : PolyMod F n (-1))
    (hL : 2 ^ levels ∣ n) (i : Fin (2 ^ levels)) :
    nttSpec ζ f hL i =
      f.poly.modBinomial (2 ^ levels) (n / 2 ^ levels) (point ζ.val levels i) (blockSize_mul hL) := by
  rw [nttSpec, split_apply, PolyQuot.apply_eq_poly]

theorem getElem_nttSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (f : PolyMod F n (-1))
    (hL : 2 ^ levels ∣ n) (i : Fin (2 ^ levels)) (x : ℕ) (hx : x < n / 2 ^ levels) :
    (nttSpec ζ f hL i)[x] = ∑ t : Fin (2 ^ levels),
      f[x + n / 2 ^ levels * t.val]'(Nat.lt_of_lt_of_eq (Poly.idx_lt hx t.isLt) (blockSize_mul hL).symm) *
        point ζ.val levels i ^ t.val := by
  rw [nttSpec_apply, Poly.getElem_modBinomial]
  rfl

theorem nttSpec_mul [IsDomain F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (f g : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) :
    nttSpec ζ (f * g) hL = nttSpec ζ f hL * nttSpec ζ g hL :=
  split_mul _ _ _ _ (root_layerPoints ζ) g

/-- The transform is multiplicative: FIPS 203 §4.3, multiplication in `T_q`. -/
theorem ntt_mul [IsDomain F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (f g : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) :
    ntt levels ζ (f * g) hL = ntt levels ζ f hL * ntt levels ζ g hL := by
  rw [ntt_eq_nttSpec, ntt_eq_nttSpec, ntt_eq_nttSpec, nttSpec_mul]

end Forward

/-! ### The inverses -/

section Inverse

variable [Field F]

theorem two_ne_zero' {l : ℕ} (ζ : PrimitiveRoot F (2 ^ (l + 1))) : ((2 : ℕ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat]; exact ζ.two_ne_zero

theorem nttInvSpec_nttSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) : nttInvSpec ζ (nttSpec ζ f hL) hL = f :=
  splitInv_split _ _ _ (root_splitPoints ζ) (ζ.natCast_two_pow_ne_zero levels) f

theorem nttSpec_nttInvSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (a : NTTDomain levels ζ n) (hL : 2 ^ levels ∣ n) : nttSpec ζ (nttInvSpec ζ a hL) hL = a :=
  split_splitInv _ _ _ (root_splitPoints ζ) (ζ.natCast_two_pow_ne_zero levels) a

theorem nttInv_ntt : ∀ (levels : ℕ) (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (f : PolyMod F n (-1))
    (hL : 2 ^ levels ∣ n), nttInv levels ζ (ntt levels ζ f hL) hL = f
  | 0, ζ, f, hL => nttInvSpec_nttSpec ζ f hL
  | l + 1, ζ, f, hL => by
    rw [ntt, nttInv, splitInv_split _ _ _ (points_splitPoints_succ ζ) (two_ne_zero' ζ),
      nttInv_ntt l]

theorem ntt_nttInv : ∀ (levels : ℕ) (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (a : NTTDomain levels ζ n)
    (hL : 2 ^ levels ∣ n), ntt levels ζ (nttInv levels ζ a hL) hL = a
  | 0, ζ, a, hL => nttSpec_nttInvSpec ζ a hL
  | l + 1, ζ, a, hL => by
    rw [ntt, nttInv, ntt_nttInv l, split_splitInv _ _ _ (points_splitPoints_succ ζ) (two_ne_zero' ζ)]

theorem nttInv_eq_nttInvSpec {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))
    (a : NTTDomain levels ζ n) (hL : 2 ^ levels ∣ n) : nttInv levels ζ a hL = nttInvSpec ζ a hL := by
  conv_lhs => rw [← nttSpec_nttInvSpec ζ a hL, ← ntt_eq_nttSpec]
  exact nttInv_ntt levels ζ _ hL

/-- Multiplying in the NTT domain computes the product in `F[X]/(X^n + 1)`
(FIPS 203 §4.3, Algorithms 11–12). -/
theorem nttInv_mul {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1))) (f g : PolyMod F n (-1))
    (hL : 2 ^ levels ∣ n) : nttInv levels ζ (ntt levels ζ f hL * ntt levels ζ g hL) hL = f * g := by
  rw [← ntt_mul, nttInv_ntt]

end Inverse

/-! ### Characterisations for external witnesses -/

section Witness

variable [CommRing F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))

/-- `a` is the transform of `f` iff each residue has the coefficients `∑ₜ f[x + d·t] · pointᵢ^t`. -/
theorem ntt_eq_iff (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) (a : NTTDomain levels ζ n) :
    ntt levels ζ f hL = a ↔ ∀ (i : Fin (2 ^ levels)) (x : ℕ) (hx : x < n / 2 ^ levels),
      (a i)[x] = ∑ t : Fin (2 ^ levels),
        f[x + n / 2 ^ levels * t.val]'(Nat.lt_of_lt_of_eq (Poly.idx_lt hx t.isLt) (blockSize_mul hL).symm) *
          point ζ.val levels i ^ t.val := by
  rw [ntt_eq_nttSpec, Residues.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Poly.ext_iff]
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  rw [getElem_nttSpec, eq_comm]

/-- `ntt_eq_iff` with the residue degree `d` named, for instantiation at concrete parameters. -/
theorem ntt_eq_iff' {d : ℕ} (hd : n / 2 ^ levels = d) (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n)
    (a : NTTDomain levels ζ n) :
    ntt levels ζ f hL = a ↔ ∀ (i : Fin (2 ^ levels)) (x : ℕ) (hx : x < d),
      (a i)[x]'(hd ▸ hx) = ∑ t : Fin (2 ^ levels),
        f[x + d * t.val]'(Nat.lt_of_lt_of_eq (Poly.idx_lt hx t.isLt) (hd ▸ blockSize_mul hL).symm) *
          point ζ.val levels i ^ t.val := by
  subst hd
  exact ntt_eq_iff ζ f hL a

/-- `a` is the transform of `f` iff residue `i` is the image of `f` in `F[X]/(X^d - pointᵢ)`. -/
theorem ntt_eq_iff_toR [IsDomain F] (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) (a : NTTDomain levels ζ n) :
    ntt levels ζ f hL = a ↔ ∀ i, a.toR i =
      R.reduceBinomial (2 ^ levels) (n / 2 ^ levels) (blockSize_mul hL) (point ζ.val levels i)
        (root_layerPoints ζ i) (Poly.toR (Poly.binomial (-1)) f.poly) := by
  rw [ntt_eq_nttSpec, nttSpec, split_eq_iff_toR _ _ _ _ (root_layerPoints ζ)]
  refine forall_congr' fun i => ?_
  simp only [Residues.toR, PolyQuot.apply_eq_poly]

/-- `a` is the transform of `f` iff the representative of residue `i` differs from that of `f`
by a multiple of `X^d - pointᵢ`. -/
theorem ntt_eq_iff_dvd [IsDomain F] [NeZero n] (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n)
    (a : NTTDomain levels ζ n) :
    ntt levels ζ f hL = a ↔ ∀ i : Fin (2 ^ levels),
      (X ^ (n / 2 ^ levels) - C (point ζ.val levels i) : F[X]) ∣ f.poly.toPoly - (a i).toPoly := by
  have : NeZero (n / 2 ^ levels) := ⟨Nat.ne_of_gt (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hL) (Nat.two_pow_pos _))⟩
  rw [ntt_eq_nttSpec, nttSpec, split_eq_iff_dvd _ _ _ _ (root_layerPoints ζ)]
  refine forall_congr' fun i => ?_
  rw [PolyQuot.apply_eq_poly]

/-- With a complete split (`n = 2^levels`), `a` is the transform of `f` iff residue `i` is the
value of `f` at `pointᵢ`. -/
theorem ntt_eq_iff_eval (hd : n / 2 ^ levels = 1) (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n)
    (a : NTTDomain levels ζ n) :
    ntt levels ζ f hL = a ↔
      ∀ i, (a i)[0]'(by omega) = f.poly.toPoly.eval (point ζ.val levels i) := by
  rw [ntt_eq_nttSpec, Residues.ext_iff]
  refine forall_congr' fun i => ?_
  rw [nttSpec_apply]
  constructor
  · intro h
    rw [← h, Poly.getElem_modBinomial_eval' _ _ _ hd]
  · intro h
    ext x hx
    have hx0 : x = 0 := by omega
    subst hx0
    rw [Poly.getElem_modBinomial_eval' _ _ _ hd, h]

end Witness

section WitnessInverse

variable [Field F] {levels : ℕ} (ζ : PrimitiveRoot F (2 ^ (levels + 1)))

theorem nttInv_eq_iff (a : NTTDomain levels ζ n) (hL : 2 ^ levels ∣ n) (f : PolyMod F n (-1)) :
    nttInv levels ζ a hL = f ↔ ntt levels ζ f hL = a :=
  ⟨fun e => e ▸ ntt_nttInv levels ζ a hL, fun e => e ▸ nttInv_ntt levels ζ f hL⟩

end WitnessInverse

end Wychelean.PolyRing.NTT
