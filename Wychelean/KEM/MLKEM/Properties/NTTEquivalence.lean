import Wychelean.KEM.MLKEM.Properties.NTTStages
import Wychelean.Utils.PolyRing.NTTProperties

namespace Wychelean.KEM.MLKEM.NTT

open Utils.PolyRing

/-- The root for the partial transform after `s` forward stages. -/
def root (s : ℕ) (hs : s ≤ 7) : PrimitiveRoot Zq (2 ^ (s + 1)) :=
  ζRoot.pow2 (7 - s) (s + 1) (by omega)

@[simp] theorem root_val (s : ℕ) (hs : s ≤ 7) : (root s hs).val = ζ ^ 2 ^ (7 - s) := rfl

theorem root_sq (s : ℕ) (hs : s < 7) :
    (root (s + 1) (by omega)).sq = root s (by omega) := by
  apply Subtype.ext
  simp only [PrimitiveRoot.sq_val, root_val, ← pow_mul]
  rw [← pow_succ]
  congr 2
  omega

@[simp] theorem root_seven : root 7 le_rfl = ζRoot := by
  apply Subtype.ext
  change ζ ^ 1 = ζ
  exact pow_one _

theorem depth_dvd (s : ℕ) (hs : s ≤ 7) : 2 ^ s ∣ 256 :=
  Utils.PolyRing.NTT.dvd_of_le hs (by decide : 2 ^ 7 ∣ 256)

theorem parent_width (s : Fin 7) : 256 / 2 ^ s.val = 2 * len s := by
  have h := blocks_mul_len s
  change 2 ^ s.val * (2 * len s) = 256 at h
  rw [← h, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

theorem child_width (s : Fin 7) : 256 / 2 ^ (s.val + 1) = len s := by
  have h := Utils.PolyRing.NTT.blockSize_succ (depth_dvd (s.val + 1) (by omega))
  rw [parent_width s] at h
  omega

/-- The FIPS twiddle counter at a block encodes its bit-reversed evaluation point. -/
theorem bitRev_counter (s : Fin 7) (b : Fin (blocks s)) :
    bitRev 7 (2 ^ s.val + b.val) = 2 ^ (6 - s.val) * (2 * bitRev s.val b.val + 1) := by
  have hsplit : 7 = (6 - s.val + 1) + s.val := by omega
  have hb : b.val < 2 ^ s.val := b.isLt
  conv_lhs => arg 1; rw [hsplit]
  rw [bitRev_add]
  have hd : (2 ^ s.val + b.val) / 2 ^ s.val = 1 := by
    rw [Nat.add_div_left _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb]
  have hm : (2 ^ s.val + b.val) % 2 ^ s.val = b.val := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hb]
  rw [hd, hm, bitRev_succ, bitRev_zero_right]
  simp only [Nat.reduceMod, Nat.zero_add, Nat.mul_one, pow_succ]
  ring

theorem point_even (s : Fin 7) (b : Fin (blocks s)) :
    Utils.PolyRing.NTT.point (root (s.val + 1) (by omega)).val (s.val + 1) (2 * b.val) =
      ζ ^ bitRev 7 (2 ^ s.val + b.val) := by
  rw [Utils.PolyRing.NTT.point, root_val, bitRev_succ]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right, Nat.mul_zero, Nat.add_zero]
  rw [← pow_mul, bitRev_counter]
  rw [show 7 - (s.val + 1) = 6 - s.val by omega]

theorem point_odd (s : Fin 7) (b : Fin (blocks s)) :
    Utils.PolyRing.NTT.point (root (s.val + 1) (by omega)).val (s.val + 1) (2 * b.val + 1) =
      -(ζ ^ bitRev 7 (2 ^ s.val + b.val) : Zq) := by
  have he := point_even s b
  rw [Utils.PolyRing.NTT.point, bitRev_succ s.val (2 * b.val)] at he
  rw [Utils.PolyRing.NTT.point, bitRev_succ s.val (2 * b.val + 1)]
  have hdiv : (2 * b.val + 1) / 2 = b.val := by omega
  have hmod : (2 * b.val + 1) % 2 = 1 := by omega
  simp only [hdiv, hmod, Nat.mul_one]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right, Nat.mul_zero, Nat.add_zero] at he
  rw [show 2 * (bitRev s.val b.val + 2 ^ s.val) + 1 =
    (2 * bitRev s.val b.val + 1) + 2 ^ (s.val + 1) by ring, pow_add,
    (root (s.val + 1) (by omega)).pow_eq_neg_one, he, mul_neg_one]

theorem flat_index (s : ℕ) (hs : s ≤ 7) (b : Fin (2 ^ s)) (j : ℕ)
    (hj : j < 256 / 2 ^ s) : j + (256 / 2 ^ s) * b.val < 256 := by
  have h := Residues.flat_idx_lt hj b.isLt
  rwa [← Utils.PolyRing.NTT.blockSize_mul (depth_dvd s hs)] at h

/-- The stage invariant in FIPS coefficient order. -/
def ForwardMatches (s : ℕ) (hs : s ≤ 7) (v : Vector Zq 256) (f : Polynomial) : Prop :=
  ∀ (b : Fin (2 ^ s)) (j : ℕ) (hj : j < 256 / 2 ^ s),
    v[j + (256 / 2 ^ s) * b.val]'(flat_index s hs b j hj) =
      (Utils.PolyRing.NTT.ntt s (root s hs) f.toPolyMod (depth_dvd s hs) b)[j]

theorem forwardMatches_zero (f : Polynomial) : ForwardMatches 0 (by omega) f.coeffs f := by
  intro b j hj
  have hb : b = 0 := Fin.fin_one_eq_zero b
  subst b
  rw [Utils.PolyRing.NTT.ntt, Utils.PolyRing.NTT.nttSpec, Residues.split_apply]
  simp only [pow_zero]
  rw [Poly.getElem_modBinomial_one]
  rfl

theorem forwardMatches_step (s : Fin 7) (v : Vector Zq 256) (f : Polynomial)
    (h : ForwardMatches s.val (by omega) v f) :
    ForwardMatches (s.val + 1) (by omega) (forwardStage (v, 2 ^ s.val) s).1 f := by
  intro b j hj
  have hj' : j < len s := by rwa [child_width s] at hj
  let p : Fin (blocks s) := ⟨b.val / 2, by
    change b.val / 2 < 2 ^ s.val
    have := b.isLt
    simp only [pow_succ] at this
    omega⟩
  let r : Fin (len s) := ⟨j, hj'⟩
  have hl := (forwardStage_pairs s v (2 ^ s.val)).2.1 p r
  have hh := (forwardStage_pairs s v (2 ^ s.val)).2.2 p r
  have hparent : j < 256 / 2 ^ s.val := by rw [parent_width s]; omega
  have hparent' : j + len s < 256 / 2 ^ s.val := by rw [parent_width s]; omega
  have hvl := h p j hparent
  have hvh := h p (j + len s) hparent'
  simp only [parent_width s] at hvl hvh
  have hlow : (low s p r).val = j + 2 * len s * p.val := by simp only [r]; omega
  have hhigh : (high s p r).val = j + len s + 2 * len s * p.val := by simp only [r]; omega
  dsimp only [low, high, r] at hl hh hlow hhigh
  simp only [hlow] at hhigh
  simp only [hlow, hhigh] at hl hh
  rw [hvl, hvh] at hl hh
  rw [Utils.PolyRing.NTT.ntt, Residues.getElem_split_two, root_sq s.val s.isLt]
  rcases Nat.mod_two_eq_zero_or_one b.val with hb | hb
  · have he : b.val = 2 * p.val := by dsimp [p]; omega
    have hidx : j + (256 / 2 ^ (s.val + 1)) * b.val = j + 2 * len s * p.val := by
      rw [child_width s, he]; ring
    have hpoint : Utils.PolyRing.NTT.points (root (s.val + 1) (by omega)).val (s.val + 1) b =
        ζ ^ bitRev 7 (2 ^ s.val + p.val) := by
      change Utils.PolyRing.NTT.point _ _ b.val = _
      rw [he]
      exact point_even s p
    simp only [child_width s] at hidx
    simpa only [hidx, hpoint, child_width s] using hl
  · have he : b.val = 2 * p.val + 1 := by dsimp [p]; omega
    have hidx : j + (256 / 2 ^ (s.val + 1)) * b.val = j + len s + 2 * len s * p.val := by
      rw [child_width s, he]; ring
    have hpoint : Utils.PolyRing.NTT.points (root (s.val + 1) (by omega)).val (s.val + 1) b =
        -(ζ ^ bitRev 7 (2 ^ s.val + p.val) : Zq) := by
      change Utils.PolyRing.NTT.point _ _ b.val = _
      rw [he]
      exact point_odd s p
    simp only [child_width s] at hidx
    simpa only [hidx, hpoint, child_width s, neg_mul, sub_eq_add_neg] using hh

/-- All seven executable stages agree with the recursive transform, for every input. -/
theorem toAbstract_ntt (f : Polynomial) :
    Tq.toAbstract (MLKEM.NTT f) = Utils.PolyRing.NTT.ntt 7 ζRoot f.toPolyMod (by decide) := by
  rw [NTT_eq_forward]
  let P (s : ℕ) (a : Vector Zq 256 × ℕ) : Prop :=
    ∃ hs : s ≤ 7, a.2 = 2 ^ s ∧ ForwardMatches s hs a.1 f
  have h := foldl_invariant (n := 7) forwardStage P (f.coeffs, 1)
    ⟨by omega, rfl, forwardMatches_zero f⟩ (by
      intro s a ha
      obtain ⟨hs, hc, hm⟩ := ha
      refine ⟨by omega, ?_, ?_⟩
      · have hcount := (forwardStage_pairs s a.1 a.2).1
        change (forwardStage (a.1, a.2) s).2 = _
        simpa only [hc, blocks, pow_succ, Nat.mul_two] using hcount
      · have he : a = (a.1, 2 ^ s.val) := Prod.ext rfl hc
        rw [he]
        exact forwardMatches_step s a.1 f hm)
  obtain ⟨hs, _, hm⟩ := h
  apply Residues.ext
  intro i
  apply Poly.ext
  intro j hj
  rw [Tq.toAbstract_apply, Tq.component_getElem]
  have he := hm i j hj
  have hr : root 7 hs = ζRoot := root_seven
  rw [hr] at he
  exact he

/-- Coefficients of the partial recursive transform, used only in the correctness proof. -/
def partialCoeffs (s : ℕ) (hs : s ≤ 7) (f : Polynomial) : Vector Zq 256 :=
  (Utils.PolyRing.NTT.ntt s (root s hs) f.toPolyMod (depth_dvd s hs)).flatten.cast
    (Utils.PolyRing.NTT.blockSize_mul (depth_dvd s hs)).symm

theorem partialMatches (s : ℕ) (hs : s ≤ 7) (f : Polynomial) :
    ForwardMatches s hs (partialCoeffs s hs f) f := by
  intro b j hj
  simp only [partialCoeffs, Vector.getElem_cast]
  exact Residues.getElem_flatten _ b ⟨j, hj⟩

theorem matches_unique (s : ℕ) (hs : s ≤ 7) (f : Polynomial) (v w : Vector Zq 256)
    (hv : ForwardMatches s hs v f) (hw : ForwardMatches s hs w f) : v = w := by
  apply Vector.ext
  intro k hk
  have hd : 0 < 256 / 2 ^ s := Nat.div_pos
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hs) (by decide)) (Nat.two_pow_pos _)
  have hb : k / (256 / 2 ^ s) < 2 ^ s := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm, ← Utils.PolyRing.NTT.blockSize_mul (depth_dvd s hs)]
    exact hk)
  have hr : k % (256 / 2 ^ s) < 256 / 2 ^ s := Nat.mod_lt _ hd
  have h := (hv ⟨k / (256 / 2 ^ s), hb⟩ _ hr).trans (hw ⟨k / (256 / 2 ^ s), hb⟩ _ hr).symm
  simpa only [Nat.mod_add_div] using h

theorem partialCoeffs_zero (f : Polynomial) : partialCoeffs 0 (by omega) f = f.coeffs :=
  matches_unique 0 (by omega) f _ _ (partialMatches _ _ f) (forwardMatches_zero f)

theorem forwardStage_partial (s : Fin 7) (f : Polynomial) :
    (forwardStage (partialCoeffs s.val (by omega) f, 2 ^ s.val) s).1 =
      partialCoeffs (s.val + 1) (by omega) f :=
  matches_unique _ _ f _ _ (forwardMatches_step s _ f (partialMatches _ _ f)) (partialMatches _ _ f)

theorem forward_eq_partial (f : Polynomial) : forward f.coeffs = partialCoeffs 7 le_rfl f := by
  have h := congrArg Residues.flatten (toAbstract_ntt f)
  simp only [Tq.toAbstract, NTT_eq_forward, Residues.flatten_ofFlat] at h
  unfold partialCoeffs
  rw [root_seven]
  exact h

/-- Complementary block indices have complementary reversed bits. -/
theorem bitRev_complement (n b : ℕ) (hb : b < 2 ^ n) :
    bitRev n (2 ^ n - 1 - b) + bitRev n b = 2 ^ n - 1 := by
  induction n generalizing b with
  | zero => simp only [bitRev_zero]; omega
  | succ n ih =>
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    have hb' : b / 2 < 2 ^ n := by rw [pow_succ] at hb; omega
    have hd : (2 ^ (n + 1) - 1 - b) / 2 = 2 ^ n - 1 - b / 2 := by
      rw [pow_succ]; omega
    have hm : (2 ^ (n + 1) - 1 - b) % 2 + b % 2 = 1 := by
      rw [pow_succ] at hb ⊢; omega
    rw [bitRev_succ, bitRev_succ, hd]
    have h := ih (b / 2) hb'
    rw [pow_succ] at hm ⊢
    have hm' := congrArg (fun x => 2 ^ n * x) hm
    have hp' : 2 ^ n - 1 + 1 = 2 ^ n := by omega
    have hp2 : 2 ^ n * 2 - 1 + 1 = 2 ^ n * 2 := by omega
    nlinarith

theorem inverse_counter_exponents (s : Fin 7) (b : Fin (blocks s)) :
    bitRev 7 (2 ^ (s.val + 1) - 1 - b.val) + bitRev 7 (2 ^ s.val + b.val) = 128 := by
  let b' : Fin (blocks s) := ⟨2 ^ s.val - 1 - b.val, by
    have := Nat.two_pow_pos s.val; change _ < 2 ^ s.val; omega⟩
  have hi : 2 ^ (s.val + 1) - 1 - b.val = 2 ^ s.val + b'.val := by
    dsimp [b']; rw [pow_succ]; have := b.isLt; change b.val < 2 ^ s.val at this; omega
  rw [hi, bitRev_counter, bitRev_counter]
  have hr := bitRev_complement s.val b.val b.isLt
  have hp : 2 ^ (6 - s.val) * 2 ^ s.val = 64 := by
    rw [← pow_add, show 6 - s.val + s.val = 6 by omega]
    rfl
  have hpos := Nat.two_pow_pos s.val
  dsimp [b']
  have hr' : bitRev s.val (2 ^ s.val - 1 - b.val) + bitRev s.val b.val + 1 = 2 ^ s.val := by omega
  have hm := congrArg (fun x => 2 ^ (6 - s.val) * x) hr'
  nlinarith

theorem inverse_twiddle (s : Fin 7) (b : Fin (blocks s)) :
    (ζ ^ bitRev 7 (2 ^ (s.val + 1) - 1 - b.val) : Zq) *
      ζ ^ bitRev 7 (2 ^ s.val + b.val) = -1 := by
  rw [← pow_add, inverse_counter_exponents]
  exact ζRoot.pow_eq_neg_one

theorem vector_ext_pairs (s : Fin 7) {v w : Vector Zq 256}
    (hl : ∀ b j, v[(low s b j).val] = w[(low s b j).val])
    (hh : ∀ b j, v[(high s b j).val] = w[(high s b j).val]) : v = w := by
  apply Vector.ext
  intro k hk
  have hp : 0 < 2 * len s := by have := len_pos s; omega
  have hb : k / (2 * len s) < blocks s := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm, blocks_mul_len]; exact hk)
  have hr : k % (2 * len s) < 2 * len s := Nat.mod_lt _ hp
  have he := Nat.mod_add_div k (2 * len s)
  let b : Fin (blocks s) := ⟨k / (2 * len s), hb⟩
  by_cases hj : k % (2 * len s) < len s
  · let j : Fin (len s) := ⟨k % (2 * len s), hj⟩
    have hidx : low s b j = ⟨k, hk⟩ := Fin.ext (by dsimp [low, b, j]; omega)
    exact (congrArg (fun i : Fin 256 => v[i.val]) hidx).symm.trans
      ((hl b j).trans (congrArg (fun i : Fin 256 => w[i.val]) hidx))
  · let j : Fin (len s) := ⟨k % (2 * len s) - len s, by omega⟩
    have hidx : high s b j = ⟨k, hk⟩ := Fin.ext (by dsimp [high, b, j]; omega)
    exact (congrArg (fun i : Fin 256 => v[i.val]) hidx).symm.trans
      ((hh b j).trans (congrArg (fun i : Fin 256 => w[i.val]) hidx))

/-- An inverse stage cancels a forward stage with an accumulated factor of two. -/
theorem inverseStage_forwardStage (s : Fin 7) (v : Vector Zq 256) (c : Zq) :
    (inverseStage (((forwardStage (v, 2 ^ s.val) s).1.map (c * ·)),
      2 ^ (s.val + 1) - 1) s).1 = v.map ((2 * c) * ·) := by
  apply vector_ext_pairs s
  · intro b j
    have h := (inverseStage_pairs s ((forwardStage (v, 2 ^ s.val) s).1.map (c * ·))
      (2 ^ (s.val + 1) - 1)).2.1 b j
    have hl := (forwardStage_pairs s v (2 ^ s.val)).2.1 b j
    have hh := (forwardStage_pairs s v (2 ^ s.val)).2.2 b j
    simp only [Vector.getElem_map] at h ⊢
    rw [h, hl, hh]
    ring
  · intro b j
    have h := (inverseStage_pairs s ((forwardStage (v, 2 ^ s.val) s).1.map (c * ·))
      (2 ^ (s.val + 1) - 1)).2.2 b j
    have hl := (forwardStage_pairs s v (2 ^ s.val)).2.1 b j
    have hh := (forwardStage_pairs s v (2 ^ s.val)).2.2 b j
    simp only [Vector.getElem_map] at h ⊢
    rw [h, hl, hh]
    calc _ = -2 * c * (ζ ^ bitRev 7 (2 ^ (s.val + 1) - 1 - b.val) *
        ζ ^ bitRev 7 (2 ^ s.val + b.val)) * v[(high s b j).val] := by ring
      _ = _ := by rw [inverse_twiddle]; ring

/-- On an arbitrary layer, Algorithm 10 computes twice the abstract `splitInv`. -/
theorem inverseStage_splitInv (s : Fin 7)
    (a : NTTDomain (s.val + 1) (root (s.val + 1) (by omega)) 256) :
    (inverseStage (a.flatten.cast (Utils.PolyRing.NTT.blockSize_mul
      (depth_dvd (s.val + 1) (by omega))).symm, 2 ^ (s.val + 1) - 1) s).1 =
    ((Residues.splitInv 2 a (Utils.PolyRing.NTT.points (root s.val (by omega)).val s.val)
      (Utils.PolyRing.NTT.blockSize_succ (depth_dvd (s.val + 1) (by omega))) (pow_succ 2 s.val)).flatten.cast
        (Utils.PolyRing.NTT.blockSize_mul (depth_dvd s.val (by omega))).symm).map ((2 : Zq) * ·) := by
  let f : Polynomial := Polynomial.ofPolyMod
    (Utils.PolyRing.NTT.nttInv (s.val + 1) (root (s.val + 1) (by omega)) a
      (depth_dvd (s.val + 1) (by omega)))
  have hnext : partialCoeffs (s.val + 1) (by omega) f = a.flatten.cast
      (Utils.PolyRing.NTT.blockSize_mul (depth_dvd (s.val + 1) (by omega))).symm := by
    unfold partialCoeffs
    rw [show Utils.PolyRing.NTT.ntt (s.val + 1) (root (s.val + 1) (by omega)) f.toPolyMod
        (depth_dvd (s.val + 1) (by omega)) = a by
      dsimp only [f]; rw [Polynomial.toPolyMod_ofPolyMod]; exact
      Utils.PolyRing.NTT.ntt_nttInv (n := 256) (s.val + 1) (root (s.val + 1) (by omega)) a
        (depth_dvd (s.val + 1) (by omega))]
  have hparent : Utils.PolyRing.NTT.ntt s.val (root s.val (by omega)) f.toPolyMod (depth_dvd s.val (by omega)) =
      Residues.splitInv 2 a (Utils.PolyRing.NTT.points (root s.val (by omega)).val s.val)
        (Utils.PolyRing.NTT.blockSize_succ (depth_dvd (s.val + 1) (by omega))) (pow_succ 2 s.val) := by
    dsimp only [f]
    rw [Polynomial.toPolyMod_ofPolyMod, Utils.PolyRing.NTT.nttInv, root_sq s.val s.isLt]
    exact Utils.PolyRing.NTT.ntt_nttInv (n := 256) s.val (root s.val (by omega)) _ _
  have h := inverseStage_forwardStage s (partialCoeffs s.val (by omega) f) 1
  rw [forwardStage_partial] at h
  simp only [one_mul, Vector.map_id_fun', id_eq, mul_one, hnext] at h
  rw [partialCoeffs, hparent] at h
  exact h

/-- The backward traversal doubles the scale at each of its seven stages. -/
theorem inverse_forward (f : Polynomial) : inverse (forward f.coeffs) = f.coeffs := by
  let P (t : ℕ) (a : Vector Zq 256 × ℕ) : Prop :=
    ∃ ht : t ≤ 7, a.2 = 2 ^ (7 - t) - 1 ∧
      a.1 = (partialCoeffs (7 - t) (by omega) f).map ((2 : Zq) ^ t * ·)
  have h := foldl_invariant (n := 7)
    (fun state s => inverseStage state ⟨6 - s.val, by omega⟩) P (forward f.coeffs, 127)
    (by refine ⟨by omega, rfl, ?_⟩; simpa only [pow_zero, one_mul, Vector.map_id_fun', id_eq] using forward_eq_partial f)
    (by
      intro t a ha
      obtain ⟨ht, hc, hv⟩ := ha
      let s : Fin 7 := ⟨6 - t.val, by omega⟩
      have hs : s.val + 1 = 7 - t.val := by dsimp [s]; omega
      have hs' : 7 - (t.val + 1) = s.val := by dsimp [s]; omega
      refine ⟨by omega, ?_, ?_⟩
      · have hcount := (inverseStage_pairs s a.1 a.2).1
        change (inverseStage (a.1, a.2) s).2 = _
        rw [hcount, hc, ← hs, hs', pow_succ]
        change 2 ^ s.val * 2 - 1 - 2 ^ s.val = 2 ^ s.val - 1
        omega
      · have hstage := inverseStage_forwardStage s (partialCoeffs s.val (by omega) f) ((2 : Zq) ^ t.val)
        rw [forwardStage_partial] at hstage
        have ha' : a = ((partialCoeffs (s.val + 1) (by omega) f).map ((2 : Zq) ^ t.val * ·),
            2 ^ (s.val + 1) - 1) := by
          apply Prod.ext
          · simpa only [hs] using hv
          · simpa only [hs] using hc
        rw [ha']
        simpa only [hs', pow_succ', Nat.sub_sub] using hstage)
  obtain ⟨_, _, hv⟩ := h
  unfold inverse
  rw [hv, partialCoeffs_zero, Vector.map_map]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Function.comp_apply]
  have hn : (2 : Zq) ^ 7 * 3303 = 1 := by decide +kernel
  calc _ = f.coeffs[i] * ((2 : Zq) ^ 7 * 3303) := by ring
    _ = _ := by rw [hn, mul_one]

end Wychelean.KEM.MLKEM.NTT

namespace Wychelean.KEM.MLKEM

open Utils.PolyRing

/-- The recursive transform retained as the algebraic comparison operation. -/
abbrev abstractNTT (f : Polynomial) : AbstractTq :=
  Utils.PolyRing.NTT.ntt 7 ζRoot f.toPolyMod (by decide)

abbrev abstractNTTInv (a : AbstractTq) : Polynomial :=
  Polynomial.ofPolyMod (Utils.PolyRing.NTT.nttInv 7 ζRoot a (by decide))

theorem toAbstract_ntt (f : Polynomial) : Tq.toAbstract (NTT f) = abstractNTT f :=
  NTT.toAbstract_ntt f

@[simp] theorem nttInv_ntt (f : Polynomial) : NTTInv (NTT f) = f := by
  rw [NTTInv_eq_inverse, NTT_eq_forward]
  change Polynomial.mk (NTT.inverse (NTT.forward f.coeffs)) = f
  rw [NTT.inverse_forward]

/-- Algorithm 10 agrees with the recursive inverse on every NTT-domain input. -/
theorem nttInv_eq_abstract (a : Tq) : NTTInv a = abstractNTTInv (Tq.toAbstract a) := by
  let f := abstractNTTInv (Tq.toAbstract a)
  have hf : NTT f = a := Tq.toAbstract_injective (by
    rw [toAbstract_ntt, abstractNTT, Polynomial.toPolyMod_ofPolyMod]
    exact Utils.PolyRing.NTT.ntt_nttInv (n := 256) 7 ζRoot (Tq.toAbstract a) (by decide))
  change NTTInv a = f
  exact (congrArg NTTInv hf).symm.trans (nttInv_ntt f)

@[simp] theorem ntt_nttInv (a : Tq) : NTT (NTTInv a) = a := by
  apply Tq.toAbstract_injective
  rw [toAbstract_ntt, nttInv_eq_abstract, abstractNTT, Polynomial.toPolyMod_ofPolyMod]
  exact Utils.PolyRing.NTT.ntt_nttInv (n := 256) 7 ζRoot (Tq.toAbstract a) (by decide)

/-- Executable Algorithms 9–12 give a ring equivalence with the polynomial ring. -/
def nttEquiv : Polynomial ≃+* Tq where
  toFun := NTT
  invFun := NTTInv
  left_inv := nttInv_ntt
  right_inv := ntt_nttInv
  map_mul' f g := by
    apply Tq.toAbstract_injective
    simp only [toAbstract_ntt, Tq.toAbstract_mul, abstractNTT, Polynomial.toPolyMod_mul]
    exact Utils.PolyRing.NTT.ntt_mul ζRoot f.toPolyMod g.toPolyMod (by decide)
  map_add' f g := by
    apply Tq.toAbstract_injective
    simp only [toAbstract_ntt, Tq.toAbstract_add, abstractNTT, Polynomial.toPolyMod_add,
      Utils.PolyRing.NTT.ntt_eq_nttSpec, Utils.PolyRing.NTT.nttSpec]
    exact Residues.split_add ..

@[simp] theorem nttEquiv_apply (f : Polynomial) : nttEquiv f = NTT f := rfl
@[simp] theorem nttEquiv_symm_apply (a : Tq) : nttEquiv.symm a = NTTInv a := rfl

end Wychelean.KEM.MLKEM
