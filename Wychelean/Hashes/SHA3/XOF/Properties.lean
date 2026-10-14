import Wychelean.Hashes.SHA3.XOF.Basic
import Wychelean.Hashes.SHA3.Properties

namespace Wychelean.Hashes.SHA3
open Wychelean Internal

namespace Incremental

variable (f : BitVec b → BitVec b) (r : Nat) (hr : 0 < r ∧ r < b)

@[simp] theorem sponge.absorb_nil (s : sponge.absorbingState r) :
    sponge.absorb f r hr s [] = s := by
  rw [sponge.absorb]
  simp [show 0 < r - s.pending.size by have := s.h_pending; omega]

private theorem buffer_cons (P : Array Bit) (bit : Bit) (N : List Bit) :
    P ++ (bit :: N).toArray = P.push bit ++ N.toArray := by
  apply Array.ext'
  simp only [Array.toList_append, Array.toList_push,
    List.append_assoc, List.singleton_append]

private theorem take_length_lt (N : List Bit) (k : Nat) :
    (N.take k).length < k ↔ N.length < k := by
  rw [List.length_take]
  omega

/-- Block absorption agrees with the single-bit transition. -/
theorem sponge.absorb_cons (s : sponge.absorbingState r) (bit : Bit) (N : List Bit) :
    sponge.absorb f r hr s (bit :: N) =
      sponge.absorb f r hr (sponge.absorbBit f r hr s bit) N := by
  have hp := s.h_pending
  by_cases hfull : s.pending.size + 1 = r
  · have hk : r - s.pending.size = 1 := by omega
    have hbit : sponge.absorbBit f r hr s bit =
        { S := f (s.S ^^^ sponge.blockMask (s.pending.push bit)),
          pending := #[], h_pending := by simpa using hr.1 } := by
      simp [sponge.absorbBit, hfull]
    rw [hbit]
    rw [sponge.absorb]
    simp only [hk, List.length_cons, Nat.succ_lt_succ_iff, Nat.not_lt_zero, dite_false,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      buffer_cons, Array.append_empty]
  · have hlt : s.pending.size + 1 < r := by omega
    have hk : r - s.pending.size = (r - (s.pending.size + 1)) + 1 := by omega
    simp only [sponge.absorbBit, Array.size_push, dite_eq_right hfull]
    conv => lhs; rw [sponge.absorb]
    conv => rhs; rw [sponge.absorb]
    simp only [take_length_lt]
    by_cases hn : N.length < r - (s.pending.size + 1)
    · have hn' : (bit :: N).length < r - s.pending.size := by simp only [List.length_cons]; omega
      simp only [Array.size_push, dite_eq_left hn, dite_eq_left hn', buffer_cons]
    · have hn' : ¬(bit :: N).length < r - s.pending.size := by simp only [List.length_cons]; omega
      simp only [Array.size_push]
      simp only [dite_eq_right hn, dite_eq_right hn']
      simp only [hk, List.take_succ_cons, List.drop_succ_cons, buffer_cons]

/-- Absorption equals repeated single-bit absorption. -/
theorem sponge.absorb_eq_foldl (s : sponge.absorbingState r) (N : List Bit) :
    sponge.absorb f r hr s N = N.foldl (sponge.absorbBit f r hr) s := by
  induction N generalizing s with
  | nil => simp only [sponge.absorb_nil, List.foldl_nil]
  | cons bit N ih => rw [sponge.absorb_cons, List.foldl_cons, ih]

/-- Absorb chunking gives the same state (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.absorb_append (s : sponge.absorbingState r) (a c : List Bit) :
    sponge.absorb f r hr (sponge.absorb f r hr s a) c =
      sponge.absorb f r hr s (a ++ c) := by
  simp only [sponge.absorb_eq_foldl, List.foldl_append]

/-- Any finite absorb sequence equals one concatenated absorb (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.absorb_chunks (s : sponge.absorbingState r) (chunks : List (List Bit)) :
    chunks.foldl (sponge.absorb f r hr) s = sponge.absorb f r hr s chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp only [List.foldl_nil, List.flatten_nil, sponge.absorb_nil]
  | cons chunk chunks ih =>
    simp only [List.foldl_cons, List.flatten_cons, ih, sponge.absorb_append]

@[simp] theorem sponge.absorbBit_pending_size (s : sponge.absorbingState r) (bit : Bit) :
    (sponge.absorbBit f r hr s bit).pending.size = (s.pending.size + 1) % r := by
  by_cases h : s.pending.size + 1 = r
  · simp [sponge.absorbBit, h]
  · have hlt : s.pending.size + 1 < r := by have := s.h_pending; omega
    simp [sponge.absorbBit, h, Nat.mod_eq_of_lt hlt]

theorem sponge.absorb_pending_size (s : sponge.absorbingState r) (input : List Bit) :
    (sponge.absorb f r hr s input).pending.size = (s.pending.size + input.length) % r := by
  induction input generalizing s with
  | nil => simp [Nat.mod_eq_of_lt s.h_pending]
  | cons bit input ih =>
    rw [sponge.absorb_cons]
    rw [ih, sponge.absorbBit_pending_size, Nat.mod_add_mod]
    congr 1
    simp only [List.length_cons]
    omega

/-- Padding leaves no incomplete block (FIPS 202 §5.1, Algorithm 9). -/
theorem sponge.finalize_complete (s : sponge.absorbingState r) (suffix : List Bit) :
    let input := sponge.absorb f r hr s suffix
    (sponge.absorb f r hr input («pad10*1» r input.pending.size).toBitsLE.toList).pending =
      #[] := by
  dsimp only
  apply Array.eq_empty_of_size_eq_zero
  rw [sponge.absorb_pending_size]
  simp only [Vector.length_toList]
  exact Internal.padLen_dvd r _ hr.1

private theorem outputBits_succ (S : BitVec b) (x d : Nat) :
    sponge.outputBits S x (d + 1) = S.getLsbD x :: sponge.outputBits S (x + 1) d := by
  simp only [sponge.outputBits, BitVec.toBitsLE, Vector.toList_ofFn, List.ofFn_succ,
    BitVec.getLsbD_extractLsb', Fin.val_zero, Nat.zero_lt_succ, decide_true,
    Bool.true_and, Nat.add_zero]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Fin.val_succ, Nat.add_lt_add_iff_right, i.isLt, decide_true, Bool.true_and]
  congr 1
  omega

private theorem outputBits_zero (S : BitVec b) (x : Nat) : sponge.outputBits S x 0 = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [sponge.outputBits]

@[simp] theorem sponge.squeezeList_zero (s : sponge.squeezingState r) :
    sponge.squeezeList f r hr s 0 = (s, []) := by
  rw [sponge.squeezeList]
  rfl

private theorem sponge.squeezeList_succ_nonboundary (s : sponge.squeezingState r) (d : Nat)
    (hx : s.x < r) :
    sponge.squeezeList f r hr s (d + 1) =
      let result := sponge.squeezeList f r hr
        { s with x := s.x + 1, hx := by omega } d
      (result.1, s.S.getLsbD s.x :: result.2) := by
  conv => lhs; rw [sponge.squeezeList]
  simp only [dite_eq_right (Nat.succ_ne_zero d), dite_eq_right (Nat.ne_of_lt hx)]
  by_cases hd : d = 0
  · subst d
    simp [show 1 ≤ r - s.x by omega, outputBits_succ, outputBits_zero]
  · by_cases hlast : s.x + 1 = r
    · have hk : r - s.x = 1 := by omega
      simp [hk, hlast, show ¬d + 1 ≤ 1 by omega,
        show d + 1 - 1 = d by omega, outputBits_succ, outputBits_zero]
    · have hk : r - s.x = (r - (s.x + 1)) + 1 := by omega
      have hx' : s.x + 1 < r := by omega
      conv => rhs; rw [sponge.squeezeList]
      simp only [dite_eq_right hd, dite_eq_right (Nat.ne_of_lt hx')]
      by_cases hfit : d ≤ r - (s.x + 1)
      · have hfit' : d + 1 ≤ r - s.x := by omega
        simp only [dite_eq_left hfit, dite_eq_left hfit', outputBits_succ]
        congr 1
        congr 1
        omega
      · have hfit' : ¬d + 1 ≤ r - s.x := by omega
        simp only [dite_eq_right hfit, dite_eq_right hfit']
        simp only [hk, outputBits_succ, List.cons_append]
        rw [show d + 1 - (r - (s.x + 1) + 1) = d - (r - (s.x + 1)) by omega]

/-- Block squeezing agrees with the single-bit transition. -/
theorem sponge.squeezeList_succ (s : sponge.squeezingState r) (d : Nat) :
    sponge.squeezeList f r hr s (d + 1) =
      let (s', bit) := sponge.squeezeBit f r hr s
      let result := sponge.squeezeList f r hr s' d
      (result.1, bit :: result.2) := by
  by_cases hx : s.x = r
  · conv => lhs; rw [sponge.squeezeList]
    simp only [dite_eq_right (Nat.succ_ne_zero d), dite_eq_left hx]
    rw [sponge.squeezeList_succ_nonboundary f r hr _ d (by simpa using hr.1)]
    simp only [sponge.squeezeBit, dite_eq_left hx, Nat.zero_add]
  · have hlt : s.x < r := by have := s.hx; omega
    simp only [sponge.squeezeBit, dite_eq_right hx]
    exact sponge.squeezeList_succ_nonboundary f r hr s d hlt

/-- Squeeze chunking gives the same state and output (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.squeezeList_add (s : sponge.squeezingState r) (m n : Nat) :
    ((sponge.squeezeList f r hr (sponge.squeezeList f r hr s m).1 n).1,
      (sponge.squeezeList f r hr s m).2 ++
        (sponge.squeezeList f r hr (sponge.squeezeList f r hr s m).1 n).2) =
      sponge.squeezeList f r hr s (m + n) := by
  induction m generalizing s with
  | zero => simp only [sponge.squeezeList_zero, Nat.zero_add, List.nil_append]
  | succ m ih =>
    rw [Nat.succ_add]
    cases h : sponge.squeezeBit f r hr s with
    | mk s' bit =>
      simp only [sponge.squeezeList_succ, h, List.cons_append]
      exact congrArg (fun p : sponge.squeezingState r × List Bit => (p.1, bit :: p.2)) (ih s')

@[simp] theorem sponge.squeeze_zero (s : sponge.squeezingState r) :
    (sponge.squeeze f r hr s 0).1 = s := by simp only [sponge.squeeze, sponge.squeezeList_zero]

/-- Squeeze chunking gives the same state (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.squeeze_state_add (s : sponge.squeezingState r) (m n : Nat) :
    (sponge.squeeze f r hr (sponge.squeeze f r hr s m).1 n).1 =
      (sponge.squeeze f r hr s (m + n)).1 := by
  exact congrArg Prod.fst (sponge.squeezeList_add f r hr s m n)

/-- Squeeze chunking gives the same output (FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.squeeze_output_add (s : sponge.squeezingState r) (m n : Nat) :
    (sponge.squeeze f r hr s m).2.toList ++
      (sponge.squeeze f r hr (sponge.squeeze f r hr s m).1 n).2.toList =
        (sponge.squeeze f r hr s (m + n)).2.toList := by
  simpa only [sponge.squeeze, Vector.toList_mk, List.toList_toArray] using
    congrArg Prod.snd (sponge.squeezeList_add f r hr s m n)

/-- Any finite squeeze sequence gives the same final state (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem sponge.squeeze_chunks (s : sponge.squeezingState r) (sizes : List Nat) :
    sizes.foldl (fun s n => (sponge.squeeze f r hr s n).1) s =
      (sponge.squeeze f r hr s sizes.sum).1 := by
  induction sizes generalizing s with
  | nil => simp only [List.foldl_nil, List.sum_nil, sponge.squeeze_zero]
  | cons size sizes ih =>
    simp only [List.foldl_cons, List.sum_cons, ih, sponge.squeeze_state_add]

/-! ### Agreement with the one-shot sponge -/

private theorem sponge.absorb_block (S : BitVec b) (h : (#[] : Array Bit).size < r)
    (L : List Bit) (hL : r ≤ L.length) :
    sponge.absorb f r hr ⟨S, #[], h⟩ L =
      sponge.absorb f r hr ⟨f (S ^^^ sponge.blockMask (L.take r).toArray), #[], h⟩
        (L.drop r) := by
  rw [sponge.absorb]
  simp only [List.length_take, Array.size_empty, Nat.sub_zero, Array.empty_append]
  rw [dite_eq_right (by omega)]

private theorem sponge.blockMask_eq (A : Array Bit) (v : BitVec r)
    (hA : A.toList = (BitVec.toBitsLE v).toList) : sponge.blockMask A = v.zeroExtend b := by
  have hs : A.size = r := by simpa using congrArg List.length hA
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [sponge.blockMask, BitVec.getLsbD_setWidth]
  by_cases hir : i < r
  · rw [BitVec.getLsbD_ofBitsLE _ _ (by omega)]
    have := List.getElem_of_eq hA (i := i) (by simp; omega)
    simp only [Array.getElem_toList, BitVec.toBitsLE, Vector.getElem_toList,
      Vector.getElem_ofFn] at this
    simp [this, hi]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

private theorem take_drop_toBitsLE {w : Nat} (P : BitVec w) (j : Nat) (hw : j * r + r ≤ w) :
    ((BitVec.toBitsLE P).toList.drop (j * r)).take r =
      (BitVec.toBitsLE (P.extractLsb' (j * r) r)).toList := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_take, List.length_drop, Vector.length_toList] at h1
    simp [BitVec.toBitsLE, BitVec.getLsbD_eq_getElem (show j * r + i < w by omega)]

/-- With nothing pending, absorbing whole rate blocks of `P` is FIPS 202 Algorithm 8, step 6. -/
theorem sponge.absorb_blocks {w : Nat} (P : BitVec w) (S : BitVec b)
    (h : (#[] : Array Bit).size < r) (k j : Nat) (hw : (j + k) * r = w) :
    sponge.absorb f r hr ⟨S, #[], h⟩ ((BitVec.toBitsLE P).toList.drop (j * r)) =
      ⟨Fin.foldl k (fun S (i : Fin k) =>
        f (S ^^^ (P.extractLsb' ((j + i) * r) r).zeroExtend b)) S, #[], h⟩ := by
  induction k generalizing j S with
  | zero =>
    simp only [Nat.add_zero] at hw
    subst hw
    rw [List.drop_eq_nil_of_le (by simp), sponge.absorb_nil, Fin.foldl_zero]
  | succ k ih =>
    have hw' : w = j * r + k * r + r := by rw [← hw, Nat.add_mul, Nat.succ_mul]; omega
    subst hw'
    rw [sponge.absorb_block f r hr _ _ _ (by simp; omega), List.drop_drop, Fin.foldl_succ,
      sponge.blockMask_eq r _ _ (by rw [take_drop_toBitsLE r P j (by omega)]),
      show j * r + r = (j + 1) * r by rw [Nat.succ_mul],
      ih _ (j + 1) (by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega)]
    simp only [Fin.val_succ, Fin.val_zero, Nat.add_zero,
      show ∀ i : Nat, j + 1 + i = j + (i + 1) from fun i => by omega]

/-- Finalizing a fresh sponge on `N` gives the one-shot absorbed state, ready to squeeze. -/
theorem sponge.finalize_init {n : Nat} (N : BitVec n) :
    sponge.finalize f r hr (sponge.init r hr) (BitVec.toBitsLE N).toList =
      ⟨Internal.absorb f r N, 0, Nat.zero_le r⟩ := by
  simp only [sponge.finalize, sponge.squeezingState.mk.injEq, and_true]
  rw [sponge.absorb_append, toList_toBitsLE_pad (m' := n) (by
      simp only [sponge.absorb_pending_size, sponge.init, Array.size_empty, Nat.zero_add,
        Vector.length_toList, padLen.j_mod]),
    ← BitVec.toList_toBitsLE_append]
  have hk : (0 + (n + padLen r n) / r) * r = padLen r n + n := by
    rw [Nat.zero_add, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (padLen_dvd r n hr.1))]
    omega
  have := sponge.absorb_blocks f r hr («pad10*1» r n ++ N) 0 (by simpa using hr.1) _ 0 hk
  simp only [Nat.zero_mul, List.drop_zero, Nat.zero_add] at this
  simp only [sponge.init, this, Internal.absorb]

/-- Squeezing from the start of a block is FIPS 202 Algorithm 8, steps 8–10. -/
theorem sponge.squeezeList_eq (S : BitVec b) (hx : 0 ≤ r) (d : Nat) :
    (sponge.squeezeList f r hr ⟨S, 0, hx⟩ d).2 =
      (BitVec.toBitsLE (Internal.squeeze f r S d hr)).toList := by
  fun_induction Internal.squeeze f r S d hr with
  | case1 S d h =>
    rw [sponge.squeezeList]
    by_cases hd : d = 0
    · subst hd
      simp [BitVec.toBitsLE]
    · simp only [dite_eq_right hd, dite_eq_right (show (0 : Nat) ≠ r by omega), Nat.sub_zero,
        dite_eq_left h, sponge.outputBits]
  | case2 S d h Z rem ih =>
    rw [sponge.squeezeList]
    simp only [dite_eq_right (show d ≠ 0 by omega), dite_eq_right (show (0 : Nat) ≠ r by omega),
      Nat.sub_zero, dite_eq_right h]
    rw [sponge.squeezeList]
    simp only [dite_eq_right (show d - r ≠ 0 by omega), ↓reduceDIte]
    rw [ih, BitVec.toList_toBitsLE_cast, BitVec.toList_toBitsLE_append]
    rfl

/-- The incremental sponge agrees with SPONGE[f, pad10*1, r] (FIPS 202 Algorithm 8) on the
message `M` followed by `suffix`. -/
theorem sponge.squeeze_finalize_absorb {n m : Nat} (M : BitVec n) (suffix : BitVec m) (d : Nat) :
    (sponge.squeeze f r hr (sponge.finalize f r hr
      (sponge.absorb f r hr (sponge.init r hr) (BitVec.toBitsLE M).toList)
      (BitVec.toBitsLE suffix).toList) d).2 =
      BitVec.toBitsLE (Internal.sponge f r (suffix ++ M) d hr) := by
  have hfin : ∀ A B, sponge.finalize f r hr (sponge.absorb f r hr (sponge.init r hr) A) B =
      sponge.finalize f r hr (sponge.init r hr) (A ++ B) := by
    intro A B
    simp only [sponge.finalize]
    rw [sponge.absorb_append f r hr _ A B]
  rw [hfin, ← BitVec.toList_toBitsLE_append, sponge.finalize_init]
  apply Vector.toList_inj.mp
  simp only [sponge.squeeze, Vector.toList_mk, Internal.sponge]
  exact sponge.squeezeList_eq f r hr _ _ d

end Incremental

theorem bytesToBits_append {n m : Nat} (a : ByteVec n) (c : ByteVec m) :
    bytesToBits (a ++ c) = ((bytesToBits a) ++ (bytesToBits c)).cast (by omega) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < 8 * n
  · have hdiv : i / 8 < n := by omega
    simp [bytesToBits, Vector.getElem_append, h, hdiv]
  · have hdiv : ¬i / 8 < n := by omega
    have hd : (i - 8 * n) / 8 = i / 8 - n := by omega
    have hm : (i - 8 * n) % 8 = i % 8 := by omega
    simp [bytesToBits, Vector.getElem_append, h, hdiv, hd, hm]

private theorem bitsToBytes_append {m n : Nat}
    (a : Vector Bit (8 * m)) (c : Vector Bit (8 * n)) :
    bitsToBytes ((a ++ c).cast (by omega)) = bitsToBytes a ++ bitsToBytes c := by
  have h := congrArg (fun bits : Vector Bit (8 * (m + n)) => bitsToBytes bits)
    (bytesToBits_append (bitsToBytes a) (bitsToBytes c))
  simpa only [bitsToBytes_bytesToBits, bytesToBits_bitsToBytes] using h.symm

theorem squeeze_bytes_output_add (f : BitVec b → BitVec b) (r : Nat)
    (hr : 0 < r ∧ r < b) (s : Incremental.sponge.squeezingState r) (m n : Nat) :
    (bitsToBytes (Incremental.sponge.squeeze f r hr s (8 * m)).2).toList ++
      (bitsToBytes (Incremental.sponge.squeeze f r hr
        (Incremental.sponge.squeeze f r hr s (8 * m)).1 (8 * n)).2).toList =
      (bitsToBytes (Incremental.sponge.squeeze f r hr s (8 * (m + n))).2).toList := by
  have hbits :
      ((Incremental.sponge.squeeze f r hr s (8 * m)).2 ++
        (Incremental.sponge.squeeze f r hr (Incremental.sponge.squeeze f r hr s (8 * m)).1
          (8 * n)).2).cast (by omega) =
        (Incremental.sponge.squeeze f r hr s (8 * (m + n))).2 := by
    apply Vector.toList_inj.mp
    simp only [Vector.toList_cast, Vector.toList_append]
    have h := Incremental.sponge.squeeze_output_add f r hr s (8 * m) (8 * n)
    rw [show 8 * m + 8 * n = 8 * (m + n) by omega] at h
    exact h
  have hbytes := congrArg (fun bits : Vector Bit (8 * (m + n)) => bitsToBytes bits) hbits
  rw [bitsToBytes_append] at hbytes
  simpa only [Vector.toList_append] using congrArg Vector.toList hbytes

theorem SHAKE128.absorb_append {n m : Nat}
    (s : Incremental.sponge.absorbingState (b - 256)) (a : ByteVec n) (c : ByteVec m) :
    SHAKE128.absorb (SHAKE128.absorb s a) c = SHAKE128.absorb s (a ++ c) := by
  simp only [SHAKE128.absorb, bytesToBits_append, Vector.toList_cast, Vector.toList_append]
  exact Incremental.sponge.absorb_append _ _ _ _ _ _

theorem SHAKE256.absorb_append {n m : Nat}
    (s : Incremental.sponge.absorbingState (b - 512)) (a : ByteVec n) (c : ByteVec m) :
    SHAKE256.absorb (SHAKE256.absorb s a) c = SHAKE256.absorb s (a ++ c) := by
  simp only [SHAKE256.absorb, bytesToBits_append, Vector.toList_cast, Vector.toList_append]
  exact Incremental.sponge.absorb_append _ _ _ _ _ _

theorem SHAKE128.squeeze_state_add (s : Incremental.sponge.squeezingState (b - 256)) (m n : Nat) :
    (SHAKE128.squeeze (SHAKE128.squeeze s m).1 n).1 = (SHAKE128.squeeze s (m + n)).1 := by
  have h := Incremental.sponge.squeeze_state_add (Permutations.Keccak.keccak_f .w1600)
    (b - 256) (by decide) s (8 * m) (8 * n)
  rw [show 8 * m + 8 * n = 8 * (m + n) by omega] at h
  exact h

theorem SHAKE256.squeeze_state_add (s : Incremental.sponge.squeezingState (b - 512)) (m n : Nat) :
    (SHAKE256.squeeze (SHAKE256.squeeze s m).1 n).1 = (SHAKE256.squeeze s (m + n)).1 := by
  have h := Incremental.sponge.squeeze_state_add (Permutations.Keccak.keccak_f .w1600)
    (b - 512) (by decide) s (8 * m) (8 * n)
  rw [show 8 * m + 8 * n = 8 * (m + n) by omega] at h
  exact h

/-- Squeezing `sizes` in turn and concatenating the outputs gives one squeeze of the total length,
for any byte-level squeeze whose outputs concatenate. -/
theorem squeeze_foldl_output {σ : Type} (squeeze : σ → (n : Nat) → σ × ByteVec n)
    (hadd : ∀ s m n, (squeeze s m).2.toList ++ (squeeze (squeeze s m).1 n).2.toList =
      (squeeze s (m + n)).2.toList)
    (s : σ) (acc : List Byte) (sizes : List Nat) :
    (sizes.foldl (fun p n => ((squeeze p.1 n).1, p.2 ++ (squeeze p.1 n).2.toList)) (s, acc)).2 =
      acc ++ (squeeze s sizes.sum).2.toList := by
  induction sizes generalizing s acc with
  | nil => simp [List.eq_nil_of_length_eq_zero (Vector.length_toList (xs := (squeeze s 0).2))]
  | cons size sizes ih => simp only [List.foldl_cons, List.sum_cons, ih, List.append_assoc, hadd]

theorem SHAKE128.squeeze_output_add (s : Incremental.sponge.squeezingState (b - 256)) (m n : Nat) :
    (SHAKE128.squeeze s m).2.toList ++ (SHAKE128.squeeze (SHAKE128.squeeze s m).1 n).2.toList =
      (SHAKE128.squeeze s (m + n)).2.toList :=
  squeeze_bytes_output_add _ _ _ _ _ _

theorem SHAKE256.squeeze_output_add (s : Incremental.sponge.squeezingState (b - 512)) (m n : Nat) :
    (SHAKE256.squeeze s m).2.toList ++ (SHAKE256.squeeze (SHAKE256.squeeze s m).1 n).2.toList =
      (SHAKE256.squeeze s (m + n)).2.toList :=
  squeeze_bytes_output_add _ _ _ _ _ _

theorem SHAKE128.squeeze_chunks (s : Incremental.sponge.squeezingState (b - 256))
    (sizes : List Nat) :
    sizes.foldl (fun s n => (SHAKE128.squeeze s n).1) s =
      (SHAKE128.squeeze s sizes.sum).1 := by
  induction sizes generalizing s with
  | nil => simp [SHAKE128.squeeze, Incremental.sponge.squeeze_zero]
  | cons size sizes ih =>
    simp only [List.foldl_cons, List.sum_cons, ih, SHAKE128.squeeze_state_add]

theorem SHAKE256.squeeze_chunks (s : Incremental.sponge.squeezingState (b - 512))
    (sizes : List Nat) :
    sizes.foldl (fun s n => (SHAKE256.squeeze s n).1) s =
      (SHAKE256.squeeze s sizes.sum).1 := by
  induction sizes generalizing s with
  | nil => simp [SHAKE256.squeeze, Incremental.sponge.squeeze_zero]
  | cons size sizes ih =>
    simp only [List.foldl_cons, List.sum_cons, ih, SHAKE256.squeeze_state_add]

private theorem toVector_append (a c : Array Byte) :
    (a ++ c).toVector = (a.toVector ++ c.toVector).cast (by simp) := by
  apply Vector.ext
  intro i hi
  simp [Array.getElem_append]

private theorem bytesToBits_cast_toList {n m : Nat} (v : ByteVec n) (h : n = m) :
    (bytesToBits (v.cast h)).toList = (bytesToBits v).toList := by
  cases h
  rfl

theorem bytesToBits_array_append (a c : Array Byte) :
    (bytesToBits (a ++ c).toVector).toList =
      (bytesToBits a.toVector).toList ++ (bytesToBits c.toVector).toList := by
  rw [toVector_append, bytesToBits_cast_toList, bytesToBits_append]
  simp only [Vector.toList_cast, Vector.toList_append]

/-- Byte-input chunking gives the same state (cf. FIPS 203 §4.1, Eq. (4.6)). -/
theorem SHAKE128.absorb_chunks (s : Incremental.sponge.absorbingState (b - 256))
    (chunks : List (Array Byte)) :
    chunks.foldl (fun s c => SHAKE128.absorb s c.toVector) s =
      SHAKE128.absorb s (chunks.foldr (· ++ ·) #[]).toVector := by
  induction chunks generalizing s with
  | nil =>
    change s = Incremental.sponge.absorb _ _ _ s []
    exact (Incremental.sponge.absorb_nil _ _ _ s).symm
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    simp only [SHAKE128.absorb, bytesToBits_array_append]
    exact Incremental.sponge.absorb_append _ _ _ _ _ _

/-- SHAKE256 counterpart of `SHAKE128.absorb_chunks` (FIPS 202 §6.2). -/
theorem SHAKE256.absorb_chunks (s : Incremental.sponge.absorbingState (b - 512))
    (chunks : List (Array Byte)) :
    chunks.foldl (fun s c => SHAKE256.absorb s c.toVector) s =
      SHAKE256.absorb s (chunks.foldr (· ++ ·) #[]).toVector := by
  induction chunks generalizing s with
  | nil =>
    change s = Incremental.sponge.absorb _ _ _ s []
    exact (Incremental.sponge.absorb_nil _ _ _ s).symm
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    simp only [SHAKE256.absorb, bytesToBits_array_append]
    exact Incremental.sponge.absorb_append _ _ _ _ _ _

/-- Input and output chunking give the same state (cf. FIPS 203 §4.1, Algorithm 2 and Eq. (4.6)). -/
theorem SHAKE128.chunking (chunks : List (Array Byte)) (sizes : List Nat) :
    sizes.foldl (fun s n => (SHAKE128.squeeze s n).1)
      (SHAKE128.finalize (chunks.foldl (fun s c => SHAKE128.absorb s c.toVector) SHAKE128.init)) =
      (SHAKE128.squeeze
        (SHAKE128.finalize (SHAKE128.absorb SHAKE128.init (chunks.foldr (· ++ ·) #[]).toVector))
        sizes.sum).1 := by
  rw [SHAKE128.absorb_chunks, SHAKE128.squeeze_chunks]

/-- SHAKE256 counterpart of `SHAKE128.chunking` (FIPS 202 §6.2). -/
theorem SHAKE256.chunking (chunks : List (Array Byte)) (sizes : List Nat) :
    sizes.foldl (fun s n => (SHAKE256.squeeze s n).1)
      (SHAKE256.finalize (chunks.foldl (fun s c => SHAKE256.absorb s c.toVector) SHAKE256.init)) =
      (SHAKE256.squeeze
        (SHAKE256.finalize (SHAKE256.absorb SHAKE256.init (chunks.foldr (· ++ ·) #[]).toVector))
        sizes.sum).1 := by
  rw [SHAKE256.absorb_chunks, SHAKE256.squeeze_chunks]

/-- Incremental SHAKE128 agrees with one-shot `shake128` (FIPS 202 §6.2). -/
theorem SHAKE128.squeeze_finalize_absorb {n} (msg : ByteVec n) (len : Nat) :
    (SHAKE128.squeeze (SHAKE128.finalize (SHAKE128.absorb SHAKE128.init msg)) len).2 =
      shake128 msg len := by
  simp only [SHAKE128.squeeze, SHAKE128.finalize, SHAKE128.absorb, SHAKE128.init,
    bytesToBits_eq_toBitsLE, Incremental.sponge.squeeze_finalize_absorb, bitsToBytes_eq_toBytesLE,
    BitVec.ofBitsLE_toBitsLE, shake128, shake128_bits, keccak]

/-- Incremental SHAKE256 agrees with one-shot `shake256` (FIPS 202 §6.2). -/
theorem SHAKE256.squeeze_finalize_absorb {n} (msg : ByteVec n) (len : Nat) :
    (SHAKE256.squeeze (SHAKE256.finalize (SHAKE256.absorb SHAKE256.init msg)) len).2 =
      shake256 msg len := by
  simp only [SHAKE256.squeeze, SHAKE256.finalize, SHAKE256.absorb, SHAKE256.init,
    bytesToBits_eq_toBitsLE, Incremental.sponge.squeeze_finalize_absorb, bitsToBytes_eq_toBytesLE,
    BitVec.ofBitsLE_toBitsLE, shake256, shake256_bits, keccak]

/-- Chunked absorption into SHAKE128 agrees with one-shot `shake128` on the concatenation. -/
theorem SHAKE128.absorb_chunks_squeeze (chunks : List (Array Byte)) (len : Nat) :
    (SHAKE128.squeeze (SHAKE128.finalize
      (chunks.foldl (fun s c => SHAKE128.absorb s c.toVector) SHAKE128.init)) len).2 =
      shake128 (chunks.foldr (· ++ ·) #[]).toVector len := by
  rw [SHAKE128.absorb_chunks, SHAKE128.squeeze_finalize_absorb]

/-- Chunked absorption into SHAKE256 agrees with one-shot `shake256` on the concatenation. -/
theorem SHAKE256.absorb_chunks_squeeze (chunks : List (Array Byte)) (len : Nat) :
    (SHAKE256.squeeze (SHAKE256.finalize
      (chunks.foldl (fun s c => SHAKE256.absorb s c.toVector) SHAKE256.init)) len).2 =
      shake256 (chunks.foldr (· ++ ·) #[]).toVector len := by
  rw [SHAKE256.absorb_chunks, SHAKE256.squeeze_finalize_absorb]

/-- Any sequence of squeezes from incremental SHAKE128 outputs a prefix of one-shot `shake128`. -/
theorem SHAKE128.squeezes_finalize_absorb {n} (msg : ByteVec n) (sizes : List Nat) :
    (sizes.foldl
      (fun p len => ((SHAKE128.squeeze p.1 len).1, p.2 ++ (SHAKE128.squeeze p.1 len).2.toList))
      (SHAKE128.finalize (SHAKE128.absorb SHAKE128.init msg), [])).2 =
      (shake128 msg sizes.sum).toList := by
  rw [squeeze_foldl_output _ SHAKE128.squeeze_output_add, SHAKE128.squeeze_finalize_absorb,
    List.nil_append]

/-- Chunked absorption and any sequence of squeezes from SHAKE128 agree with one-shot `shake128`. -/
theorem SHAKE128.absorb_chunks_squeezes (chunks : List (Array Byte)) (sizes : List Nat) :
    (sizes.foldl
      (fun p len => ((SHAKE128.squeeze p.1 len).1, p.2 ++ (SHAKE128.squeeze p.1 len).2.toList))
      (SHAKE128.finalize (chunks.foldl (fun s c => SHAKE128.absorb s c.toVector) SHAKE128.init),
        [])).2 =
      (shake128 (chunks.foldr (· ++ ·) #[]).toVector sizes.sum).toList := by
  rw [SHAKE128.absorb_chunks, SHAKE128.squeezes_finalize_absorb]

/-- Any sequence of squeezes from incremental SHAKE256 outputs a prefix of one-shot `shake256`. -/
theorem SHAKE256.squeezes_finalize_absorb {n} (msg : ByteVec n) (sizes : List Nat) :
    (sizes.foldl
      (fun p len => ((SHAKE256.squeeze p.1 len).1, p.2 ++ (SHAKE256.squeeze p.1 len).2.toList))
      (SHAKE256.finalize (SHAKE256.absorb SHAKE256.init msg), [])).2 =
      (shake256 msg sizes.sum).toList := by
  rw [squeeze_foldl_output _ SHAKE256.squeeze_output_add, SHAKE256.squeeze_finalize_absorb,
    List.nil_append]

/-- Chunked absorption and any sequence of squeezes from SHAKE256 agree with one-shot `shake256`. -/
theorem SHAKE256.absorb_chunks_squeezes (chunks : List (Array Byte)) (sizes : List Nat) :
    (sizes.foldl
      (fun p len => ((SHAKE256.squeeze p.1 len).1, p.2 ++ (SHAKE256.squeeze p.1 len).2.toList))
      (SHAKE256.finalize (chunks.foldl (fun s c => SHAKE256.absorb s c.toVector) SHAKE256.init),
        [])).2 =
      (shake256 (chunks.foldr (· ++ ·) #[]).toVector sizes.sum).toList := by
  rw [SHAKE256.absorb_chunks, SHAKE256.squeezes_finalize_absorb]

end Wychelean.Hashes.SHA3
