module

public import Wychelean.Hashes.SHA3.XOF.Properties
public import Wychelean.Hashes.TurboSHAKE.XOF.Basic

/-!
# Properties of incremental TurboSHAKE

Splitting the input across `absorb` calls, or the output across `squeeze` calls, does not change
the result, and the incremental API agrees with the one-shot functions. These are the SHAKE
properties of `Wychelean.Hashes.SHA3.XOF.Properties`, with KP in place of Keccak-f.
-/

@[expose] public section

namespace Wychelean.Hashes.TurboSHAKE
open Wychelean Hashes.SHA3 Hashes.SHA3.Internal Internal

theorem TurboSHAKE128.absorb_append {n m : Nat}
    (s : Incremental.sponge.absorbingState (b - 256)) (a : ByteVec n) (c : ByteVec m) :
    TurboSHAKE128.absorb (TurboSHAKE128.absorb s a) c = TurboSHAKE128.absorb s (a ++ c) := by
  simp only [TurboSHAKE128.absorb, bytesToBits_append, Vector.toList_cast, Vector.toList_append]
  exact Incremental.sponge.absorb_append _ _ _ _ _ _

theorem TurboSHAKE128.squeeze_state_add (s : Incremental.sponge.squeezingState (b - 256))
    (m n : Nat) :
    (TurboSHAKE128.squeeze (TurboSHAKE128.squeeze s m).1 n).1 =
      (TurboSHAKE128.squeeze s (m + n)).1 := by
  have h := Incremental.sponge.squeeze_state_add KP (b - 256) (by decide) s (8 * m) (8 * n)
  rw [show 8 * m + 8 * n = 8 * (m + n) by omega] at h
  exact h

theorem TurboSHAKE128.squeeze_output_add (s : Incremental.sponge.squeezingState (b - 256))
    (m n : Nat) :
    (TurboSHAKE128.squeeze s m).2.toList ++
      (TurboSHAKE128.squeeze (TurboSHAKE128.squeeze s m).1 n).2.toList =
        (TurboSHAKE128.squeeze s (m + n)).2.toList :=
  squeeze_bytes_output_add _ _ _ _ _ _

theorem TurboSHAKE128.squeeze_chunks (s : Incremental.sponge.squeezingState (b - 256))
    (sizes : List Nat) :
    sizes.foldl (fun s n => (TurboSHAKE128.squeeze s n).1) s =
      (TurboSHAKE128.squeeze s sizes.sum).1 := by
  induction sizes generalizing s with
  | nil => simp [TurboSHAKE128.squeeze, Incremental.sponge.squeeze_zero]
  | cons size sizes ih =>
    simp only [List.foldl_cons, List.sum_cons, ih, TurboSHAKE128.squeeze_state_add]

/-- Byte-input chunking gives the same state. -/
theorem TurboSHAKE128.absorb_chunks (s : Incremental.sponge.absorbingState (b - 256))
    (chunks : List (Array Byte)) :
    chunks.foldl (fun s c => TurboSHAKE128.absorb s c.toVector) s =
      TurboSHAKE128.absorb s (chunks.foldr (· ++ ·) #[]).toVector := by
  induction chunks generalizing s with
  | nil =>
    change s = Incremental.sponge.absorb _ _ _ s []
    exact (Incremental.sponge.absorb_nil _ _ _ s).symm
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    simp only [TurboSHAKE128.absorb, bytesToBits_array_append]
    exact Incremental.sponge.absorb_append _ _ _ _ _ _

/-- Input and output chunking give the same state, for any domain separation byte `D`. -/
theorem TurboSHAKE128.chunking (chunks : List (Array Byte)) (D : Byte) (hD : 0 < D ∧ D < 0x80)
    (sizes : List Nat) :
    sizes.foldl (fun s n => (TurboSHAKE128.squeeze s n).1)
      (TurboSHAKE128.finalize
        (chunks.foldl (fun s c => TurboSHAKE128.absorb s c.toVector) TurboSHAKE128.init) D hD) =
      (TurboSHAKE128.squeeze
        (TurboSHAKE128.finalize
          (TurboSHAKE128.absorb TurboSHAKE128.init (chunks.foldr (· ++ ·) #[]).toVector) D hD)
        sizes.sum).1 := by
  rw [TurboSHAKE128.absorb_chunks, TurboSHAKE128.squeeze_chunks]

theorem TurboSHAKE256.absorb_append {n m : Nat}
    (s : Incremental.sponge.absorbingState (b - 512)) (a : ByteVec n) (c : ByteVec m) :
    TurboSHAKE256.absorb (TurboSHAKE256.absorb s a) c = TurboSHAKE256.absorb s (a ++ c) := by
  simp only [TurboSHAKE256.absorb, bytesToBits_append, Vector.toList_cast, Vector.toList_append]
  exact Incremental.sponge.absorb_append _ _ _ _ _ _

theorem TurboSHAKE256.squeeze_state_add (s : Incremental.sponge.squeezingState (b - 512))
    (m n : Nat) :
    (TurboSHAKE256.squeeze (TurboSHAKE256.squeeze s m).1 n).1 =
      (TurboSHAKE256.squeeze s (m + n)).1 := by
  have h := Incremental.sponge.squeeze_state_add KP (b - 512) (by decide) s (8 * m) (8 * n)
  rw [show 8 * m + 8 * n = 8 * (m + n) by omega] at h
  exact h

theorem TurboSHAKE256.squeeze_output_add (s : Incremental.sponge.squeezingState (b - 512))
    (m n : Nat) :
    (TurboSHAKE256.squeeze s m).2.toList ++
      (TurboSHAKE256.squeeze (TurboSHAKE256.squeeze s m).1 n).2.toList =
        (TurboSHAKE256.squeeze s (m + n)).2.toList :=
  squeeze_bytes_output_add _ _ _ _ _ _

theorem TurboSHAKE256.squeeze_chunks (s : Incremental.sponge.squeezingState (b - 512))
    (sizes : List Nat) :
    sizes.foldl (fun s n => (TurboSHAKE256.squeeze s n).1) s =
      (TurboSHAKE256.squeeze s sizes.sum).1 := by
  induction sizes generalizing s with
  | nil => simp [TurboSHAKE256.squeeze, Incremental.sponge.squeeze_zero]
  | cons size sizes ih =>
    simp only [List.foldl_cons, List.sum_cons, ih, TurboSHAKE256.squeeze_state_add]

/-- Byte-input chunking gives the same state. -/
theorem TurboSHAKE256.absorb_chunks (s : Incremental.sponge.absorbingState (b - 512))
    (chunks : List (Array Byte)) :
    chunks.foldl (fun s c => TurboSHAKE256.absorb s c.toVector) s =
      TurboSHAKE256.absorb s (chunks.foldr (· ++ ·) #[]).toVector := by
  induction chunks generalizing s with
  | nil =>
    change s = Incremental.sponge.absorb _ _ _ s []
    exact (Incremental.sponge.absorb_nil _ _ _ s).symm
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    simp only [TurboSHAKE256.absorb, bytesToBits_array_append]
    exact Incremental.sponge.absorb_append _ _ _ _ _ _

/-- Input and output chunking give the same state, for any domain separation byte `D`. -/
theorem TurboSHAKE256.chunking (chunks : List (Array Byte)) (D : Byte) (hD : 0 < D ∧ D < 0x80)
    (sizes : List Nat) :
    sizes.foldl (fun s n => (TurboSHAKE256.squeeze s n).1)
      (TurboSHAKE256.finalize
        (chunks.foldl (fun s c => TurboSHAKE256.absorb s c.toVector) TurboSHAKE256.init) D hD) =
      (TurboSHAKE256.squeeze
        (TurboSHAKE256.finalize
          (TurboSHAKE256.absorb TurboSHAKE256.init (chunks.foldr (· ++ ·) #[]).toVector) D hD)
        sizes.sum).1 := by
  rw [TurboSHAKE256.absorb_chunks, TurboSHAKE256.squeeze_chunks]

/-- Incremental TurboSHAKE128 agrees with one-shot `turboShake128` (RFC 9861 §2). -/
theorem TurboSHAKE128.squeeze_finalize_absorb {n} (M : ByteVec n) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (L : Nat) :
    (TurboSHAKE128.squeeze (TurboSHAKE128.finalize (TurboSHAKE128.absorb TurboSHAKE128.init M) D hD)
      L).2 = turboShake128 M D L hD := by
  simp only [TurboSHAKE128.squeeze, TurboSHAKE128.finalize, TurboSHAKE128.absorb,
    TurboSHAKE128.init, bytesToBits_eq_toBitsLE, Incremental.sponge.squeeze_finalize_absorb,
    bitsToBytes_eq_toBytesLE, BitVec.ofBitsLE_toBitsLE, turboShake128, turboShake]

/-- Chunked absorption into TurboSHAKE128 agrees with one-shot `turboShake128` on the
concatenation. -/
theorem TurboSHAKE128.absorb_chunks_squeeze (chunks : List (Array Byte)) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (L : Nat) :
    (TurboSHAKE128.squeeze (TurboSHAKE128.finalize
      (chunks.foldl (fun s c => TurboSHAKE128.absorb s c.toVector) TurboSHAKE128.init) D hD) L).2 =
      turboShake128 (chunks.foldr (· ++ ·) #[]).toVector D L hD := by
  rw [TurboSHAKE128.absorb_chunks, TurboSHAKE128.squeeze_finalize_absorb]

/-- Incremental TurboSHAKE256 agrees with one-shot `turboShake256` (RFC 9861 §2). -/
theorem TurboSHAKE256.squeeze_finalize_absorb {n} (M : ByteVec n) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (L : Nat) :
    (TurboSHAKE256.squeeze (TurboSHAKE256.finalize (TurboSHAKE256.absorb TurboSHAKE256.init M) D hD)
      L).2 = turboShake256 M D L hD := by
  simp only [TurboSHAKE256.squeeze, TurboSHAKE256.finalize, TurboSHAKE256.absorb,
    TurboSHAKE256.init, bytesToBits_eq_toBitsLE, Incremental.sponge.squeeze_finalize_absorb,
    bitsToBytes_eq_toBytesLE, BitVec.ofBitsLE_toBitsLE, turboShake256, turboShake]

/-- Chunked absorption into TurboSHAKE256 agrees with one-shot `turboShake256` on the
concatenation. -/
theorem TurboSHAKE256.absorb_chunks_squeeze (chunks : List (Array Byte)) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (L : Nat) :
    (TurboSHAKE256.squeeze (TurboSHAKE256.finalize
      (chunks.foldl (fun s c => TurboSHAKE256.absorb s c.toVector) TurboSHAKE256.init) D hD) L).2 =
      turboShake256 (chunks.foldr (· ++ ·) #[]).toVector D L hD := by
  rw [TurboSHAKE256.absorb_chunks, TurboSHAKE256.squeeze_finalize_absorb]

/-- Any sequence of squeezes from incremental TurboSHAKE128 outputs a prefix of one-shot
`turboShake128`. -/
theorem TurboSHAKE128.squeezes_finalize_absorb {n} (M : ByteVec n) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (sizes : List Nat) :
    (sizes.foldl
      (fun p L => ((TurboSHAKE128.squeeze p.1 L).1, p.2 ++ (TurboSHAKE128.squeeze p.1 L).2.toList))
      (TurboSHAKE128.finalize (TurboSHAKE128.absorb TurboSHAKE128.init M) D hD, [])).2 =
      (turboShake128 M D sizes.sum hD).toList := by
  rw [squeeze_foldl_output _ TurboSHAKE128.squeeze_output_add,
    TurboSHAKE128.squeeze_finalize_absorb, List.nil_append]

/-- Chunked absorption and any sequence of squeezes from TurboSHAKE128 agree with one-shot
`turboShake128`. -/
theorem TurboSHAKE128.absorb_chunks_squeezes (chunks : List (Array Byte)) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (sizes : List Nat) :
    (sizes.foldl
      (fun p L => ((TurboSHAKE128.squeeze p.1 L).1, p.2 ++ (TurboSHAKE128.squeeze p.1 L).2.toList))
      (TurboSHAKE128.finalize
        (chunks.foldl (fun s c => TurboSHAKE128.absorb s c.toVector) TurboSHAKE128.init) D hD,
        [])).2 =
      (turboShake128 (chunks.foldr (· ++ ·) #[]).toVector D sizes.sum hD).toList := by
  rw [TurboSHAKE128.absorb_chunks, TurboSHAKE128.squeezes_finalize_absorb]

/-- Any sequence of squeezes from incremental TurboSHAKE256 outputs a prefix of one-shot
`turboShake256`. -/
theorem TurboSHAKE256.squeezes_finalize_absorb {n} (M : ByteVec n) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (sizes : List Nat) :
    (sizes.foldl
      (fun p L => ((TurboSHAKE256.squeeze p.1 L).1, p.2 ++ (TurboSHAKE256.squeeze p.1 L).2.toList))
      (TurboSHAKE256.finalize (TurboSHAKE256.absorb TurboSHAKE256.init M) D hD, [])).2 =
      (turboShake256 M D sizes.sum hD).toList := by
  rw [squeeze_foldl_output _ TurboSHAKE256.squeeze_output_add,
    TurboSHAKE256.squeeze_finalize_absorb, List.nil_append]

/-- Chunked absorption and any sequence of squeezes from TurboSHAKE256 agree with one-shot
`turboShake256`. -/
theorem TurboSHAKE256.absorb_chunks_squeezes (chunks : List (Array Byte)) (D : Byte)
    (hD : 0 < D ∧ D < 0x80) (sizes : List Nat) :
    (sizes.foldl
      (fun p L => ((TurboSHAKE256.squeeze p.1 L).1, p.2 ++ (TurboSHAKE256.squeeze p.1 L).2.toList))
      (TurboSHAKE256.finalize
        (chunks.foldl (fun s c => TurboSHAKE256.absorb s c.toVector) TurboSHAKE256.init) D hD,
        [])).2 =
      (turboShake256 (chunks.foldr (· ++ ·) #[]).toVector D sizes.sum hD).toList := by
  rw [TurboSHAKE256.absorb_chunks, TurboSHAKE256.squeezes_finalize_absorb]

end Wychelean.Hashes.TurboSHAKE
