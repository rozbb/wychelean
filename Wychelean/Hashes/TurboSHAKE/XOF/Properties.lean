import Wychelean.Hashes.SHA3.XOF.Properties
import Wychelean.Hashes.TurboSHAKE.XOF.Basic

/-!
# Chunking properties of incremental TurboSHAKE

Splitting the input across `absorb` calls, or the output across `squeeze` calls, does not change
the result. These are the SHAKE properties of `Wychelean.Hashes.SHA3.XOF.Properties`, with KP in
place of Keccak-f.
-/

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

end Wychelean.Hashes.TurboSHAKE
