import Wychelean.Hashes.TurboSHAKE

/-!
# KangarooTwelve: KT128 and KT256
RFC 9861 §3: https://www.rfc-editor.org/rfc/rfc9861.html#section-3
One-shot byte-oriented specifications, including customization and tree hashing.
-/
namespace Wychelean.Hashes.KangarooTwelve
open Wychelean

/-- RFC 9861 §3.3: the integer uses at most 255 bytes, followed by its one-byte length. -/
abbrev lengthLimit : Nat := 256 ^ 255

def lengthBytes (x : Nat) : Nat := if x = 0 then 0 else Nat.log 256 x + 1

theorem lengthBytes_lt (x : Nat) (h : x < lengthLimit) : lengthBytes x < 256 := by
  unfold lengthBytes
  split
  · decide
  · rename_i hx
    have := Nat.log_lt_of_lt_pow hx h
    omega

/-- RFC 9861 §3.3: minimal big-endian integer bytes followed by their count; zero encodes as 00.
The precondition rules out an overflowing length byte. -/
def length_encode (x : Nat) (_h : x < lengthLimit) : Vector UInt8 (lengthBytes x + 1) :=
  Vector.ofFn fun i => if i.val < lengthBytes x then
    UInt8.ofNat (x / 256 ^ (lengthBytes x - 1 - i.val))
  else UInt8.ofNat (lengthBytes x)

/-- RFC 9861 §3.2: each message chunk contains at most 8192 bytes. -/
abbrev chunkSize : Nat := 8192

/-- Number of chunks after the first, for S=M||C||length_encode(|C|). -/
def chainingValueCount (m c : Nat) : Nat := (m + c + lengthBytes c) / chunkSize

/-- RFC 9861 §§3.2 and 3.4: leaf CVs are 32 bytes for KT128 and 64 for KT256. -/
def chainingValueSize (strength256 : Bool) : Nat := if strength256 then 64 else 32

/-- Construct the final node and its domain byte. Chunking is applied to the entire encoded S.
RFC 9861 §3.2: short-node D=07, leaf D=0b, final-node D=06; the divider is 03||00^7.
KT256 changes only the capacity and CV size (§3.4). -/
def finalNode (strength256 : Bool) (M : Vector UInt8 m) (C : Vector UInt8 c)
    (hC : c < lengthLimit) (hCount : chainingValueCount m c < lengthLimit) :
    Array UInt8 × TurboSHAKE.Domain := Id.run do
  let S := M.toArray ++ C.toArray ++ (length_encode c hC).toArray
  if S.size ≤ chunkSize then return (S, ⟨7, by decide⟩)
  let count := chainingValueCount m c
  let mut node := S.extract 0 chunkSize ++ #[3,0,0,0,0,0,0,0]
  for i in [0:count] do
    let chunk := S.extract (chunkSize * (i+1)) (chunkSize * (i+2))
    let cv := bitsToBytes (TurboSHAKE.bits strength256 chunk.toVector ⟨11, by decide⟩
      (8 * chainingValueSize strength256))
    node := node ++ cv.toArray
  node := node ++ (length_encode count hCount).toArray ++ #[255,255]
  return (node, ⟨6, by decide⟩)

/-- KangarooTwelve output in bits. The tree is independent of the requested output length. -/
def bits (strength256 : Bool) (M : Vector UInt8 m) (C : Vector UInt8 c) (d : Nat)
    (hC : c < lengthLimit) (hCount : chainingValueCount m c < lengthLimit) : Vector Bool d :=
  let (node, domain) := finalNode strength256 M C hC hCount
  TurboSHAKE.bits strength256 node.toVector domain d

/-- KT128, RFC 9861 §3.2. d is in bytes. -/
def KT128 (M : Vector UInt8 m) (C : Vector UInt8 c) (d : Nat)
    (hC : c < lengthLimit := by decide)
    (hCount : chainingValueCount m c < lengthLimit := by decide) : Vector UInt8 d :=
  bitsToBytes (bits false M C (8*d) hC hCount)

/-- KT256, RFC 9861 §3.4. d is in bytes. -/
def KT256 (M : Vector UInt8 m) (C : Vector UInt8 c) (d : Nat)
    (hC : c < lengthLimit := by decide)
    (hCount : chainingValueCount m c < lengthLimit := by decide) : Vector UInt8 d :=
  bitsToBytes (bits true M C (8*d) hC hCount)

/-- Byte convenience interface, with empty customization by default. -/
def kt128 (M : Vector UInt8 m) (d : Nat) (C : Array UInt8 := #[])
    (hC : C.size < lengthLimit := by decide)
    (hCount : chainingValueCount m C.size < lengthLimit := by decide) : Vector UInt8 d :=
  KT128 M C.toVector d hC hCount

def kt256 (M : Vector UInt8 m) (d : Nat) (C : Array UInt8 := #[])
    (hC : C.size < lengthLimit := by decide)
    (hCount : chainingValueCount m C.size < lengthLimit := by decide) : Vector UInt8 d :=
  KT256 M C.toVector d hC hCount

theorem bits_prefix (strength256 : Bool) (M : Vector UInt8 m) (C : Vector UInt8 c)
    (d e : Nat) (hC : c < lengthLimit) (hCount : chainingValueCount m c < lengthLimit) (h : d ≤ e) :
    slice (bits strength256 M C e hC hCount) 0 d (by omega) = bits strength256 M C d hC hCount :=
  TurboSHAKE.bits_prefix _ _ _ _ _ h

theorem KT128_prefix (M : Vector UInt8 m) (C : Vector UInt8 c) (d e : Nat)
    (hC : c < lengthLimit) (hCount : chainingValueCount m c < lengthLimit) (h : d ≤ e) :
    slice (KT128 M C e hC hCount) 0 d (by omega) = KT128 M C d hC hCount := by
  unfold KT128
  rw [← bitsToBytes_slice _ d h, bits_prefix _ _ _ _ _ _ _ (by omega)]

theorem KT256_prefix (M : Vector UInt8 m) (C : Vector UInt8 c) (d e : Nat)
    (hC : c < lengthLimit) (hCount : chainingValueCount m c < lengthLimit) (h : d ≤ e) :
    slice (KT256 M C e hC hCount) 0 d (by omega) = KT256 M C d hC hCount := by
  unfold KT256
  rw [← bitsToBytes_slice _ d h, bits_prefix _ _ _ _ _ _ _ (by omega)]

end Wychelean.Hashes.KangarooTwelve
