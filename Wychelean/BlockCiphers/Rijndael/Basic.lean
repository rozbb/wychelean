module

public import Wychelean.Utils.Bits
public import Wychelean.Utils.Bitwise
public import Wychelean.Utils.Bytes

/-!
# Rijndael
Rijndael, the block cipher standardized as AES. Section, equation, table and algorithm numbers
refer to FIPS 197 (update 1), which specifies AES: Rijndael with 128-bit blocks (`Nb = 4`). The
192- and 256-bit blocks (`Nb = 6, 8`) follow the Rijndael AES proposal, which differs only in the
number of rounds and the row shifts.
https://doi.org/10.6028/NIST.FIPS.197-upd1
https://csrc.nist.gov/csrc/media/projects/cryptographic-standards-and-guidelines/documents/aes-development/rijndael-ammended.pdf
-/

@[expose] public section

namespace Wychelean.BlockCiphers.Rijndael
open Wychelean
open scoped Wychelean.Notations

attribute [local grind →] Membership.mem.upper

/-- Elementwise XOR, for words and states. -/
scoped instance [XorOp α] : XorOp (Vector α n) := ⟨Vector.zipWith (· ^^^ ·)⟩

/-! ## GF(2⁸) (§4) -/

namespace GF

/-- `XTIMES(b)` (Eq. 4.5). -/
def xtimes (b : Byte) : Byte :=
  if b.toBitVec[7] then (b <<< 1) ^^^ 0x1b else b <<< 1

/-- `b • c`: the XOR of `XTIMES^i(b)` over the set bits `i` of `c` (Eqs. 4.6–4.7). -/
def mul (b c : Byte) : Byte :=
  Fin.foldl 8 (fun acc i => if c.toBitVec[i] then acc ^^^ Nat.repeat xtimes i b else acc) 0

/-- `b⁻¹ = b²⁵⁴` (Eq. 4.11). -/
def inv (b : Byte) : Byte := Nat.repeat (mul b) 254 1

end GF

/-- A word `[a₀, a₁, a₂, a₃]` (§3.5). -/
abbrev Word := Vector Byte 4

/-- `d[i] = ⊕ⱼ a[(i - j) mod 4] • b[j]` (Eq. 4.8). -/
def mulWord (a b : Word) : Word :=
  Vector.ofFn fun i => Fin.foldl 4 (fun d j => d ^^^ GF.mul a[(i.val + 4 - j.val) % 4] b[j]) 0

/-! ## The S-box (§5.1.1, §5.3.2) -/

/-- Table 4: the affine map of Eq. 5.3 applied to `b⁻¹`. -/
def sboxTable : Vector Byte 256 := Vector.ofFn fun i =>
  let b := GF.inv (.ofNat i)
  b ^^^ b.rotr 4 ^^^ b.rotr 5 ^^^ b.rotr 6 ^^^ b.rotr 7 ^^^ 0x63

/-- Table 6: Table 4 with inputs and outputs switched. -/
def invSboxTable : Vector Byte 256 :=
  Fin.foldl 256 (fun t i => t.set sboxTable[i].toNat (.ofNat i)) (.replicate 256 0)

def sbox (b : Byte) : Byte := sboxTable[b.toNat]

def invSbox (b : Byte) : Byte := invSboxTable[b.toNat]

/-! ## The state and its transformations (§3.4, §5.1, §5.3) -/

/-- `Nb` columns: `s[c][r]` is `s[r, c]` (§3.5). -/
abbrev State (Nb : Nat) := Vector Word Nb

/-- `s[r, c] = in[r + 4c]` (Eq. 3.6). -/
def State.ofBytes (inp : ByteVec (4 * Nb)) : State Nb :=
  Vector.ofFn fun c => Vector.ofFn fun r => inp[r.val + 4 * c.val]

/-- `out[r + 4c] = s[r, c]` (Eq. 3.7). -/
def State.toBytes (s : State Nb) : ByteVec (4 * Nb) :=
  Vector.ofFn fun i => s[i.val / 4][i.val % 4]

def subBytes (s : State Nb) : State Nb := s.map (·.map sbox)

def invSubBytes (s : State Nb) : State Nb := s.map (·.map invSbox)

/-- The row shifts `C[r]` (proposal, Table 2). -/
def shiftOffsets (Nb : Nat) : Vector Nat 4 :=
  if Nb = 8 then #v[0, 1, 3, 4] else #v[0, 1, 2, 3]

/-- `s'[r, c] = s[r, (c + C[r]) mod Nb]` (Eq. 5.5). -/
def shiftRows (s : State Nb) : State Nb :=
  Vector.ofFn fun c => Vector.ofFn fun r =>
    (s[(c.val + (shiftOffsets Nb)[r]) % Nb]'(Nat.mod_lt _ c.pos))[r]

/-- `s'[r, c] = s[r, (c - C[r]) mod Nb]` (Eq. 5.12). -/
def invShiftRows (s : State Nb) : State Nb :=
  Vector.ofFn fun c => Vector.ofFn fun r =>
    (s[(c.val + Nb - (shiftOffsets Nb)[r]) % Nb]'(Nat.mod_lt _ c.pos))[r]

/-- Eqs. 5.6–5.7. -/
def mixColumns (s : State Nb) : State Nb := s.map (mulWord #v[0x02, 0x01, 0x01, 0x03])

/-- Eqs. 5.13–5.14. -/
def invMixColumns (s : State Nb) : State Nb := s.map (mulWord #v[0x0e, 0x09, 0x0d, 0x0b])

/-! ## Key expansion (§5.2) -/

/-- `Nr = max(Nk, Nb) + 6` (proposal, Table 1). -/
def rounds (Nk Nb : Nat) : Nat := max Nk Nb + 6

/-- Eq. 5.10. -/
def rotWord (a : Word) : Word := #v[a[1], a[2], a[3], a[0]]

/-- Eq. 5.11. -/
def subWord (a : Word) : Word := a.map sbox

/-- `Rcon[j] = [x^(j-1), {00}, {00}, {00}]` (Table 5). -/
def rcon (j : Nat) : Word := #v[Nat.repeat GF.xtimes (j - 1) 1, 0, 0, 0]

/-- Algorithm 2, producing `Nb * (Nr + 1)` words. -/
def keyExpansion (Nk Nb : Nat) (key : ByteVec (4 * Nk)) :
    Vector Word (Nb * (rounds Nk Nb + 1)) := Id.run do
  let mut w := .replicate _ 0
  for h : i in [0:Nb * (rounds Nk Nb + 1)] do
    if _ : i < Nk then
      w := w.set i #v[key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]]
    else
      let mut temp := w[i - 1]
      if i % Nk = 0 then
        temp := subWord (rotWord temp) ^^^ rcon (i / Nk)
      else if Nk > 6 ∧ i % Nk = 4 then
        temp := subWord temp
      w := w.set i (w[i - Nk] ^^^ temp)
  return w

/-- Round key `round` is `w[Nb * round .. Nb * round + Nb - 1]` (Eq. 5.9). -/
def roundKeys (w : Vector Word (Nb * (Nr + 1))) : Vector (State Nb) (Nr + 1) :=
  Vector.ofFn fun round => Vector.ofFn fun c =>
    w[Nb * round.val + c.val]'(by
      have := Nat.mul_le_mul_left Nb (Nat.le_of_lt_succ round.isLt)
      rw [Nat.mul_succ]; omega)

/-! ## The cipher (§5.1, §5.3) -/

/-- Algorithm 1. -/
def cipher (inp : ByteVec (4 * Nb)) (Nr : Nat) (w : Vector Word (Nb * (Nr + 1))) :
    ByteVec (4 * Nb) := Id.run do
  let k := roundKeys w
  let mut state := State.ofBytes inp
  state := state ^^^ k[0]
  for h : round in [1:Nr] do
    state := subBytes state
    state := shiftRows state
    state := mixColumns state
    state := state ^^^ k[round]
  state := subBytes state
  state := shiftRows state
  state := state ^^^ k[Nr]
  return state.toBytes

/-- Algorithm 3, with `round` running from `Nr - 1` down to `1`. -/
def invCipher (inp : ByteVec (4 * Nb)) (Nr : Nat) (w : Vector Word (Nb * (Nr + 1))) :
    ByteVec (4 * Nb) := Id.run do
  let k := roundKeys w
  let mut state := State.ofBytes inp
  state := state ^^^ k[Nr]
  for i in [1:Nr] do
    let round := Nr - i
    state := invShiftRows state
    state := invSubBytes state
    state := state ^^^ k[round]
    state := invMixColumns state
  state := invShiftRows state
  state := invSubBytes state
  state := state ^^^ k[0]
  return state.toBytes

/-- Rijndael with an `Nk`-word key and an `Nb`-word block (Eq. 5.1). -/
def rijndael (Nk Nb : Nat) (inp : ByteVec (4 * Nb)) (key : ByteVec (4 * Nk))
    (_ : Nk ∈ [4, 6, 8] ∧ Nb ∈ [4, 6, 8] := by decide) : ByteVec (4 * Nb) :=
  cipher inp (rounds Nk Nb) (keyExpansion Nk Nb key)

/-- The inverse of `rijndael Nk Nb`. -/
def rijndaelInv (Nk Nb : Nat) (inp : ByteVec (4 * Nb)) (key : ByteVec (4 * Nk))
    (_ : Nk ∈ [4, 6, 8] ∧ Nb ∈ [4, 6, 8] := by decide) : ByteVec (4 * Nb) :=
  invCipher inp (rounds Nk Nb) (keyExpansion Nk Nb key)

/-! ## AES (Table 3) -/

def aes128 (inp key : ByteVec 16) : ByteVec 16 := rijndael 4 4 inp key
def aes192 (inp : ByteVec 16) (key : ByteVec 24) : ByteVec 16 := rijndael 6 4 inp key
def aes256 (inp : ByteVec 16) (key : ByteVec 32) : ByteVec 16 := rijndael 8 4 inp key

def aes128Inv (inp key : ByteVec 16) : ByteVec 16 := rijndaelInv 4 4 inp key
def aes192Inv (inp : ByteVec 16) (key : ByteVec 24) : ByteVec 16 := rijndaelInv 6 4 inp key
def aes256Inv (inp : ByteVec 16) (key : ByteVec 32) : ByteVec 16 := rijndaelInv 8 4 inp key

end Wychelean.BlockCiphers.Rijndael
