module

public import Wychelean.Utils.Bits
public import Wychelean.Utils.Bitwise
public import Wychelean.Utils.Bytes
public import Wychelean.Utils.PolyRing.ModMonic

/-!
# Rijndael
Rijndael, the block cipher standardized as AES.

Section, equation, table and algorithm numbers refer to FIPS 197 (update 1), which specifies AES.
AES is just Rijndael with a 4-word block (`Nb = 4`) and a 4-, 6- or 8-word key (`Nk = 4, 6, 8`).
Page numbers ("proposal p. 12") refer to the Rijndael AES proposal (document version 2, 03/09/99),
which also defines 6- and 8-word blocks (§4) and 5- and 7-word blocks and keys (§12.1, p. 42). We
follow the notation of FIPS 197, and where it fixes the block at 4 words we generalize `4` to `Nb`,
citing the page of the proposal that does the same.

https://doi.org/10.6028/NIST.FIPS.197-upd1
https://csrc.nist.gov/csrc/media/projects/cryptographic-standards-and-guidelines/documents/aes-development/rijndael-ammended.pdf
-/

@[expose] public section

namespace Wychelean.BlockCiphers.Rijndael
open Wychelean Wychelean.Utils.PolyRing
open scoped Wychelean.Notations

attribute [local grind →] Membership.mem.upper
attribute [local grind =] Std.Rco.mem_toList_iff_mem Std.Rco.mem_iff

/-- Elementwise XOR, for words and states. -/
scoped instance [XorOp α] : XorOp (Vector α n) := ⟨Vector.zipWith (· ^^^ ·)⟩

/-! ## Parameters -/

/-- The block lengths: 128 bits (FIPS 197), 192 and 256 bits (proposal p. 12), and 160 and 224
bits (proposal p. 42). -/
inductive BlockLength where
  | b128 | b160 | b192 | b224 | b256
  deriving DecidableEq, Repr

/-- `Nb`, the number of columns of the state: the block length divided by 32 (proposal p. 8). -/
abbrev BlockLength.Nb : BlockLength → Nat
  | .b128 => 4
  | .b160 => 5
  | .b192 => 6
  | .b224 => 7
  | .b256 => 8

/-- The row shifts `C[r]`, as offsets modulo `Nb`: `C[0] = 0` (proposal p. 11) and `C[1], C[2],
C[3]` from Table 2 (proposal p. 12) and Table 8 (proposal p. 42). -/
def BlockLength.C : (b : BlockLength) → Vector (Fin b.Nb) 4
  | .b128 => #v[0, 1, 2, 3]
  | .b160 => #v[0, 1, 2, 3]
  | .b192 => #v[0, 1, 2, 3]
  | .b224 => #v[0, 1, 2, 4]
  | .b256 => #v[0, 1, 3, 4]

instance (b : BlockLength) : NeZero b.Nb := ⟨by cases b <;> decide⟩

/-- The key lengths: 128, 192 and 256 bits (Table 3), and 160 and 224 bits (proposal p. 42). -/
inductive KeyLength where
  | k128 | k160 | k192 | k224 | k256
  deriving DecidableEq, Repr

/-- `Nk`, the number of words of the key: the key length divided by 32 (proposal p. 9). -/
abbrev KeyLength.Nk : KeyLength → Nat
  | .k128 => 4
  | .k160 => 5
  | .k192 => 6
  | .k224 => 7
  | .k256 => 8

/-- `Nr = max(Nk, Nb) + 6` (proposal p. 42). For `Nk, Nb ∈ {4, 6, 8}` this is Table 1 (proposal
p. 10), and for `Nb = 4` it is Table 3. -/
abbrev rounds (k : KeyLength) (b : BlockLength) : Nat := max k.Nk b.Nb + 6

/-! ## GF(2⁸) (§4) -/

namespace GF

/-- The polynomial `b(x) = b₇x⁷ + b₆x⁶ + … + b₀` of the byte `{b₇ b₆ … b₀}` (Eq. 4.1). -/
def toPoly (b : Byte) : Poly (ZMod 2) 8 := .ofFn fun i => if b.toBitVec[i] then 1 else 0

/-- The byte of a polynomial of degree below 8 (Eq. 4.1). -/
def ofPoly (p : Poly (ZMod 2) 8) : Byte := ⟨BitVec.ofBitsLE (Vector.ofFn fun i => p[i] = 1)⟩

/-- `m(x) = x⁸ + x⁴ + x³ + x + 1` (Eq. 4.3), represented as `x⁸ + μ(x)`. -/
def μ : Poly (ZMod 2) 8 := .ofFn fun i => if i.val ∈ [4, 3, 1, 0] then 1 else 0

/-- `b(x)c(x) mod m(x)` (Eq. 4.4). -/
def mulPoly (b c : Byte) : Byte := ofPoly (Poly.mulMonic μ (toPoly b) (toPoly c))

/-- `mulPoly b c` for all bytes `b` and `c`, so that each product is computed only once. -/
def mulTable : Vector (Vector Byte 256) 256 :=
  Vector.ofFn fun b => Vector.ofFn fun c => mulPoly (.ofNat b) (.ofNat c)

/-- `b • c = b(x)c(x) mod m(x)` (Eq. 4.4), read from `mulTable`. -/
def mul (b c : Byte) : Byte := mulTable[b.toNat][c.toNat]

/-- `XTIMES(b) = b • {02}` (Eq. 4.5). -/
def xtimes (b : Byte) : Byte :=
  if b.toBitVec[7] then (b <<< 1) ^^^ 0b00011011 else b <<< 1

/-- `b⁻¹ = b²⁵⁴` (Eq. 4.11). -/
def inv (b : Byte) : Byte := Nat.repeat (mul b) 254 1

end GF

/-- A word `[a₀, a₁, a₂, a₃]` (§3.5). -/
abbrev Word := Vector Byte 4

/-- `d[i] = ⊕ⱼ a[(i - j) mod 4] • b[j]` (Eq. 4.8). `Fin 4` arithmetic performs the reduction
modulo 4. -/
def mulWord (a b : Word) : Word :=
  Vector.ofFn fun i => Fin.foldl 4 (fun d j => d ^^^ GF.mul a[i - j] b[j]) 0

/-! ## The S-box (§5.1.1, §5.3.2) -/

/-- `b̃`: `{00}` if `b = {00}`, and `b⁻¹` otherwise (Eq. 5.2). -/
def tilde (b : Byte) : Byte := if b = 0 then 0 else GF.inv b

/-- Table 4: `SBOX(b)` is the affine map of Eq. 5.3 applied to `b̃`, with `c = {01100011}`. Bit
`i` of `b̃.rotr n` is `b̃[(i + n) mod 8]`. -/
def sboxTable : Vector Byte 256 := Vector.ofFn fun i =>
  let b := tilde (.ofNat i)
  b ^^^ b.rotr 4 ^^^ b.rotr 5 ^^^ b.rotr 6 ^^^ b.rotr 7 ^^^ 0b01100011

/-- Table 6: Table 4 with inputs and outputs switched. -/
def invSboxTable : Vector Byte 256 :=
  Fin.foldl 256 (fun t i => t.set sboxTable[i].toNat (.ofNat i)) (.replicate 256 0)

def sbox (b : Byte) : Byte := sboxTable[b.toNat]

def invSbox (b : Byte) : Byte := invSboxTable[b.toNat]

/-! ## The state and its transformations (§3.4, §5.1, §5.3) -/

variable {b : BlockLength}

/-- The state: 4 rows and `Nb` columns (§3.4, with `Nb` columns as in proposal p. 8), stored as
its columns, the words `s[c]` (§3.5). -/
abbrev State (b : BlockLength) := Vector Word b.Nb

/-- `s[r, c]`: the byte of the state `s` in row `r` and column `c` (§3.4). -/
scoped syntax:max term noWs "[" term ", " term "]" : term
scoped macro_rules | `($s[$r, $c]) => `($s[$c][$r])

/-- The state `s` with `s[r, c] = f r c`. -/
def State.ofFn (f : Fin 4 → Fin b.Nb → Byte) : State b :=
  Vector.ofFn fun c => Vector.ofFn fun r => f r c

/-- `s[r, c] = in[r + 4c]` for `0 ≤ r < 4` and `0 ≤ c < Nb` (Eq. 3.6; proposal p. 9). -/
def State.ofBytes (inp : ByteVec (4 * b.Nb)) : State b :=
  State.ofFn fun r c => inp[r.val + 4 * c.val]

/-- `out[r + 4c] = s[r, c]` for `0 ≤ r < 4` and `0 ≤ c < Nb` (Eq. 3.7; proposal p. 9). -/
def State.toBytes (s : State b) : ByteVec (4 * b.Nb) := Id.run do
  let mut out := .replicate _ 0
  for hc : c in [0:b.Nb] do
    for hr : r in [0:4] do
      out := out.set (r + 4 * c) s[r, c]
  return out

/-- `SUBBYTES()`: `SBOX()` applied to each byte of the state (§5.1.1, first paragraph). -/
def subBytes (s : State b) : State b := s.map (·.map sbox)

/-- `INVSUBBYTES()`: `INVSBOX()` applied to each byte of the state (§5.3.2, first paragraph). -/
def invSubBytes (s : State b) : State b := s.map (·.map invSbox)

/-- `s'[r, c] = s[r, (c + C[r]) mod Nb]`: Eq. 5.5, with the shift `r` and the 4 columns
generalized to `C[r]` and `Nb` (proposal pp. 11–12). `Fin Nb` arithmetic performs the reduction
modulo `Nb`. -/
def shiftRows (s : State b) : State b :=
  State.ofFn fun r c => s[r, c + b.C[r]]

/-- `s'[r, c] = s[r, (c - C[r]) mod Nb]`: Eq. 5.12, generalized as `shiftRows` is (proposal
p. 12). -/
def invShiftRows (s : State b) : State b :=
  State.ofFn fun r c => s[r, c - b.C[r]]

/-- `MIXCOLUMNS()`: each column `s[c]` multiplied by the matrix of `[{02}, {01}, {01}, {03}]`
(Eqs. 5.6–5.7), for `0 ≤ c < Nb` rather than `0 ≤ c < 4` (proposal p. 12). -/
def mixColumns (s : State b) : State b := s.map (mulWord #v[0x02, 0x01, 0x01, 0x03])

/-- `INVMIXCOLUMNS()`: as `mixColumns`, with the matrix of `[{0e}, {09}, {0d}, {0b}]`
(Eqs. 5.13–5.14). -/
def invMixColumns (s : State b) : State b := s.map (mulWord #v[0x0e, 0x09, 0x0d, 0x0b])

/-- `ADDROUNDKEY()`: `s'[c] = s[c] ⊕ w[l + c]` for `0 ≤ c < Nb`, where the round key `w[l..l +
Nb - 1]` is given as `roundKey` (Eq. 5.9, with `4` generalized to `Nb` as in proposal p. 13). -/
def addRoundKey (s : State b) (roundKey : Vector Word b.Nb) : State b :=
  Vector.ofFn fun c => s[c] ^^^ roundKey[c]

/-! ## Key expansion (§5.2) -/

/-- `ROTWORD()` (Eq. 5.10). -/
def rotWord (a : Word) : Word := #v[a[1], a[2], a[3], a[0]]

/-- `SUBWORD()` (Eq. 5.11). -/
def subWord (a : Word) : Word := a.map sbox

/-- `Rcon[j] = [x^(j-1), {00}, {00}, {00}]`, the powers of `x` generated by `XTIMES()` (Table 5;
proposal p. 15 for `j > 10`). -/
def rcon (j : Nat) : Word := #v[Nat.repeat GF.xtimes (j - 1) 1, 0, 0, 0]

theorem Nk_lt (k : KeyLength) (b : BlockLength) : k.Nk < b.Nb * (rounds k b + 1) := by
  cases k <;> cases b <;> decide

/-- `KEYEXPANSION()`: Algorithm 2, producing `Nb * (Nr + 1)` words rather than `4 * (Nr + 1)`, as in
the pseudocode of proposal pp. 14–15. -/
def keyExpansion (k : KeyLength) (b : BlockLength) (key : ByteVec (4 * k.Nk)) :
    Vector Word (b.Nb * (rounds k b + 1)) := Id.run do
  let mut w := .replicate _ 0
  for h : i in [0:k.Nk] do
    w := w.set i #v[key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]]
      (by grind [Nk_lt k b])
  for h : i in [k.Nk:b.Nb * (rounds k b + 1)] do
    let mut temp := w[i - 1]
    if i % k.Nk = 0 then
      temp := subWord (rotWord temp) ^^^ rcon (i / k.Nk)
    else if k.Nk > 6 ∧ i % k.Nk = 4 then
      temp := subWord temp
    w := w.set i (w[i - k.Nk] ^^^ temp)
  return w

/-- The round key `w[Nb * round..Nb * round + Nb - 1]` (Eq. 5.9, with `4` generalized to `Nb` as in
proposal p. 15). -/
def roundKey {Nr : Nat} (w : Vector Word (b.Nb * (Nr + 1))) (round : Nat) (h : round ≤ Nr := by grind) :
    Vector Word b.Nb :=
  slice w (b.Nb * round) b.Nb (by
    have := Nat.mul_le_mul_left b.Nb h
    rw [Nat.mul_succ]; omega)

/-! ## The cipher (§5.1, §5.3) -/

/-- `CIPHER()`: Algorithm 1, with round keys of `Nb` words rather than 4 (proposal p. 16). -/
def cipher (inp : ByteVec (4 * b.Nb)) (Nr : Nat) (w : Vector Word (b.Nb * (Nr + 1))) :
    ByteVec (4 * b.Nb) := Id.run do
  let mut state := State.ofBytes inp
  state := addRoundKey state (roundKey w 0)
  for h : round in [1:Nr] do
    state := subBytes state
    state := shiftRows state
    state := mixColumns state
    state := addRoundKey state (roundKey w round)
  state := subBytes state
  state := shiftRows state
  state := addRoundKey state (roundKey w Nr)
  return state.toBytes

/-- `INVCIPHER()`: Algorithm 3, with round keys of `Nb` words rather than 4 (proposal p. 16). -/
def invCipher (inp : ByteVec (4 * b.Nb)) (Nr : Nat) (w : Vector Word (b.Nb * (Nr + 1))) :
    ByteVec (4 * b.Nb) := Id.run do
  let mut state := State.ofBytes inp
  state := addRoundKey state (roundKey w Nr)
  for h : round in (1...Nr).toList.reverse do
    state := invShiftRows state
    state := invSubBytes state
    state := addRoundKey state (roundKey w round)
    state := invMixColumns state
  state := invShiftRows state
  state := invSubBytes state
  state := addRoundKey state (roundKey w 0)
  return state.toBytes

/-- Rijndael with key length `k` and block length `b`: Eq. 5.1, with `Nr = max(Nk, Nb) + 6`
(proposal p. 42). -/
def rijndael (k : KeyLength) (b : BlockLength) (inp : ByteVec (4 * b.Nb))
    (key : ByteVec (4 * k.Nk)) : ByteVec (4 * b.Nb) :=
  cipher inp (rounds k b) (keyExpansion k b key)

/-- The inverse of `rijndael k b`. -/
def rijndaelInv (k : KeyLength) (b : BlockLength) (inp : ByteVec (4 * b.Nb))
    (key : ByteVec (4 * k.Nk)) : ByteVec (4 * b.Nb) :=
  invCipher inp (rounds k b) (keyExpansion k b key)

/-! ## AES (Table 3) -/

def aes128 (inp key : ByteVec 16) : ByteVec 16 := rijndael .k128 .b128 inp key
def aes192 (inp : ByteVec 16) (key : ByteVec 24) : ByteVec 16 := rijndael .k192 .b128 inp key
def aes256 (inp : ByteVec 16) (key : ByteVec 32) : ByteVec 16 := rijndael .k256 .b128 inp key

def aes128Inv (inp key : ByteVec 16) : ByteVec 16 := rijndaelInv .k128 .b128 inp key
def aes192Inv (inp : ByteVec 16) (key : ByteVec 24) : ByteVec 16 := rijndaelInv .k192 .b128 inp key
def aes256Inv (inp : ByteVec 16) (key : ByteVec 32) : ByteVec 16 := rijndaelInv .k256 .b128 inp key

end Wychelean.BlockCiphers.Rijndael
