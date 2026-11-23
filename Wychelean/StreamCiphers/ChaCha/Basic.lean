module

public import Wychelean.Utils.Bitwise
public import Wychelean.Utils.Bytes

/-!
# ChaCha
Specification of the ChaCha20 stream cipher as defined in RFC 8439 §2.1–§2.4.
https://www.rfc-editor.org/rfc/rfc8439.html#section-2

The RFC 8439 state layout and ChaCha20 cipher are built on top.
-/

@[expose] public section

namespace Wychelean.StreamCiphers.ChaCha

/-- Number of 32-bit words in the ChaCha state (§2.2). -/
abbrev stateWords : Nat := 16
/-- Size in bytes of a serialized state, i.e., a keystream block (§2.3). -/
abbrev blockBytes : Nat := 4 * stateWords
/-- Size of the key in bytes (§2.3). -/
abbrev keyBytes : Nat := 32
/-- Size of the RFC 8439 nonce in bytes (§2.3). -/
abbrev nonceBytes : Nat := 12

/-- The ChaCha state: sixteen 32-bit words, viewed as a 4×4 matrix in row-major order (§2.2). -/
abbrev State := Vector UInt32 stateWords

/-! ## Words and bytes -/

/-- Read `4 * n` bytes as `n` little-endian 32-bit words (§2.3). -/
def wordsOfBytesLE {n : Nat} (v : ByteVec (4 * n)) : Vector UInt32 n :=
  Vector.ofFn fun i => ⟨BitVec.ofBytesLE (Vector.ofFn fun (j : Fin 4) => v[4 * i.val + j.val])⟩

/-- Write `n` 32-bit words as `4 * n` bytes, each word little-endian (§2.3, "serialize"). -/
def wordsToBytesLE {n : Nat} (ws : Vector UInt32 n) : ByteVec (4 * n) :=
  Vector.ofFn fun i => (ws[i.val / 4] >>> (8 * (i.val % 4)).toUInt32).toUInt8

/-! ## The block function -/

/-- The quarter round on four words (§2.1):
```
a += b; d ^= a; d <<<= 16;
c += d; b ^= c; b <<<= 12;
a += b; d ^= a; d <<<= 8;
c += d; b ^= c; b <<<= 7;
```
-/
def quarterRound (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b; let d := (d ^^^ a).rotl 16
  let c := c + d; let b := (b ^^^ c).rotl 12
  let a := a + b; let d := (d ^^^ a).rotl 8
  let c := c + d; let b := (b ^^^ c).rotl 7
  (a, b, c, d)

/-- `QUARTERROUND(x, y, z, w)`: the quarter round on the words of the state at indices `x`, `y`,
`z` and `w`, leaving the others alone (§2.2). -/
def qround (x y z w : Fin stateWords) (s : State) : State :=
  let (a, b, c, d) := quarterRound s[x] s[y] s[z] s[w]
  ((s.set x a).set y b |>.set z c).set w d

/-- A column round: quarter rounds on each column of the state matrix (§2.3). -/
def columnRound (s : State) : State :=
  s |> qround 0 4 8 12 |> qround 1 5 9 13 |> qround 2 6 10 14 |> qround 3 7 11 15

/-- A diagonal round: quarter rounds on each diagonal of the state matrix (§2.3). -/
def diagonalRound (s : State) : State :=
  s |> qround 0 5 10 15 |> qround 1 6 11 12 |> qround 2 7 8 13 |> qround 3 4 9 14

/-- `inner_block` from §2.3.1: a column round followed by a diagonal round. -/
def doubleRound (s : State) : State := diagonalRound (columnRound s)

/-- Apply `numRounds` rounds to the state, alternating column and diagonal rounds, starting with a
column round (§2.3). ChaCha20 is `numRounds = 20`, i.e., 10 double rounds. -/
def rounds (numRounds : Nat) (s : State) : State :=
  Fin.foldl numRounds (fun s i => if i.val % 2 = 0 then columnRound s else diagonalRound s) s

/-- The ChaCha block function with `numRounds` rounds on an arbitrary input state: run the rounds,
then add the input state word-wise modulo `2 ^ 32` (§2.3). The result is a state, before
serialization. This is the reusable core: it fixes no layout of constants, key, counter or nonce. -/
def block (numRounds : Nat) (s : State) : State :=
  Vector.zipWith (· + ·) (rounds numRounds s) s

/-! ## RFC 8439 layout -/

/-- The constants in words 0–3: "expa", "nd 3", "2-by", "te k" (§2.3). -/
def constants : Vector UInt32 4 := #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- The initial state for RFC 8439 ChaCha: constants in words 0–3, the key in words 4–11, the
block counter in word 12, and the nonce in words 13–15, all read as little-endian words (§2.3). -/
def initState (key : ByteVec keyBytes) (counter : UInt32) (nonce : ByteVec nonceBytes) : State :=
  (constants ++ wordsOfBytesLE (n := 8) key ++ #v[counter] ++ wordsOfBytesLE (n := 3) nonce).cast
    (by decide)

/-- The RFC 8439 ChaCha block function with `numRounds` rounds: 64 keystream bytes for the given
key, block counter and nonce, serialized with each word little-endian (§2.3). -/
def chachaBlock (numRounds : Nat) (key : ByteVec keyBytes) (counter : UInt32)
    (nonce : ByteVec nonceBytes) : ByteVec blockBytes :=
  wordsToBytesLE (block numRounds (initState key counter nonce))

/-- `chacha20_block(key, counter, nonce)` (§2.3.1). -/
def chacha20Block (key : ByteVec keyBytes) (counter : UInt32) (nonce : ByteVec nonceBytes) :
    ByteVec blockBytes :=
  chachaBlock 20 key counter nonce

/-! ## RFC 8439 encryption -/

/-- Number of keystream blocks needed to cover `n` bytes. -/
abbrev numBlocks (n : Nat) : Nat := (n + blockBytes - 1) / blockBytes

/-- The keystream for `m` blocks: the serialized blocks for counters `counter, …, counter + m - 1`,
concatenated (§2.4). Requires that the counter does not wrap. -/
def keystream (numRounds : Nat) (key : ByteVec keyBytes) (counter : UInt32)
    (nonce : ByteVec nonceBytes) (m : Nat) (_ : counter.toNat + m ≤ 2 ^ 32) :
    ByteVec (m * blockBytes) :=
  (Vector.ofFn fun (j : Fin m) =>
    chachaBlock numRounds key (counter + j.val.toUInt32) nonce).flatten

/-- RFC 8439 ChaCha encryption with `numRounds` rounds: XOR the message with the keystream
starting at block `counter`, discarding any keystream left over after the last byte (§2.4).
Decryption is the same operation. The block counter must not wrap: a single (key, nonce) pair
covers at most `2 ^ 32` blocks (§2.3). -/
def chachaEncrypt (numRounds : Nat) {n : Nat} (key : ByteVec keyBytes) (counter : UInt32)
    (nonce : ByteVec nonceBytes) (msg : ByteVec n)
    (h : counter.toNat + numBlocks n ≤ 2 ^ 32) : ByteVec n :=
  let ks := keystream numRounds key counter nonce (numBlocks n) h
  Vector.ofFn fun i => msg[i] ^^^ ks[i.val]'(by
    have := i.isLt; simp only [numBlocks, blockBytes, stateWords] at *; omega)

/-- `chacha20_encrypt(key, counter, nonce, plaintext)` (§2.4.1). -/
def chacha20 {n : Nat} (key : ByteVec keyBytes) (counter : UInt32) (nonce : ByteVec nonceBytes)
    (msg : ByteVec n) (h : counter.toNat + numBlocks n ≤ 2 ^ 32) : ByteVec n :=
  chachaEncrypt 20 key counter nonce msg h

end Wychelean.StreamCiphers.ChaCha
