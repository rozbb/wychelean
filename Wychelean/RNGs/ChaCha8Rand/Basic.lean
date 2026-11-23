module

public import Wychelean.StreamCiphers.ChaCha.Basic

/-!
# ChaCha8Rand
Specification of the ChaCha8Rand random number generator, as defined in C2SP.
https://c2sp.org/chacha8rand

Each iteration takes a 32-byte input, uses it as a ChaCha8 key with a zero nonce to produce 16
blocks, removes the final addition of the constant and counter words, and interleaves the blocks
four at a time. The last 32 bytes are the next iteration's input and the other 992 bytes are output.
-/

@[expose] public section

namespace Wychelean.RNGs.ChaCha8Rand
open StreamCiphers.ChaCha

/-- Size of the seed, and of each iteration's input, in bytes. -/
abbrev seedBytes : Nat := 32
/-- Number of rounds of the underlying ChaCha. -/
abbrev numRounds : Nat := 8
/-- Number of ChaCha blocks produced per iteration, with counters `0` to `15`. -/
abbrev blocksPerIter : Nat := 16
/-- Number of blocks interleaved together. -/
abbrev interleave : Nat := 4
/-- Bytes produced per iteration, including the next iteration's input. -/
abbrev iterBytes : Nat := blocksPerIter * blockBytes
/-- Bytes of output per iteration. -/
abbrev outputBytes : Nat := iterBytes - seedBytes

/-- Block `i` of an iteration: ChaCha8 with the input as key, a zero nonce and block counter `i`,
with the constants subtracted from words 0–3 and `i` subtracted from word 12. This skips the final
addition for the constant, nonce and counter words; the nonce words are zero. -/
def block (input : ByteVec seedBytes) (i : Fin blocksPerIter) : State :=
  let out := wordsOfBytesLE (n := stateWords)
    (chachaBlock numRounds input i.val.toUInt32 (Vector.replicate nonceBytes 0))
  Vector.ofFn fun w =>
    if h : w.val < 4 then out[w] - constants[w.val]
    else if w.val = 12 then out[w] - i.val.toUInt32
    else out[w]

/-- The 1024 bytes of an iteration, permuted so that for each sequence of four blocks, the first
four bytes of each block come first, then the next four bytes of each block, and so on. -/
def iterStream (input : ByteVec seedBytes) : ByteVec iterBytes :=
  let words : Vector UInt32 (iterBytes / 4) := Vector.ofFn fun k =>
    -- Word `k` lies in group `k / 64` of four blocks; within the group, it is word
    -- `(k % 64) / 4` of block `k % 4`.
    have := k.isLt
    (block input ⟨interleave * (k.val / (interleave * stateWords)) + k.val % interleave, by
      simp only [iterBytes, blocksPerIter, blockBytes, interleave, stateWords] at *; omega⟩)[
      (k.val % (interleave * stateWords)) / interleave]'(by
        simp only [interleave, stateWords]; omega)
  (wordsToBytesLE words).cast (by decide)

/-- One iteration: 992 bytes of output, and the 32-byte input of the next iteration. -/
def iteration (input : ByteVec seedBytes) : ByteVec outputBytes × ByteVec seedBytes :=
  let stream := iterStream input
  ((stream.take outputBytes).cast (by decide), (stream.drop outputBytes).cast (by decide))

/-- The output of `n` iterations starting from `seed`, concatenated. -/
def iterations (seed : ByteVec seedBytes) : (n : Nat) → ByteVec (n * outputBytes)
  | 0 => (#v[] : ByteVec 0).cast (by simp)
  | n + 1 =>
    let (out, next) := iteration seed
    (out ++ iterations next n).cast (by rw [Nat.succ_mul, Nat.add_comm])

/-- The first `len` bytes of ChaCha8Rand output from `seed`. -/
def chacha8rand (seed : ByteVec seedBytes) (len : Nat) : ByteVec len :=
  let n := (len + outputBytes - 1) / outputBytes
  let out := iterations seed n
  Vector.ofFn fun i => out[i.val]'(by
    have := i.isLt
    simp only [n, outputBytes, iterBytes, blocksPerIter, blockBytes, seedBytes, stateWords] at *
    have := Nat.lt_div_mul_add (a := len + 992 - 1) (b := 992) (by decide)
    omega)

end Wychelean.RNGs.ChaCha8Rand
