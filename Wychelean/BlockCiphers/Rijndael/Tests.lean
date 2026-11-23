module

public import Wychelean.BlockCiphers.Rijndael.Basic
public import RunTests.Basic
public import RunTests.Parser.Hex
public import RunTests.Parser.Rsp

/-! Rijndael FIPS 197 examples, NIST CAVP suites, and Rijndael with other block and key lengths. -/

namespace Wychelean.BlockCiphers.Rijndael.Tests

open RunTests RunTests.Parser RunTests.Parser.Rsp
open Std.Internal.Parsec Std.Internal.Parsec.String

private def hexOf (bytes : Array UInt8) : String := toHex bytes.toVector

private def keyLength? : Nat → Option KeyLength
  | 16 => some .k128 | 20 => some .k160 | 24 => some .k192 | 28 => some .k224 | 32 => some .k256
  | _ => none

private def blockLength? : Nat → Option BlockLength
  | 16 => some .b128 | 20 => some .b160 | 24 => some .b192 | 28 => some .b224 | 32 => some .b256
  | _ => none

/-- Rijndael, or its inverse, with the key and block lengths of `key` and `inp`. -/
private def run (inverse : Bool) (key inp : Array UInt8) : IO (Array UInt8) := do
  let some k := keyLength? key.size | throw (IO.userError s!"no Rijndael with a {key.size}-byte key")
  let some b := blockLength? inp.size
    | throw (IO.userError s!"no Rijndael with a {inp.size}-byte block")
  let key ← IO.ofExcept (toFixed (4 * k.Nk) key)
  let inp ← IO.ofExcept (toFixed (4 * b.Nb) inp)
  return (if inverse then rijndaelInv k b inp key else rijndael k b inp key).toArray

/-- Checks `f` against each record, forward on `(plaintext, ciphertext)` and inverse on
`(ciphertext, plaintext)`. -/
private def checkBoth (f : Bool → Array UInt8 → Array UInt8 → IO (Array UInt8))
    (records : List (String × Array UInt8 × Array UInt8 × Array UInt8)) : IO (List Test) :=
  records.flatMapM fun (name, key, pt, ct) => do
    return [check s!"{name}, forward" (hexOf ct) (hexOf (← f false key pt)),
            check s!"{name}, inverse" (hexOf pt) (hexOf (← f true key ct))]

/-! ## FIPS 197 -/

/-- Table 4, read row by row. -/
private def table4 : String :=
  "637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0\
   b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b275\
   09832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cf\
   d0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2\
   cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdb\
   e0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08\
   ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9e\
   e1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16"

/-- Table 6, read row by row. -/
private def table6 : String :=
  "52096ad53036a538bf40a39e81f3d7fb7ce339829b2fff87348e4344c4dee9cb\
   547b9432a6c2233dee4c950b42fac34e082ea16628d924b2765ba2496d8bd125\
   72f8f66486689816d4a45ccc5d65b6926c704850fdedb9da5e154657a78d9d84\
   90d8ab008cbcd30af7e45805b8b34506d02c1e8fca3f0f02c1afbd0301138a6b\
   3a9111414f67dcea97f2cfcef0b4e67396ac7422e7ad3585e2f937e81c75df6e\
   47f11a711d29c5896fb7620eaa18be1bfc563e4bc6d279209adbc0fe78cd5af4\
   1fdda8338807c731b11210592780ec5f60517fa919b54a0d2de57a9f93c99cef\
   a0e03b4dae2af5b0c8ebbb3c83539961172b047eba77d626e169146355210c7d"

/-- Appendix A.1–A.3: the key schedules `w₀ ‖ w₁ ‖ …`, which begin with the key. -/
private def scheduleA1 : String :=
  "2b7e151628aed2a6abf7158809cf4f3ca0fafe1788542cb123a339392a6c7605\
   f2c295f27a96b9435935807a7359f67f3d80477d4716fe3e1e237e446d7a883b\
   ef44a541a8525b7fb671253bdb0bad00d4d1c6f87c839d87caf2b8bc11f915bc\
   6d88a37a110b3efddbf98641ca0093fd4e54f70e5f5fc9f384a64fb24ea6dc4f\
   ead27321b58dbad2312bf5607f8d292fac7766f319fadc2128d12941575c006e\
   d014f9a8c9ee2589e13f0cc8b6630ca6"

private def scheduleA2 : String :=
  "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7bfe0c91f72402f5a5\
   ec12068e6c827f6b0e7a95b95c56fec24db7b4bd69b5411885a74796e92538fd\
   e75fad44bb095386485af05721efb14fa448f6d94d6dce24aa326360113b30e6\
   a25e7ed583b1cf9a27f939436a94f767c0a69407d19da4e1ec1786eb6fa64971\
   485f703222cb8755e26d135233f0b7b340beeb282f18a2596747d26b458c553e\
   a7e1466c9411f1df821f750aad07d753ca4005388fcc5006282d166abc3ce7b5\
   e98ba06f448c773c8ecc720401002202"

private def scheduleA3 : String :=
  "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4\
   9ba354118e6925afa51a8b5f2067fcdea8b09c1a93d194cdbe49846eb75d5b9a\
   d59aecb85bf3c917fee94248de8ebe96b5a9328a2678a647983122292f6c79b3\
   812c81addadf48ba24360af2fab8b46498c5bfc9bebd198e268c3ba709e04214\
   68007bacb2df331696e939e46c518d80c814e20476a9fb8a5025c02d59c58239\
   de1369676ccc5a71fa2563959674ee155886ca5d2e2f31d77e0af1fa27cf73c3\
   749c47ab18501ddae2757e4f7401905acafaaae3e4d59b349adf6acebd10190d\
   fe4890d1e6188d0b046df344706c631e"

private def flatten (w : Vector Word n) : ByteVec (n * 4) := w.flatten

def fips : Suite where
  name := "Rijndael FIPS 197 examples"
  tests := do
    let decode := fun (n : Nat) (s : String) => IO.ofExcept (fromHex (n := n) s)
    let keyB := hex! "2b7e151628aed2a6abf7158809cf4f3c"
    let inB := hex! "3243f6a8885a308d313198a2e0370734"
    let outB := hex! "3925841d02dc09fbdc118597196a0b32"
    let a1 ← decode 176 scheduleA1
    let a2 ← decode 208 scheduleA2
    let a3 ← decode 240 scheduleA3
    return [
      check "Table 4" (← decode 256 table4) sboxTable,
      check "Table 6" (← decode 256 table6) invSboxTable,
      check "Eq. 4.6" (hex! "57ae478e070e1c38")
        (Vector.ofFn fun i : Fin 8 => Nat.repeat GF.xtimes i.val 0x57),
      check "Eq. 4.6: {57} • {80}" 0x38 (GF.mul 0x57 0x80),
      check "Eq. 4.7: {57} • {13}" 0xfe (GF.mul 0x57 0x13),
      check "Eq. 4.5: XTIMES(b) = b • {02} for all b" true
        ((List.range 256).all fun b => GF.xtimes b.toUInt8 == GF.mul b.toUInt8 0x02),
      check "Eq. 4.10: b • b̃ = {01} for all b ≠ {00}" true
        ((List.range' 1 255).all fun b => GF.mul b.toUInt8 (tilde b.toUInt8) == 0x01),
      check "Table 5" (hex! "01020408102040801b36")
        (Vector.ofFn fun j : Fin 10 => (rcon (j.val + 1))[0]),
      check "Appendix A.1" a1 (flatten (keyExpansion .k128 .b128 (a1.take 16))),
      check "Appendix A.2" a2 (flatten (keyExpansion .k192 .b128 (a2.take 24))),
      check "Appendix A.3" a3 (flatten (keyExpansion .k256 .b128 (a3.take 32))),
      check "Appendix B, AES-128" outB (aes128 inB keyB),
      check "Appendix B, AES-128⁻¹" inB (aes128Inv outB keyB)
    ]

/-! ## NIST CAVP (AESAVS, ECB) -/

private def vectorDir : System.FilePath := "Wychelean/BlockCiphers/Rijndael/TestVectors"

/-- `COUNT`, `KEY`, then `PLAINTEXT` and `CIPHERTEXT` in the order of the section; returns
`(count, key, plaintext, ciphertext)`. -/
private def record (decrypt : Bool) :
    Parser (Nat × Array UInt8 × Array UInt8 × Array UInt8) := do
  let count ← field "COUNT" digits
  let key ← field "KEY" readHex
  if decrypt then
    let ct ← field "CIPHERTEXT" readHex
    return (count, key, ← field "PLAINTEXT" readHex, ct)
  else
    let pt ← field "PLAINTEXT" readHex
    return (count, key, pt, ← field "CIPHERTEXT" readHex)

/-- Labels each record with its section and its own `COUNT`. -/
private def named (sec : String)
    (records : Array (Nat × Array UInt8 × Array UInt8 × Array UInt8)) :
    List (String × Array UInt8 × Array UInt8 × Array UInt8) :=
  records.toList.map fun (count, r) => (s!"{sec} COUNT = {count}", r)

/-- The `[ENCRYPT]` and `[DECRYPT]` sections of a response file, each with `count` records. -/
private def load (dir file : String) (count : Nat) :
    IO (List (String × Array UInt8 × Array UInt8 × Array UInt8)) := do
  let parser := responseFile do
    header "ENCRYPT"
    let encrypt ← many1 (record false)
    header "DECRYPT"
    return (encrypt, ← many1 (record true))
  let (encrypt, decrypt) ← parseFile parser (vectorDir / dir / file)
  unless encrypt.size == count && decrypt.size == count do
    throw (IO.userError s!"{file}: expected {count} records per section, found \
      {encrypt.size} and {decrypt.size}")
  return named "ENCRYPT" encrypt ++ named "DECRYPT" decrypt

/-- ECB: each 16-byte block separately. -/
private def ecb (inverse : Bool) (key inp : Array UInt8) : IO (Array UInt8) := do
  unless inp.size % 16 == 0 do
    throw (IO.userError s!"{inp.size} bytes is not a whole number of blocks")
  (List.range (inp.size / 16)).foldlM
    (fun out i => return out ++ (← run inverse key (inp.extract (16 * i) (16 * i + 16)))) #[]

private def knownAnswers (dir file : String) (count : Nat) : Suite where
  name := s!"Rijndael {dir}/{file}"
  verbose := false
  tests := do checkBoth ecb (← load dir file count)

/-- AESAVS §6.4.1: each record's output is 1000 chained applications to its input. -/
private def chain (inverse : Bool) (key inp : Array UInt8) : IO (Array UInt8) :=
  (List.range 1000).foldlM (fun x _ => run inverse key x) inp

private def monteCarlo (bits : Nat) : Suite where
  name := s!"Rijndael aesmct/ECBMCT{bits}.rsp"
  verbose := false
  tests := do checkBoth chain (← load "aesmct" s!"ECBMCT{bits}.rsp" 100)

/-! ## Rijndael with other block and key lengths -/

/-- The 25 example vectors of Brian Gladman's `dev_vec.txt`, one for each pair of key and block
lengths, as listed in cryptopy: the key and plaintext are prefixes of `key` and `pt`.
https://github.com/dustcloud/smartmeshsdk/blob/a95f3e4d9e2254d59d326428fef8c77319cd4373/external_libs/cryptopy/crypto/cipher/rijndael_test.py -/
def gladman : Suite where
  name := "Rijndael Gladman examples"
  tests := do
    let key := (hex! "2b7e151628aed2a6abf7158809cf4f3c762e7160f38b4da56a784d9045190cfe").toArray
    let pt := (hex! "3243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c8").toArray
    let vectors := [
      (16, 16, "3925841d02dc09fbdc118597196a0b32"),
      (20, 16, "231d844639b31b412211cfe93712b880"),
      (24, 16, "f9fb29aefc384a250340d833b87ebc00"),
      (28, 16, "8faa8fe4dee9eb17caa4797502fc9d3f"),
      (32, 16, "1a6e6c2c662e7da6501ffb62bc9e93f3"),
      (16, 20, "16e73aec921314c29df905432bc8968ab64b1f51"),
      (20, 20, "0553eb691670dd8a5a5b5addf1aa7450f7a0e587"),
      (24, 20, "73cd6f3423036790463aa9e19cfcde894ea16623"),
      (28, 20, "601b5dcd1cf4ece954c740445340bf0afdc048df"),
      (32, 20, "579e930b36c1529aa3e86628bacfe146942882cf"),
      (16, 24, "b24d275489e82bb8f7375e0d5fcdb1f481757c538b65148a"),
      (20, 24, "738dae25620d3d3beff4a037a04290d73eb33521a63ea568"),
      (24, 24, "725ae43b5f3161de806a7c93e0bca93c967ec1ae1b71e1cf"),
      (28, 24, "bbfc14180afbf6a36382a061843f0b63e769acdc98769130"),
      (32, 24, "0ebacf199e3315c2e34b24fcc7c46ef4388aa475d66c194c"),
      (16, 28, "b0a8f78f6b3c66213f792ffd2a61631f79331407a5e5c8d3793aceb1"),
      (20, 28, "08b99944edfce33a2acb131183ab0168446b2d15e958480010f545e3"),
      (24, 28, "be4c597d8f7efe22a2f7e5b1938e2564d452a5bfe72399c7af1101e2"),
      (28, 28, "ef529598ecbce297811b49bbed2c33bbe1241d6e1a833dbe119569e8"),
      (32, 28, "02fafc200176ed05deb8edb82a3555b0b10d47a388dfd59cab2f6c11"),
      (16, 32, "7d15479076b69a46ffb3b3beae97ad8313f622f67fedb487de9f06b9ed9c8f19"),
      (20, 32, "514f93fb296b5ad16aa7df8b577abcbd484decacccc7fb1f18dc567309ceeffd"),
      (24, 32, "5d7101727bb25781bf6715b0e6955282b9610e23a43c2eb062699f0ebf5887b2"),
      (28, 32, "d56c5a63627432579e1dd308b2c8f157b40a4bfb56fea1377b25d3ed3d6dbf80"),
      (32, 32, "a49406115dfb30a40418aafa4869b7c6a886ff31602a7dd19c889dc64f7e4e7a")]
    let records ← vectors.mapM fun (keyBytes, blockBytes, ct) => do
      let ct ← IO.ofExcept (fromHex (n := blockBytes) ct)
      return (s!"{8 * keyBytes}-bit key, {8 * blockBytes}-bit block",
        key.extract 0 keyBytes, pt.extract 0 blockBytes, ct.toArray)
    checkBoth run records

/-- faest-ref's Rijndael tests (MIT):
https://github.com/faest-sign/faest-ref/blob/4fb6b71143b37764546b7c7729440d9cd8898a5e/tests/aes.cpp -/
def faestRef : Suite where
  name := "Rijndael faest-ref examples"
  tests := checkBoth run [
    ("Rijndael-192", #[0x80] ++ .replicate 23 0, .replicate 24 0,
      (hex! "564d36fdeb8bf7e275f010b2f5ee69cfeae67ea0e37e3209").toArray),
    ("Rijndael-256", #[0x80] ++ .replicate 31 0, .replicate 32 0,
      (hex! "e62abce069837b65309be4eda2c0e149fe56c07b7082d3287f592c4a4927a277").toArray)]

/-- Records per section of each known-answer file. -/
private def katCounts : List (String × Nat) :=
  [("GFSbox128", 7), ("GFSbox192", 6), ("GFSbox256", 5),
   ("KeySbox128", 21), ("KeySbox192", 24), ("KeySbox256", 16),
   ("VarKey128", 128), ("VarKey192", 192), ("VarKey256", 256),
   ("VarTxt128", 128), ("VarTxt192", 128), ("VarTxt256", 128)]

/-- All Rijndael suites. `full` adds the Monte Carlo suites (200,000 blocks per direction each:
both sections, each checked in both directions). -/
public def suites (full := false) : List Suite :=
  let default := [fips] ++
    katCounts.map (fun (name, count) => knownAnswers "KAT_AES" s!"ECB{name}.rsp" count) ++
    [128, 192, 256].map (fun bits => knownAnswers "aesmmt" s!"ECBMMT{bits}.rsp" 10) ++
    [gladman, faestRef]
  if full then default ++ [128, 192, 256].map monteCarlo else default

end Wychelean.BlockCiphers.Rijndael.Tests
