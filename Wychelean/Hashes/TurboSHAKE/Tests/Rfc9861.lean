import Wychelean.Hashes.TurboSHAKE
import RunTests.Basic
import RunTests.Parser.Basic

/-!
# TurboSHAKE RFC 9861 known-answer tests

The TurboSHAKE test vectors of <https://www.rfc-editor.org/rfc/rfc9861.html#section-5>, checked
against the one-shot functions and against the incremental API with several squeeze schedules.
The `ptn(17**5 bytes)` vectors run only in the full suite. We don't do the `ptn(17**6 bytes)` ones:
absorbing is quadratic in the message length, so each would take over an hour.
-/

namespace Wychelean.Hashes.TurboSHAKE.Tests
open RunTests RunTests.Parser Hashes.SHA3

/-! ## Vectors -/

/-- §5: the pattern `00 01 02 .. F9 FA`, repeated as many times as necessary and truncated to
`n` bytes. -/
private def ptn (n : Nat) : Array UInt8 := Array.ofFn fun (i : Fin n) => (i.val % 0xFB).toUInt8

/-- A vector as §5 prints it. `tail` holds the expected output string, or just last 32 bytes if
that's all the spec provided -/
private structure Kat where
  name : String
  M : Array UInt8
  D : UInt8
  L : Nat
  tail : Array UInt8

private def turboShake128Vectors : List Kat := [
  ⟨"TurboSHAKE128(M=`00`^0, D=`1F`, 32)", #[], 0x1F, 32,
    (hex! "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c").toArray⟩,
  ⟨"TurboSHAKE128(M=`00`^0, D=`1F`, 64)", #[], 0x1F, 64,
    (hex! "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c\
      3e8ccae2a4dae56c84a04c2385c03c15e8193bdf58737363321691c05462c8df").toArray⟩,
  ⟨"TurboSHAKE128(M=`00`^0, D=`1F`, 10032), last 32 bytes", #[], 0x1F, 10032,
    (hex! "a3b9b0385900ce761f22aed548e754da10a5242d62e8c658e3f3a923a7555607").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**0 bytes), D=`1F`, 32)", ptn (17 ^ 0), 0x1F, 32,
    (hex! "55cedd6f60af7bb29a4042ae832ef3f58db7299f893ebb9247247d856958daa9").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**1 bytes), D=`1F`, 32)", ptn (17 ^ 1), 0x1F, 32,
    (hex! "9c97d036a3bac819db70ede0ca554ec6e4c2a1a4ffbfd9ec269ca6a111161233").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**2 bytes), D=`1F`, 32)", ptn (17 ^ 2), 0x1F, 32,
    (hex! "96c77c279e0126f7fc07c9b07f5cdae1e0be60bdbe10620040e75d7223a624d2").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**3 bytes), D=`1F`, 32)", ptn (17 ^ 3), 0x1F, 32,
    (hex! "d4976eb56bcf118520582b709f73e1d6853e001fdaf80e1b13e0d0599d5fb372").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**4 bytes), D=`1F`, 32)", ptn (17 ^ 4), 0x1F, 32,
    (hex! "da67c7039e98bf530cf7a37830c6664e14cbab7f540f58403b1b82951318ee5c").toArray⟩,
  ⟨"TurboSHAKE128(M=ptn(17**5 bytes), D=`1F`, 32)", ptn (17 ^ 5), 0x1F, 32,
    (hex! "b97a906fbf83ef7c812517abf3b2d0aea0c4f60318ce11cf103925127f59eecd").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF FF FF`, D=`01`, 32)", #[0xFF, 0xFF, 0xFF], 0x01, 32,
    (hex! "bf323f940494e88ee1c540fe660be8a0c93f43d15ec006998462fa994eed5dab").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF`, D=`06`, 32)", #[0xFF], 0x06, 32,
    (hex! "8ec9c66465ed0d4a6c35d13506718d687a25cb05c74cca1e42501abd83874a67").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF FF FF`, D=`07`, 32)", #[0xFF, 0xFF, 0xFF], 0x07, 32,
    (hex! "b658576001cad9b1e5f399a9f77723bba05458042d68206f7252682dba3663ed").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF FF FF FF FF FF FF`, D=`0B`, 32)", #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], 0x0B, 32,
    (hex! "8deeaa1aec47ccee569f659c21dfa8e112db3cee37b18178b2acd805b799cc37").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF`, D=`30`, 32)", #[0xFF], 0x30, 32,
    (hex! "553122e2135e363c3292bed2c6421fa232bab03daa07c7d6636603286506325b").toArray⟩,
  ⟨"TurboSHAKE128(M=`FF FF FF`, D=`7F`, 32)", #[0xFF, 0xFF, 0xFF], 0x7F, 32,
    (hex! "16274cc656d44cefd422395d0f9053bda6d28e122aba15c765e5ad0e6eaf26f9").toArray⟩ ]

private def turboShake256Vectors : List Kat := [
  ⟨"TurboSHAKE256(M=`00`^0, D=`1F`, 64)", #[], 0x1F, 64,
    (hex! "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db\
      11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0").toArray⟩,
  ⟨"TurboSHAKE256(M=`00`^0, D=`1F`, 10032), last 32 bytes", #[], 0x1F, 10032,
    (hex! "abefa11630c661269249742685ec082f207265dccf2f43534e9c61ba0c9d1d75").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**0 bytes), D=`1F`, 64)", ptn (17 ^ 0), 0x1F, 64,
    (hex! "3e1712f928f8eaf1054632b2aa0a246ed8b0c378728f60bc970410155c28820e\
      90cc90d8a3006aa2372c5c5ea176b0682bf22bae7467ac94f74d43d39b0482e2").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**1 bytes), D=`1F`, 64)", ptn (17 ^ 1), 0x1F, 64,
    (hex! "b3bab0300e6a191fbe6137939835923578794ea54843f5011090fa2f3780a9e5\
      cb22c59d78b40a0fbff9e672c0fbe0970bd2c845091c6044d687054da5d8e9c7").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**2 bytes), D=`1F`, 64)", ptn (17 ^ 2), 0x1F, 64,
    (hex! "66b810db8e90780424c0847372fdc95710882fde31c6df75beb9d4cd9305cfca\
      e35e7b83e8b7e6eb4b78605880116316fe2c078a09b94ad7b8213c0a738b65c0").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**3 bytes), D=`1F`, 64)", ptn (17 ^ 3), 0x1F, 64,
    (hex! "c74ebc919a5b3b0dd1228185ba02d29ef442d69d3d4276a93efe0bf9a16a7dc0\
      cd4eabadab8cd7a5edd96695f5d360abe09e2c6511a3ec397da3b76b9e1674fb").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**4 bytes), D=`1F`, 64)", ptn (17 ^ 4), 0x1F, 64,
    (hex! "02cc3a8897e6f4f6ccb6fd46631b1f5207b66c6de9c7b55b2d1a23134a170afd\
      ac234eaba9a77cff88c1f020b73724618c5687b362c430b248cd38647f848a1d").toArray⟩,
  ⟨"TurboSHAKE256(M=ptn(17**5 bytes), D=`1F`, 64)", ptn (17 ^ 5), 0x1F, 64,
    (hex! "add53b06543e584b5823f626996aee50fe45ed15f20243a7165485acb4aa76b4\
      ffda75cedf6d8cdc95c332bd56f4b986b58bb17d1778bfc1b1a97545cdf4ec9f").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF FF FF`, D=`01`, 64)", #[0xFF, 0xFF, 0xFF], 0x01, 64,
    (hex! "d21c6fbbf587fa2282f29aea620175fb0257413af78a0b1b2a87419ce031d933\
      ae7a4d383327a8a17641a34f8a1d1003ad7da6b72dba84bb62fef28f62f12424").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF`, D=`06`, 64)", #[0xFF], 0x06, 64,
    (hex! "738d7b4e37d18b7f22ad1b5313e357e3dd7d07056a26a303c433fa3533455280\
      f4f5a7d4f700efb437fe6d281405e07be32a0a972e22e63adc1b090daefe004b").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF FF FF`, D=`07`, 64)", #[0xFF, 0xFF, 0xFF], 0x07, 64,
    (hex! "18b3b5b7061c2e67c1753a00e6ad7ed7ba1c906cf93efb7092eaf27fbeebb755\
      ae6e292493c110e48d260028492b8e09b5500612b8f2578985ded5357d00ec67").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF FF FF FF FF FF FF`, D=`0B`, 64)", #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], 0x0B, 64,
    (hex! "bb36764951ec97e9d85f7ee9a67a7718fc005cf42556be79ce12c0bde50e5736\
      d6632b0d0dfb202d1bbb8ffe3dd74cb00834fa756cb03471bab13a1e2c16b3c0").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF`, D=`30`, 64)", #[0xFF], 0x30, 64,
    (hex! "f3fe12873d34bcbb2e608779d6b70e7f86bec7e90bf113cbd4fdd0c4e2f4625e\
      148dd7ee1a52776cf77f240514d9ccfc3b5ddab8ee255e39ee389072962c111a").toArray⟩,
  ⟨"TurboSHAKE256(M=`FF FF FF`, D=`7F`, 64)", #[0xFF, 0xFF, 0xFF], 0x7F, 64,
    (hex! "abe569c1f77ec340f02705e7d37c9ab7e155516e4a6a150021d70b6fac0bb40c\
      069f9a9828a0d575cd99f9bae435ab1acf7ed9110ba97ce0388d074bac768776").toArray⟩ ]

/-! ## Suite -/

/-- One instance, through its one-shot and incremental APIs. -/
private structure Instance where
  name : String
  /-- The rate in bytes (RFC 9861 §2.2, Table 1). -/
  rate : Nat
  vectors : List Kat
  oneShot : Array UInt8 → (D : UInt8) → 0 < D ∧ D < 0x80 → (L : Nat) → ByteVec L
  State : Type
  absorb : Array UInt8 → (D : UInt8) → 0 < D ∧ D < 0x80 → State
  squeeze : State → (L : Nat) → State × ByteVec L

/-- Squeeze `L` bytes in requests of the sizes in `schedule`, cycled. -/
private def Instance.squeezeAll (inst : Instance) (s : inst.State) (L : Nat)
    (schedule : Array Nat) : Array UInt8 := Id.run do
  let mut s := s
  let mut out : Array UInt8 := #[]
  let mut k := 0
  while out.size < L do
    let (s', c) := inst.squeeze s (min schedule[k % schedule.size]! (L - out.size))
    s := s'
    out := out ++ c.toArray
    k := k + 1
  return out

/-- Squeezing schedules for testing our incremental API. This includes a constant 3-byte squeeze, as
well as a schedule which crosses the rate boundary -/
private def schedules (rate : Nat) : List (Array Nat) :=
  [#[3], #[1, rate - 1, 0, rate + 1, rate, 5, 0, 2]]

private def knownAnswers (inst : Instance) (full : Bool) : Suite where
  name := s!"{inst.name} (RFC 9861 known-answer tests)"
  tests := do
    let mut tests := #[]
    for v in inst.vectors.filter fun v => full || v.M.size < 17 ^ 5 do
      if hD : 0 < v.D ∧ v.D < 0x80 then
        let expected := toHex v.tail.toVector
        let tail (out : Array UInt8) := toHex (out.extract (v.L - v.tail.size) v.L).toVector
        tests := tests.push (check v.name expected (tail (inst.oneShot v.M v.D hD v.L).toArray))
        let s := inst.absorb v.M v.D hD
        for schedule in schedules inst.rate do
          tests := tests.push (check s!"{v.name}, incremental with requests {schedule}"
            expected (tail (inst.squeezeAll s v.L schedule)))
      else throw (IO.userError s!"{v.name}: D is not a domain separation byte")
    return tests.toList

private def turboShake128Instance : Instance where
  name := "TurboSHAKE128"
  rate := 168
  vectors := turboShake128Vectors
  oneShot M D hD L := turboShake128 M.toVector D L hD
  State := Incremental.sponge.state (Hashes.SHA3.Internal.b - 256)
  absorb M D hD := TurboSHAKE128.initAndAbsorb M.toVector D hD
  squeeze := TurboSHAKE128.squeeze

private def turboShake256Instance : Instance where
  name := "TurboSHAKE256"
  rate := 136
  vectors := turboShake256Vectors
  oneShot M D hD L := turboShake256 M.toVector D L hD
  State := Incremental.sponge.state (Hashes.SHA3.Internal.b - 512)
  absorb M D hD := TurboSHAKE256.initAndAbsorb M.toVector D hD
  squeeze := TurboSHAKE256.squeeze

/-- Every vector above; `full` adds the 1.4 MB messages. -/
def rfc9861 (full := false) : List Suite :=
  [knownAnswers turboShake128Instance full, knownAnswers turboShake256Instance full]

end Wychelean.Hashes.TurboSHAKE.Tests
