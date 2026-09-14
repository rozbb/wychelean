import Wychelean.KEM.MLKEM
import RunTests.Basic
import RunTests.Parser.Wycheproof

/-!
# ML-KEM Wycheproof known-answer tests

Project Wycheproof's ML-KEM vectors, which carry the adversarial coverage: encapsulation keys
whose coefficients are not reduced modulo `q` (the §7.2 modulus check), decapsulation keys with
a corrupted hash or embedded key (the §7.3 hash check), keys, seeds and ciphertexts of the wrong
length, malleable ciphertexts, and ciphertexts that must take the implicit-rejection path.
All four file kinds drive the internal API of FIPS 203 (§6) with explicit seeds and messages:

- `mlkem_*_keygen_seed_test.json`: `KeyGen` from the seed `d ‖ z` must give the expected keys.
- `mlkem_*_test.json`: `KeyGen_internal` from the seed, then `Decaps` of the given ciphertext
  must give the expected shared key.
- `mlkem_*_encaps_test.json`: `Encaps` with the given message must give the expected shared key
  and ciphertext, or reject the encapsulation key.
- `mlkem_*_semi_expanded_decaps_test.json`: `Decaps` with an explicit decapsulation key.

A case marked `invalid` must be rejected, which here means a length that does not fit the
parameter set, or `Encaps`/`Decaps` returning `none`. A `valid` case must be accepted and give
the expected answer. Malformed expected values are reported as fixture problems, never as a
pass, and the random tapes returned by `KeyGen` and `Encaps` are checked to have advanced by
exactly the bytes those algorithms read.
-/

namespace Wychelean.KEM.MLKEM.Tests

open RunTests RunTests.Parser RunTests.Parser.Wycheproof

private def vectorDir : System.FilePath := "Wychelean/KEM/MLKEM/TestVectors"

private def parameterSet : String → Except String ParameterSet
  | "ML-KEM-512" => .ok .ML_KEM_512
  | "ML-KEM-768" => .ok .ML_KEM_768
  | "ML-KEM-1024" => .ok .ML_KEM_1024
  | other => .error s!"unknown parameter set {other}"

/-- A random tape that replays `bytes`, as the RBG of §3.3 would deliver them. -/
private def tapeOf (bytes : Array UInt8) : RandomTape := fun i => bytes[i]?.getD 0

/-- Bytes of a tape, to check how far a call advanced it. -/
private def tapeBytes (tape : RandomTape) (n : Nat) : Vector UInt8 n := Vector.ofFn fun i => tape i

/-- What the specification did with a case's inputs. -/
private inductive Outcome where
  /-- The input was rejected: a length that does not fit the parameter set, or `none` from
  `Encaps`/`Decaps`. -/
  | rejected (reason : String)
  /-- The input was accepted; the comparisons against the expected outputs, or a description of
  a malformed fixture. -/
  | accepted (checks : Except String (List Test))

/-- Reinterpret an input as a fixed-length vector, rejecting the case otherwise. -/
private def input (n : Nat) (bytes : Array UInt8) : Except Outcome (Vector UInt8 n) :=
  (toFixed n bytes).mapError .rejected

/-- Combine a case's expected result with the outcome: `invalid` must be rejected; `valid` must
be accepted and match; `acceptable` may be rejected but must match if accepted. A malformed
expected value is a fixture problem, never a pass. -/
private def judge (c : Case α) (run : Except Outcome Unit) : Test :=
  let outcome := match run with
    | .error o => o
    | .ok () => .accepted (.error "no outcome recorded")
  match c.result, outcome with
  | .invalid, .rejected _ => { name := c.name, failure := none }
  | .invalid, .accepted _ => { name := c.name, failure := some "expected the input to be rejected" }
  | .acceptable, .rejected _ => { name := c.name, failure := none }
  | .valid, .rejected reason => { name := c.name, failure := some s!"rejected: {reason}" }
  | _, .accepted (.error problem) => { name := c.name, failure := some s!"fixture: {problem}" }
  | _, .accepted (.ok tests) =>
    { name := c.name,
      failure := (tests.find? (·.failure.isSome)).bind fun t => t.failure.map (s!"{t.name}: {·}") }

/-- Finish a run: the input was accepted, the comparisons are `checks`. -/
private def accept (checks : Except String (List Test)) : Except Outcome Unit :=
  .error (.accepted checks)

/-! ## Case payloads -/

private structure KeyGenCase where
  seed : Array UInt8
  ek : Array UInt8
  dk : Array UInt8

private def KeyGenCase.ofJson (j : Lean.Json) : Except String KeyGenCase := do
  return { seed := ← getHexBytes j "seed", ek := ← getHexBytes j "ek", dk := ← getHexBytes j "dk" }

private def KeyGenCase.run (p : ParameterSet) (c : KeyGenCase) : Except Outcome Unit := do
  let seed ← input 64 c.seed
  let (ek', dk', tape) := KeyGen p (tapeOf (seed.toArray ++ #[0xa5, 0x5a]))
  accept do
    let ek ← toFixed (ekLen p) c.ek
    let dk ← toFixed (dkLen p) c.dk
    return [check "ek" ek ek', check "dk" dk dk',
            check "tape advanced by 64 bytes" #v[0xa5, 0x5a] (tapeBytes tape 2)]

private structure KemCase where
  seed : Array UInt8
  ek : Option (Array UInt8)
  c : Array UInt8
  K : Array UInt8

private def KemCase.ofJson (j : Lean.Json) : Except String KemCase := do
  return { seed := ← getHexBytes j "seed", ek := ← getHexBytes? j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes j "K" }

private def KemCase.run (p : ParameterSet) (c : KemCase) : Except Outcome Unit := do
  let seed ← input 64 c.seed
  let (ek', dk) := KeyGen_internal p (slice seed 0 32) (slice seed 32 32)
  let ct ← input (ctLen p) c.c
  let some K' := Decaps p dk ct | throw (.rejected "decapsulation key failed its hash check")
  accept do
    let K ← toFixed 32 c.K
    let ekChecks ← match c.ek with
      | none => pure []
      | some ek => do let ek ← toFixed (ekLen p) ek; pure [check "ek" ek ek']
    return ekChecks ++ [check "K" K K']

private structure EncapsCase where
  m : Array UInt8
  ek : Array UInt8
  c : Array UInt8
  K : Array UInt8

private def EncapsCase.ofJson (j : Lean.Json) : Except String EncapsCase := do
  return { m := ← getHexBytes j "m", ek := ← getHexBytes j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes j "K" }

private def EncapsCase.run (p : ParameterSet) (c : EncapsCase) : Except Outcome Unit := do
  let m ← input 32 c.m
  let ek ← input (ekLen p) c.ek
  let some (K', c', tape) := Encaps p ek (tapeOf (m.toArray ++ #[0xa5, 0x5a]))
    | throw (.rejected "encapsulation key failed the modulus check")
  accept do
    let K ← toFixed 32 c.K
    let ct ← toFixed (ctLen p) c.c
    return [check "K" K K', check "c" ct c',
            check "tape advanced by 32 bytes" #v[0xa5, 0x5a] (tapeBytes tape 2)]

private structure DecapsCase where
  dk : Array UInt8
  ek : Array UInt8
  c : Array UInt8
  K : Option (Array UInt8)

private def DecapsCase.ofJson (j : Lean.Json) : Except String DecapsCase := do
  return { dk := ← getHexBytes j "dk", ek := ← getHexBytes j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes? j "K" }

private def DecapsCase.run (p : ParameterSet) (c : DecapsCase) : Except Outcome Unit := do
  let dk ← input (dkLen p) c.dk
  let ct ← input (ctLen p) c.c
  let some K' := Decaps p dk ct | throw (.rejected "decapsulation key failed its hash check")
  accept do
    let some K := c.K | throw "case gives no shared key"
    let K ← toFixed 32 K
    let ek ← toFixed (ekLen p) c.ek
    return [check "K" K K', check "embedded ek" ek (dkParts p dk).2.1]

/-! ## Suites -/

/-- Every `invalid` case of a group (rejected before any expensive computation), every flagged
case (the file's `notes` mark these as the edge cases, e.g. implicit rejection), and the first
`limit` others. -/
private def sample (limit : Option Nat) (cases : Array (Case α)) : Array (Case α) :=
  match limit with
  | none => cases
  | some n => Id.run do
    let mut kept := #[]
    let mut plain := 0
    for c in cases do
      if c.result == .invalid || !c.flags.isEmpty then
        kept := kept.push c
      else if plain < n then
        kept := kept.push c
        plain := plain + 1
    return kept

/-- Run a file's cases, taking the parameter set from each group's header. -/
private def suite (file : String) (type : String) (ofJson : Lean.Json → Except String α)
    (run : ParameterSet → α → Except Outcome Unit) (limit : Option Nat) : Suite where
  name := s!"ML-KEM Wycheproof {file}"
  tests := do
    let parsed ← parseFile ofJson (vectorDir / file)
    let mut tests := []
    for group in parsed.groups do
      let name ← IO.ofExcept (getField String group.header "parameterSet")
      let p ← IO.ofExcept (parameterSet name)
      unless group.type == type && file.startsWith s!"mlkem_{name.drop 7}_" do
        throw (IO.userError s!"{file}: expected {type} vectors, got {group.type} for {name}")
      tests := tests ++ ((sample limit group.cases).map fun c => judge c (run p c.data)).toList
    return tests

/-- All twelve files for the three parameter sets. A Keccak permutation costs milliseconds in this
specification and each accepted case runs hundreds of them, so by default each group contributes
its `invalid` and flagged cases and its first eight others; `full` runs every case. -/
def wycheproofSuites (full := false) : List Suite := Id.run do
  let limit := if full then none else some 8
  let mut suites := []
  for size in ["512", "768", "1024"] do
    suites := suites ++ [
      suite s!"mlkem_{size}_keygen_seed_test.json" "MLKEMKeyGen" KeyGenCase.ofJson KeyGenCase.run
        limit,
      suite s!"mlkem_{size}_test.json" "MLKEMTest" KemCase.ofJson KemCase.run limit,
      suite s!"mlkem_{size}_encaps_test.json" "MLKEMEncapsTest" EncapsCase.ofJson EncapsCase.run
        limit,
      suite s!"mlkem_{size}_semi_expanded_decaps_test.json" "MLKEMDecapsValidationTest"
        DecapsCase.ofJson DecapsCase.run limit ]
  return suites

end Wychelean.KEM.MLKEM.Tests
