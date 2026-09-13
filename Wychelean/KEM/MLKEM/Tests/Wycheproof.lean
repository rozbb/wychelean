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
the expected answer.
-/

namespace Wychelean.KEM.MLKEM.Tests

open RunTests RunTests.Parser RunTests.Parser.Wycheproof

private def vectorDir : System.FilePath := "Wychelean/KEM/MLKEM/TestVectors"

private def parameterSet : String → Except String ParameterSet
  | "ML-KEM-512" => .ok .ML_KEM_512
  | "ML-KEM-768" => .ok .ML_KEM_768
  | "ML-KEM-1024" => .ok .ML_KEM_1024
  | other => .error s!"unknown parameter set {other}"

private abbrev ekSize (p : ParameterSet) : ℕ := 384 * k p + 32
private abbrev dkSize (p : ParameterSet) : ℕ := 768 * k p + 96
private abbrev ctSize (p : ParameterSet) : ℕ := 32 * (dᵤ p * k p + dᵥ p)

/-- A random tape that replays `bytes`, as the RBG of §3.3 would deliver them. -/
private def tapeOf (bytes : Array UInt8) : RandomTape := fun i => bytes[i]?.getD 0

/-- Combine a case's expected result with what the specification did: `.error` is a rejection,
`.ok` carries the comparisons an accepted input must pass. -/
private def judge (c : Case α) (run : Except String (List Test)) : Test :=
  match c.result, run with
  | .invalid, .error _ => { name := c.name, failure := none }
  | .invalid, .ok _ => { name := c.name, failure := some "expected the input to be rejected" }
  | _, .error reason => { name := c.name, failure := some s!"rejected: {reason}" }
  | _, .ok tests =>
    { name := c.name,
      failure := (tests.find? (·.failure.isSome)).bind fun t => t.failure.map (s!"{t.name}: {·}") }

/-! ## Case payloads -/

private structure KeyGenCase where
  seed : Array UInt8
  ek : Array UInt8
  dk : Array UInt8

private def KeyGenCase.ofJson (j : Lean.Json) : Except String KeyGenCase := do
  return { seed := ← getHexBytes j "seed", ek := ← getHexBytes j "ek", dk := ← getHexBytes j "dk" }

private def KeyGenCase.run (p : ParameterSet) (c : KeyGenCase) : Except String (List Test) := do
  let seed ← toFixed 64 c.seed
  let ek ← toFixed (ekSize p) c.ek
  let dk ← toFixed (dkSize p) c.dk
  let (ek', dk', _) := KeyGen p (tapeOf seed.toArray)
  return [check "ek" ek ek', check "dk" dk dk']

private structure KemCase where
  seed : Array UInt8
  ek : Option (Array UInt8)
  c : Array UInt8
  K : Array UInt8

private def KemCase.ofJson (j : Lean.Json) : Except String KemCase := do
  return { seed := ← getHexBytes j "seed", ek := ← getHexBytes? j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes j "K" }

private def KemCase.run (p : ParameterSet) (c : KemCase) : Except String (List Test) := do
  let seed ← toFixed 64 c.seed
  let (ek', dk) := KeyGen_internal p (slice seed 0 32) (slice seed 32 32)
  let ct ← toFixed (ctSize p) c.c
  let K ← toFixed 32 c.K
  let some K' := Decaps p dk ct | throw "decapsulation key failed its hash check"
  let ekChecks ← match c.ek with
    | none => pure []
    | some ek => do let ek ← toFixed (ekSize p) ek; pure [check "ek" ek ek']
  return ekChecks ++ [check "K" K K']

private structure EncapsCase where
  m : Array UInt8
  ek : Array UInt8
  c : Array UInt8
  K : Array UInt8

private def EncapsCase.ofJson (j : Lean.Json) : Except String EncapsCase := do
  return { m := ← getHexBytes j "m", ek := ← getHexBytes j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes j "K" }

private def EncapsCase.run (p : ParameterSet) (c : EncapsCase) : Except String (List Test) := do
  let m ← toFixed 32 c.m
  let ek ← toFixed (ekSize p) c.ek
  let some (K', c', _) := Encaps p ek (tapeOf m.toArray)
    | throw "encapsulation key failed the modulus check"
  let K ← toFixed 32 c.K
  let ct ← toFixed (ctSize p) c.c
  return [check "K" K K', check "c" ct c']

private structure DecapsCase where
  dk : Array UInt8
  ek : Array UInt8
  c : Array UInt8
  K : Option (Array UInt8)

private def DecapsCase.ofJson (j : Lean.Json) : Except String DecapsCase := do
  return { dk := ← getHexBytes j "dk", ek := ← getHexBytes j "ek",
           c := ← getHexBytes j "c", K := ← getHexBytes? j "K" }

private def DecapsCase.run (p : ParameterSet) (c : DecapsCase) : Except String (List Test) := do
  let dk ← toFixed (dkSize p) c.dk
  let ct ← toFixed (ctSize p) c.c
  let some K' := Decaps p dk ct | throw "decapsulation key failed its hash check"
  let some K := c.K | throw "case is valid but gives no shared key"
  let K ← toFixed 32 K
  let ek ← toFixed (ekSize p) c.ek
  return [check "K" K K', check "embedded ek" ek (slice dk (384 * k p) (384 * k p + 32))]

/-! ## Suites -/

/-- Every `invalid` case of a group, which is rejected before any expensive computation, and the
first `limit` others. -/
private def sample (limit : Option Nat) (cases : Array (Case α)) : Array (Case α) :=
  match limit with
  | none => cases
  | some n => Id.run do
    let mut kept := #[]
    let mut accepted := 0
    for c in cases do
      if c.result == .invalid then
        kept := kept.push c
      else if accepted < n then
        kept := kept.push c
        accepted := accepted + 1
    return kept

/-- Run a file's cases, taking the parameter set from each group's header. -/
private def suite (file : String) (type : String) (ofJson : Lean.Json → Except String α)
    (run : ParameterSet → α → Except String (List Test)) (limit : Option Nat) : Suite where
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
its `invalid` cases and its first eight others; `full` runs every case. -/
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
