import Wychelean.KEM.MLKEM
import RunTests.Basic

namespace Wychelean.KEM.MLKEM.Tests

open Polynomial (NTT)
open Tq (NTTInv)

open RunTests
open scoped Wychelean.Utils.Linear

-- These definitional checks pin the notation of the pseudocode to the FIPS algorithms.
example (a b : Tq) : a * b = MultiplyNTTs a b := rfl
example {k : K} (a b : NTTVector k) :
    ⟪a, b⟫ = (Vector.zipWith MultiplyNTTs a b).foldl (· + ·) 0 := rfl

private def monomial (n : ℕ) : Polynomial :=
  Polynomial.ofFn fun i => if i.val = n then 1 else 0

private def polynomials : List (String × Polynomial) :=
  [("zero", 0), ("one", 1)] ++
  ([1, 127, 128, 254, 255].map fun i => (s!"X^{i}", monomial i)) ++
  [("dense ascending", Polynomial.ofFn fun i => ((i.val + 1 : ℕ) : Zq)),
   ("dense quadratic", Polynomial.ofFn fun i => ((i.val * i.val + 7 * i.val + 3 : ℕ) : Zq)),
   ("all q-1", Polynomial.ofFn fun _ => (-1 : Zq))]

private def domains : List (String × Tq) :=
  [("zero", 0), ("one", 1),
   ("dense flat", ⟨Vector.ofFn fun i => (i.val * 37 + 9 : ℕ)⟩),
   ("all q-1", ⟨Vector.replicate 256 (-1)⟩),
   ("odd coefficients", ⟨Vector.ofFn fun i => if i.val % 2 = 1 then 1 else 0⟩)]

/-- Agreement with the recursive algebraic operations on structurally different inputs. -/
def arithmeticSuite : Suite where
  name := "ML-KEM FIPS arithmetic agreement"
  tests := IO.lazyPure fun _ =>
    (polynomials.flatMap fun (name, f) => [
      check s!"{name}: Algorithm 9 = recursive NTT" true (Tq.toAbstract (NTT f) == abstractNTT f),
      check s!"{name}: inverse after forward" true (NTTInv (NTT f) == f)]) ++
    (domains.flatMap fun (name, a) => [
      check s!"{name}: Algorithm 10 = recursive inverse" true (NTTInv a == abstractNTTInv a.toAbstract),
      check s!"{name}: forward after inverse" true (NTT (NTTInv a) == a),
      check s!"{name}: multiplicative identity" true (a * 1 == a)]) ++
    (domains.flatMap fun (name, a) => domains.map fun (name', b) =>
      check s!"{name} * {name'}: Algorithm 11 = quadratic multiplication" true
        ((a * b).toAbstract == a.toAbstract * b.toAbstract)) ++
    (polynomials.map fun (name, f) =>
      let g : Polynomial := Polynomial.ofFn (fun i : Fin 256 => ((3 * i.val + 1 : ℕ) : Zq))
      check s!"{name}: multiplication through FIPS transforms" true (NTTInv (NTT f * NTT g) == f * g))

end Wychelean.KEM.MLKEM.Tests
