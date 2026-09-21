import Wychelean.KEM.MLKEM
import RunTests.Basic

namespace Wychelean.KEM.MLKEM.Tests

open RunTests
open scoped Wychelean.Utils.PolyRing

-- These definitional checks pin the public notation to the FIPS executable definitions.
example (f : Polynomial) : f.ntt.coeffs = NTT.forward f.coeffs := rfl
example (a : Tq) : a.nttInv.coeffs = NTT.inverse a.coeffs := rfl
example (a b : Tq) : a * b = NTT.multiply a b := rfl
example {k : K} (v : PolyVector q k) : v.ntt = v.map Polynomial.ntt := rfl
example {k : K} (v w : PolyVector q k) :
    (v + w : PolyVector q k).ntt = (v + w : PolyVector q k).map Polynomial.ntt := rfl
example {k : K} (a : NTTMatrix k) (v : NTTVector k) :
    (a * v : NTTVector k).nttInv = (a * v : NTTVector k).map Tq.nttInv := rfl
example {k : K} (a b : NTTVector k) :
    ⟪a, b⟫ = (Vector.zipWith NTT.multiply a b).foldl (· + ·) 0 := rfl

private def monomial (n : ℕ) : Polynomial :=
  Utils.PolyRing.PolyMod.ofFn fun i => if i.val = n then 1 else 0

private def polynomials : List (String × Polynomial) :=
  [("zero", 0), ("one", 1)] ++
  ([1, 127, 128, 254, 255].map fun i => (s!"X^{i}", monomial i)) ++
  [("dense ascending", Utils.PolyRing.PolyMod.ofFn fun i => ((i.val + 1 : ℕ) : Zq)),
   ("dense quadratic", Utils.PolyRing.PolyMod.ofFn fun i => ((i.val * i.val + 7 * i.val + 3 : ℕ) : Zq)),
   ("all q-1", Utils.PolyRing.PolyMod.ofFn fun _ => (-1 : Zq))]

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
      check s!"{name}: Algorithm 9 = recursive NTT" true (Tq.toAbstract f.ntt == abstractNTT f),
      check s!"{name}: inverse after forward" true (f.ntt.nttInv == f)]) ++
    (domains.flatMap fun (name, a) => [
      check s!"{name}: Algorithm 10 = recursive inverse" true (a.nttInv == abstractNTTInv a.toAbstract),
      check s!"{name}: forward after inverse" true (a.nttInv.ntt == a),
      check s!"{name}: multiplicative identity" true (a * 1 == a)]) ++
    (domains.flatMap fun (name, a) => domains.map fun (name', b) =>
      check s!"{name} * {name'}: Algorithm 11 = quadratic multiplication" true
        ((a * b).toAbstract == a.toAbstract * b.toAbstract)) ++
    (polynomials.map fun (name, f) =>
      let g : Polynomial := Utils.PolyRing.PolyMod.ofFn (fun i : Fin 256 => ((3 * i.val + 1 : ℕ) : Zq))
      check s!"{name}: multiplication through FIPS transforms" true ((f.ntt * g.ntt).nttInv == f * g))

end Wychelean.KEM.MLKEM.Tests
