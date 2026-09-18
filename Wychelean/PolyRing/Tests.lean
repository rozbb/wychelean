import Wychelean.PolyRing
import RunTests.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-! Executable checks of the transform at the ML-KEM parameters (`q = 3329`, `ζ = 17`, seven
layers) and the ML-DSA parameters (`q = 8380417`, `ζ = 1753`, eight layers): the layer form
against the closed form, a radix-4 schedule, the butterfly loops, and products through the NTT
against the ring product. -/

namespace Wychelean.PolyRing.Tests

open RunTests

private instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 8380417) := ⟨by norm_num⟩

/-- `ζ = 17` is a primitive 256-th root of unity in `ℤ_3329` (FIPS 203 §4.3). -/
private def ζKem : PrimitiveRoot (ZMod 3329) (2 ^ 8) :=
  PrimitiveRoot.ofPowEqNegOne 17 (by decide +kernel) (by decide)

/-- `ζ = 1753` is a primitive 512-th root of unity in `ℤ_8380417` (FIPS 204 §7.5). -/
private def ζDsa : PrimitiveRoot (ZMod 8380417) (2 ^ 9) :=
  PrimitiveRoot.ofPowEqNegOne 1753 (by decide +kernel) (by decide)

private instance : Fact (2 ^ 7 ∣ 256) := ⟨by decide⟩
private instance : Fact (2 ^ 8 ∣ 256) := ⟨by decide⟩

private instance {q n : ℕ} : ToString (Poly (ZMod q) n) :=
  ⟨fun f => toString (f.coeffs.toList.map (·.val))⟩
private instance {q : ℕ} : ToString (PolyMod (ZMod q) 256 (-1)) :=
  ⟨fun f => toString (f.coeffs.toList.map (·.val))⟩
private instance {q d m : ℕ} {γ : Fin m → ZMod q} : ToString (Residues (ZMod q) d m γ) :=
  ⟨fun a => toString (a.flatten.toList.map (·.val))⟩

section Kem

private abbrev q := 3329
private abbrev P := PolyMod (ZMod q) 256 (-1)
private abbrev Tq := NTTDomain 7 ζKem 256

private def monomial (i : Fin 256) : P := PolyMod.ofFn fun j => if j = i then 1 else 0

/-- `X^i · X^j` in `ℤ_q[X]/(X^256 + 1)`. -/
private def monomialProduct (i j : Fin 256) : P :=
  PolyMod.ofFn fun k =>
    if k.val = (i.val + j.val) % 256 then (if i.val + j.val < 256 then 1 else -1) else 0

private def dense (a b c : ℕ) : P :=
  PolyMod.ofFn fun i => ((a * i.val * i.val + b * i.val + c : ℕ) : ZMod q)

private def ntt (f : P) : Tq := f.ntt

private def viaNTT (f g : P) : P := (ntt f * ntt g).nttInv

def kemSuite : Suite where
  name := "PolyRing and NTT (ML-KEM parameters)"
  tests := IO.lazyPure fun _ =>
    let polys := [dense 1 0 0, dense 7 3 1, dense 0 1 3328, monomial 0, monomial 255]
    let pairs : List (Fin 256 × Fin 256) := [(1, 1), (100, 155), (100, 156), (255, 255)]
    (polys.map fun f => check "nttInv (ntt f) = f" f (ntt f).nttInv) ++
    (pairs.map fun (i, j) =>
      check s!"X^{i} * X^{j} closed form" (monomialProduct i j) (monomial i * monomial j)) ++
    (pairs.map fun (i, j) =>
      check s!"X^{i} * X^{j} via NTT" (monomial i * monomial j) (viaNTT (monomial i) (monomial j))) ++
    ((polys.zip polys.reverse).map fun (f, g) =>
      check s!"f * g via NTT (dense)" (f * g) (viaNTT f g)) ++
    (polys.map fun f => check "ntt = nttSpec" (NTT.nttSpec ζKem f (by decide)) (ntt f)) ++
    (polys.map fun f =>
      check "ntt = radix-4 schedule" (NTT.nttSched [2, 2, 2, 1] 0 ζKem f (by decide)) (ntt f)) ++
    (polys.map fun f =>
      check "nttInvSched (ntt f) = f" f (NTT.nttInvSched [2, 2, 2, 1] 0 ζKem (ntt f) (by decide))) ++
    (polys.map fun f => check "ntt loops = ntt" (NTT.Loops.ntt 7 ζKem.val f (by decide)) (ntt f)) ++
    (polys.map fun f =>
      check "nttInv loops = nttInv" (NTT.Loops.nttInv 7 ζKem.val (ntt f) (by decide)) (ntt f).nttInv)

end Kem

section Dsa

private abbrev q' := 8380417
private abbrev P' := PolyMod (ZMod q') 256 (-1)
private abbrev Tq' := NTTDomain 8 ζDsa 256

private def dense' (a b c : ℕ) : P' :=
  PolyMod.ofFn fun i => ((a * i.val * i.val + b * i.val + c : ℕ) : ZMod q')

private def ntt' (f : P') : Tq' := f.ntt

def dsaSuite : Suite where
  name := "PolyRing and NTT (ML-DSA parameters)"
  tests := IO.lazyPure fun _ =>
    let polys := [dense' 1 0 0, dense' 7 3 1, dense' 0 1 8380416, dense' 12345 0 6789]
    (polys.map fun f => check "nttInv (ntt f) = f" f (ntt' f).nttInv) ++
    ((polys.zip polys.reverse).map fun (f, g) =>
      check s!"f * g via NTT" (f * g) (ntt' f * ntt' g).nttInv) ++
    (polys.map fun f => check "ntt = nttSpec" (NTT.nttSpec ζDsa f (by decide)) (ntt' f)) ++
    (polys.map fun f => check "ntt loops = ntt" (NTT.Loops.ntt 8 ζDsa.val f (by decide)) (ntt' f)) ++
    (polys.map fun f =>
      check "nttInv loops = nttInv" (NTT.Loops.nttInv 8 ζDsa.val (ntt' f) (by decide)) (ntt' f).nttInv)

end Dsa

section Cyclic

private abbrev C := PolyMod (ZMod 3329) 256 1

private def denseC (a b c : ℕ) : C :=
  PolyMod.ofFn fun i => ((a * i.val * i.val + b * i.val + c : ℕ) : ZMod 3329)

/-- The complete split of `ℤ_q[X]/(X^256 - 1)` at the primitive 256-th root `17`. -/
private def nttC (f : C) := NTT.Cyclic.ntt ζKem f (by decide)

def cyclicSuite : Suite where
  name := "PolyRing cyclic split (X^256 - 1)"
  tests := IO.lazyPure fun _ =>
    let polys := [denseC 1 0 0, denseC 7 3 1, denseC 0 1 3328]
    (polys.map fun f =>
      check "nttInv (ntt f) = f" f (NTT.Cyclic.nttInv ζKem (nttC f) (by decide))) ++
    ((polys.zip polys.reverse).map fun (f, g) =>
      check "f * g via the cyclic split" (f * g) (NTT.Cyclic.nttInv ζKem (nttC f * nttC g) (by decide)))

end Cyclic

section Monic

/-- `X² + X + 1` over `ℤ_7`. -/
private def μ : Poly (ZMod 7) 2 := ⟨#v[1, 1]⟩

def monicSuite : Suite where
  name := "PolyRing division by a monic polynomial"
  tests := IO.lazyPure fun _ =>
    let x : Poly (ZMod 7) 2 := ⟨#v[0, 1]⟩
    let onePlusX : Poly (ZMod 7) 2 := ⟨#v[1, 1]⟩
    let f := (dense 1 0 0).poly
    let g := (dense 7 3 1).poly
    [ check "X^3 mod (X^2 + X + 1) = 1" (⟨#v[1, 0]⟩ : Poly (ZMod 7) 2)
        (Poly.modMonic μ (⟨#v[0, 0, 0, 1]⟩ : Poly (ZMod 7) 4)),
      check "X^5 + 3 mod (X^2 + X + 1) = 2 - X" (⟨#v[2, 6]⟩ : Poly (ZMod 7) 2)
        (Poly.modMonic μ (⟨#v[3, 0, 0, 0, 0, 1]⟩ : Poly (ZMod 7) 6)),
      check "X * X = -X - 1" (⟨#v[6, 6]⟩ : Poly (ZMod 7) 2) (Poly.mulMonic μ x x),
      check "(1 + X)^2 = X" (⟨#v[0, 1]⟩ : Poly (ZMod 7) 2) (Poly.mulMonic μ onePlusX onePlusX),
      check "mulMonic (X^256 + 1) = mulMod (-1)" (Poly.mulMod (-1) f g)
        (Poly.mulMonic (Poly.binomial (-1)) f g) ]

end Monic

def suites : List Suite := [kemSuite, dsaSuite, cyclicSuite, monicSuite]

end Wychelean.PolyRing.Tests
