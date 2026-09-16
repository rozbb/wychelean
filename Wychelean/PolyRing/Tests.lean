import Wychelean.PolyRing
import Wychelean.KEM.MLKEM.Basic
import RunTests.Basic

/-! Executable checks with ML-KEM's parameters (`q = 3329`, `ζ = 17`, seven layers): the butterfly
loops against the residue forms, and products through the NTT against `Poly` multiplication. -/

namespace Wychelean.PolyRing.Tests

open RunTests Wychelean.KEM.MLKEM

private abbrev P := Poly (ZMod 3329) 256 (-1)

private def monomial (i : Fin 256) : P := Poly.ofFn fun j => if j = i then 1 else 0

/-- `X^i · X^j` in `ℤ_q[X]/(X^256 + 1)`. -/
private def monomialProduct (i j : Fin 256) : P :=
  Poly.ofFn fun k =>
    if k.val = (i.val + j.val) % 256 then (if i.val + j.val < 256 then 1 else -1) else 0

private def dense (a b c : ℕ) : P :=
  Poly.ofFn fun i => ((a * i.val * i.val + b * i.val + c : ℕ) : ZMod 3329)

private def ntt (f : P) : Tq := f.ntt

private def viaNTT (f g : P) : P := (ntt f * ntt g).nttInv

private instance : ToString P := ⟨fun f => toString (f.coeffs.toList.map (·.val))⟩
private instance : ToString Tq := ⟨fun f => toString (f.flatten.toList.map (·.val))⟩

def suite : Suite where
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
    (polys.map fun f => check "ntt loops = nttSpec" (NTT.nttSpec ζ 7 f) (ntt f)) ++
    (polys.map fun f => check "ntt loops = nttRec" (NTT.nttRec ζ 7 (by decide) f) (ntt f)) ++
    (polys.map fun f => check "nttInv loops = nttInvSpec" (NTT.nttInvSpec ζ 7 (ntt f)) (ntt f).nttInv)

def suites : List Suite := [suite]

end Wychelean.PolyRing.Tests
