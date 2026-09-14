import Wychelean.Lattice
import Wychelean.KEM.MLKEM.Basic
import RunTests.Basic

/-!
# Lattice library checks

Executable checks of the ring and transform, instantiated with ML-KEM's parameters
(`q = 3329`, `ζ = 17`, seven layers): the inverse transform undoes the forward one, and the
product computed through the NTT (`NTT⁻¹(MultiplyNTTs(NTT f, NTT g))`) equals the negacyclic
product `f * g` of `Lattice.Poly`, on monomials (where `X^i · X^j = ±X^(i+j)` is known in
closed form) and on dense polynomials; and the loops agree with the residue closed forms
`nttSpec`/`nttInvSpec` of `Lattice.NTTSpec`.
-/

namespace Wychelean.Lattice.Tests

open RunTests Wychelean.KEM.MLKEM

private abbrev P := Poly (ZMod 3329) 256

private def monomial (i : Fin 256) : P := Vector.ofFn fun j => if j = i then 1 else 0

/-- `X^i · X^j` in `ℤ_q[X]/(X^256 + 1)`. -/
private def monomialProduct (i j : Fin 256) : P :=
  Vector.ofFn fun k =>
    if k.val = (i.val + j.val) % 256 then (if i.val + j.val < 256 then 1 else -1) else 0

private def dense (a b c : ℕ) : P := Vector.ofFn fun i => ((a * i.val * i.val + b * i.val + c : ℕ) : ZMod 3329)

private def viaNTT (f g : P) : P := NTTInv (MultiplyNTTs (NTT f) (NTT g))

private instance : ToString P := ⟨fun f => toString (f.toList.map (·.val))⟩
private instance : ToString NTTPolynomial := ⟨fun f => toString (f.residues.toList.map (·.val))⟩

def suite : Suite where
  name := "Lattice ring and NTT (ML-KEM parameters)"
  tests := pure <|
    let polys := [dense 1 0 0, dense 7 3 1, dense 0 1 3328, dense 2 2 2, monomial 0, monomial 255]
    let pairs : List (Fin 256 × Fin 256) := [(0, 0), (1, 1), (3, 5), (100, 155), (100, 156), (255, 255), (128, 128), (0, 255)]
    (polys.map fun f => check s!"NTTInv (NTT f) = f" f (NTTInv (NTT f))) ++
    (pairs.map fun (i, j) =>
      check s!"X^{i} * X^{j} closed form" (monomialProduct i j) (monomial i * monomial j)) ++
    (pairs.map fun (i, j) =>
      check s!"X^{i} * X^{j} via NTT" (monomial i * monomial j) (viaNTT (monomial i) (monomial j))) ++
    ((polys.zip polys.reverse).map fun (f, g) =>
      check s!"f * g via NTT (dense)" (f * g) (viaNTT f g)) ++
    (polys.map fun f => check "ntt loops = nttSpec" (NTT.nttSpec ζ 7 f) (NTT f)) ++
    (polys.map fun f => check "nttInv loops = nttInvSpec" (NTT.nttInvSpec ζ 7 (NTT f)) (NTTInv (NTT f))) ++
    (polys.map fun f => check "nttInvSpec (nttSpec f) = f" f (NTT.nttInvSpec ζ 7 (NTT.nttSpec ζ 7 f))) ++
    ((polys.zip polys.reverse).map fun (f, g) =>
      check "MultiplyNTTs = mulNTT" (NTT.mulNTT ζ 7 (NTT f) (NTT g)) (MultiplyNTTs (NTT f) (NTT g)))

def suites : List Suite := [suite]

end Wychelean.Lattice.Tests
