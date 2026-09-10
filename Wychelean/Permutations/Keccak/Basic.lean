import Wychelean.Utils.Bits

/-!
Keccak-p, FIPS 202 §§3–3.4:
https://doi.org/10.6028/NIST.FIPS.202

Adapted from Microsoft SymCrypt's SHA3 specification:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean

MIT notice: Wychelean/Hashes/SHA3/LICENSE.SymCrypt.
-/
namespace Wychelean.Permutations.Keccak
open Wychelean
open scoped Wychelean.Notations

/-- Table 1: exactly the seven supported widths, b = 25·2^ℓ. -/
inductive Width where
  | w25 | w50 | w100 | w200 | w400 | w800 | w1600
  deriving DecidableEq, Repr

/-- FIPS 202 §3.1, Table 1: ℓ = log₂(b/25). -/
abbrev Width.ℓ : Width → Nat
  | .w25 => 0
  | .w50 => 1
  | .w100 => 2
  | .w200 => 3
  | .w400 => 4
  | .w800 => 5
  | .w1600 => 6

abbrev w (width : Width) : Nat := 2 ^ width.ℓ
abbrev b (width : Width) : Nat := 25 * w width
abbrev Lane (width : Width) := BitVec (w width)
abbrev State (width : Width) := Vector (Vector (Lane width) 5) 5

/-- FIPS 202 §3.1.2, Equation (1). Bit i of S is its ith least significant bit. -/
def vecToState (S : BitVec (b width)) : State width :=
  Vector.ofFn fun x => Vector.ofFn fun y =>
    S.extractLsb' (w width * (5 * y.val + x.val)) (w width)

/-- FIPS 202 §3.1.3: serialize the lanes in Equation (1) order, least significant bit first. -/
def stateToVec (A : State width) : BitVec (b width) :=
  BitVec.ofBitsLE (Vector.ofFn fun i =>
    have hd : i.val / w width < 25 := Nat.div_lt_of_lt_mul (by simpa only [b, Nat.mul_comm] using i.isLt)
    A[i.val / w width % 5][i.val / w width / 5].getLsbD (i.val % w width))

/-- Algorithm 1, θ. Fin 5 arithmetic performs reduction modulo 5. -/
def θ (A : State width) : State width :=
  let C := Vector.ofFn fun (x : Fin 5) => A[x][0] ^^^ A[x][1] ^^^ A[x][2] ^^^ A[x][3] ^^^ A[x][4]
  let D := Vector.ofFn fun (x : Fin 5) => C[x-1] ^^^ C[x+1].rotateLeft 1
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y] ^^^ D[x]

/-- Rotation offsets for ρ, computed from Algorithm 2 (§3.2.2). -/
def ρ.Offsets : Vector (Vector Nat 5) 5 := Id.run do
  let mut offsets := .replicate 5 (.replicate 5 0)
  let mut x : Fin 5 := 1
  let mut y : Fin 5 := 0
  for t in [0 : 24] do
    offsets := offsets.set x (offsets[x].set y ((t + 1) * (t + 2) / 2))
    (x, y) := (y, 2 * x + 3 * y)
  pure offsets

/-- Algorithm 2 -/
def ρ (A : State width) : State width :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y].rotateLeft ρ.Offsets[x][y]

/-- Algorithm 3. -/
def π (A : State width) : State width :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x+3*y][x]

/-- Algorithm 4. -/
def χ (A : State width) : State width :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y] ^^^ (~~~A[x+1][y] &&& A[x+2][y])

/-- FIPS 202 §3.2.5, Algorithm 5. -/
def rc (t : Int) : Bool := Id.run do
  let mut R : BitVec 8 := 1
  for _ in [0 : (t % 255).toNat] do
    let feedback : BitVec 8 := if R[7] then 0x71 else 0
    R := (R <<< 1) ^^^ feedback
  return R[0]

/-- Algorithm 6. -/
def ι.RC (width : Width) (iᵣ : Int) : Lane width := Id.run do
  let mut RC : Lane width := 0
  for j in [0 : width.ℓ + 1] do
    RC := RC.setBit (2 ^ j - 1) (rc (j + 7 * iᵣ))
  return RC

def ι (iᵣ : Int) (A : State width) : State width :=
  Vector.ofFn fun x => Vector.ofFn fun y =>
    if x = 0 ∧ y = 0 then A[x][y] ^^^ ι.RC width iᵣ else A[x][y]

def Rnd (A : State width) (iᵣ : Int) : State width := (ι iᵣ ∘ χ ∘ π ∘ ρ ∘ θ) A

/-- Algorithm 7: round indices ending at 12+2ℓ-1, including negative indices.
For b=800 (ℓ=5), rounds=12 gives indices 10 through 21.
FIPS 202 Table 1, §3.3 Algorithm 7, and §3.4's 30-round example. -/
def roundIndex (width : Width) (rounds j : Nat) : Int := 12 + 2 * (width.ℓ : Int) - rounds + j

/-- FIPS 202 Algorithm 7 for positive round counts; zero rounds is an identity extension. -/
def keccak_p (width : Width) (rounds : Nat) (S : BitVec (b width)) : BitVec (b width) :=
  stateToVec (Fin.foldl rounds (fun A j => Rnd A (roundIndex width rounds j)) (vecToState S))

/-- FIPS 202 §3.4: full-round Keccak-f[b]. -/
def keccak_f (width : Width) := keccak_p width (12 + 2 * width.ℓ)

end Wychelean.Permutations.Keccak
