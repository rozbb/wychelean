import Wychelean.Utils.Bits

/-!
Keccak-p, FIPS 202 §§3–3.4: https://doi.org/10.6028/NIST.FIPS.202
Generalized from Microsoft SymCrypt's SHA3 spec:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
MIT notice: Wychelean/Hashes/SHA3/LICENSE.SymCrypt.
-/
namespace Wychelean.Permutations.Keccak
open Wychelean
open scoped Wychelean.Notations

/-- Table 1: exactly the seven supported widths, b = 25·2^ℓ. -/
abbrev Width := Fin 7
abbrev w (ℓ : Width) : Nat := 2 ^ ℓ.val
abbrev b (ℓ : Width) : Nat := 25 * w ℓ
abbrev Lane (ℓ : Width) := BitVec (w ℓ)
abbrev State (ℓ : Width) := Vector (Vector (Lane ℓ) 5) 5

/-- FIPS 202 §3.1.2, Equation (1). -/
def stringToState (S : Vector Bool (b ℓ)) : State ℓ :=
  Vector.ofFn fun x => Vector.ofFn fun y => BitVec.ofBitsLE (Vector.ofFn fun z =>
    S[w ℓ * (5 * y.val + x.val) + z.val]'(by
      have hh : 5 * y.val + x.val + 1 ≤ 25 := by omega
      have := Nat.mul_le_mul_left (w ℓ) hh
      have := z.isLt
      simp only [b, Nat.mul_add, Nat.mul_one] at *
      omega))

def stateToString (A : State ℓ) : Vector Bool (b ℓ) :=
  Vector.ofFn fun i =>
    have hd : i.val / w ℓ < 25 := Nat.div_lt_of_lt_mul (by simpa [b, Nat.mul_comm] using i.isLt)
    A[i.val / w ℓ % 5][i.val / w ℓ / 5].getLsbD (i.val % w ℓ)

/-- Algorithm 1, θ. Fin 5 arithmetic performs reduction modulo 5. -/
def θ (A : State ℓ) : State ℓ :=
  let C := Vector.ofFn fun (x : Fin 5) => A[x][0] ^^^ A[x][1] ^^^ A[x][2] ^^^ A[x][3] ^^^ A[x][4]
  let D := Vector.ofFn fun (x : Fin 5) => C[x-1] ^^^ C[x+1].rotateLeft 1
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y] ^^^ D[x]

/-! ### Algorithm 2: ρ(A) (§3.2.2) — rotate each lane by its computed offset

    1. A′[0, 0, z] = A[0, 0, z].       (offset 0 — handled by zero-initialization)
    2. Let (x, y) = (1, 0).
    3. For t from 0 to 23:
       a. A′[x, y, z] = A[x, y, (z − (t+1)(t+2)/2) mod w].
       b. Let (x, y) = (y, (2x + 3y) mod 5). -/

/-- Rotation offsets for ρ, computed from Algorithm 2 (§3.2.2). -/
def ρ.Offsets : Vector (Vector Nat 5) 5 := Id.run do
  let mut offsets := .replicate 5 (.replicate 5 0)
  let mut x : Fin 5 := 1
  let mut y : Fin 5 := 0
  for t in [0 : 24] do
    offsets := offsets.set x (offsets[x].set y ((t + 1) * (t + 2) / 2))
    (x, y) := (y, 2 * x + 3 * y)
  pure offsets

/-- Algorithm 2; rotation reduces offsets modulo the lane width. -/
def ρ (A : State ℓ) : State ℓ :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y].rotateLeft ρ.Offsets[x][y]
/-- Algorithm 3. -/
def π (A : State ℓ) : State ℓ :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x+3*y][x]
/-- Algorithm 4. -/
def χ (A : State ℓ) : State ℓ :=
  Vector.ofFn fun x => Vector.ofFn fun y => A[x][y] ^^^ (~~~A[x+1][y] &&& A[x+2][y])

private def Trunc (s : Nat) (v : Vector Bool n) (h : s ≤ n := by grind) := slice v 0 s

def rc.algorithm (t : Nat) : Bool := Id.run do
  -- 1. If t mod 255 = 0, return 1.
  if t % 255 = 0 then return true
  -- 2. Let R = 10000000.
  let mut R := #v[1, 0, 0, 0, 0, 0, 0, 0]
  -- 3. For i from 1 to t mod 255:
  for _ in [1 : t % 255 + 1] do
    let R' := #v[0] ‖ Trunc 8 R
    let R' := R'.set 0 (R'[0] ^^ R'[8])
    let R' := R'.set 4 (R'[4] ^^ R'[8])
    let R' := R'.set 5 (R'[5] ^^ R'[8])
    let R' := R'.set 6 (R'[6] ^^ R'[8])
    R := Trunc 8 R'
  pure R[0]

/-- Algorithm 5 depends only on t mod 255; cache its complete period. -/
def rc.table : Vector Bool 255 := Vector.ofFn fun t => rc.algorithm t

def rc (t : Int) : Bool := rc.table[(t % 255).toNat]

/-- Algorithm 6. Signed round indices are essential for more than 12+2ℓ rounds (§3.4). -/
def ι.RC (ℓ : Width) (iᵣ : Int) : Lane ℓ :=
  Fin.foldl (ℓ.val + 1) (fun acc j =>
    if rc (j.val + 7 * iᵣ) then acc ^^^ (BitVec.ofNat (w ℓ) 1 <<< (2 ^ j.val - 1)) else acc) 0

def ι (A : State ℓ) (iᵣ : Int) : State ℓ :=
  Vector.ofFn fun x => Vector.ofFn fun y =>
    if x = 0 ∧ y = 0 then A[x][y] ^^^ ι.RC ℓ iᵣ else A[x][y]

def Rnd (A : State ℓ) (iᵣ : Int) : State ℓ := ι (χ (π (ρ (θ A)))) iᵣ

/-- Algorithm 7: nr rounds ending at index 12+2ℓ-1, including negative indices.
For b=800 (ℓ=5), nr=12 gives indices 10 through 21.
FIPS 202 Table 1, §3.3 Algorithm 7, and §3.4's 30-round example. -/
def roundIndex (ℓ : Width) (nr j : Nat) : Int := 12 + 2 * (ℓ.val : Int) - nr + j

/-- FIPS 202 Algorithm 7 for positive nr; zero rounds is an identity extension. -/
def KECCAK_p (ℓ : Width) (nr : Nat) (S : Vector Bool (b ℓ)) : Vector Bool (b ℓ) :=
  stateToString (Fin.foldl nr (fun A j => Rnd A (roundIndex ℓ nr j)) (stringToState S))

/-- FIPS 202 §3.4: full-round Keccak-f[b]. -/
def KECCAK_f (ℓ : Width) := KECCAK_p ℓ (12 + 2 * ℓ.val)

end Wychelean.Permutations.Keccak
