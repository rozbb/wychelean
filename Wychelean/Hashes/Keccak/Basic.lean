import Wychelean.Utils.Bits

/-!
Keccak-p, FIPS 202 §§3–5: https://doi.org/10.6028/NIST.FIPS.202
Generalized from Microsoft SymCrypt's SHA3 spec:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
MIT notice: Wychelean/Hashes/SHA3/LICENSE.SymCrypt.
-/
namespace Wychelean.Hashes.Keccak
open Wychelean
open scoped Wychelean.Notations

/-- Table 1: exactly the seven supported widths, b = 25·2^ℓ. -/
abbrev Width := Fin 7
abbrev w (ℓ : Width) : Nat := 2 ^ ℓ.val
abbrev b (ℓ : Width) : Nat := 25 * w ℓ
abbrev Lane (ℓ : Width) := BitVec (w ℓ)
abbrev State (ℓ : Width) := Vector (Vector (Lane ℓ) 5) 5

theorem w_pos (ℓ : Width) : 0 < w ℓ := Nat.two_pow_pos _

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

/-- Algorithm 5 first reduces its integer argument modulo 255; lookup preserves its result. -/
theorem rc_eq_algorithm (t : Int) : rc t = rc.algorithm ((t % 255).toNat) := by
  simp only [rc, rc.table, Vector.getElem_ofFn]




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

/-- String/state conversion is a bijection (§3.1.2–3.1.3). -/
theorem stringToState_stateToString (A : State ℓ) : stringToState (stateToString A) = A := by
  apply Vector.ext
  intro x hx
  apply Vector.ext
  intro y hy
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [stringToState, Vector.getElem_ofFn, BitVec.getLsbD_ofBitsLE _ _ hz, stateToString]
  have hdiv : (w ℓ * (5 * y + x) + z) / w ℓ = 5 * y + x := by
    rw [Nat.mul_add_div (w_pos ℓ)]
    simp [Nat.div_eq_of_lt hz]
  have hmod : (w ℓ * (5 * y + x) + z) % w ℓ = z := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hz]
  have hx' : (5 * y + x) % 5 = x := by omega
  have hy' : (5 * y + x) / 5 = y := by omega
  simp only [hdiv, hmod, hx', hy']

theorem stateToString_stringToState (S : Vector Bool (b ℓ)) : stateToString (stringToState S) = S := by
  apply Vector.ext
  intro i hi
  simp only [stateToString, stringToState, Vector.getElem_ofFn]
  rw [BitVec.getLsbD_ofBitsLE _ _ (Nat.mod_lt _ (w_pos ℓ))]
  simp only [Vector.getElem_ofFn]
  congr 1
  rw [show 5 * (i / w ℓ / 5) + i / w ℓ % 5 = i / w ℓ from Nat.div_add_mod _ _]
  exact Nat.div_add_mod _ _

@[simp] theorem KECCAK_p_zero (ℓ : Width) (S : Vector Bool (b ℓ)) : KECCAK_p ℓ 0 S = S := by
  simp [KECCAK_p, Fin.foldl_zero, stateToString_stringToState]
theorem KECCAK_f_eq (ℓ : Width) : KECCAK_f ℓ = KECCAK_p ℓ (12 + 2 * ℓ.val) := rfl

/-- Direct executable check of FIPS 202 Table 1 and Algorithm 7 for Keccak-p[800,12]. -/
theorem rounds_800_12 : (List.range 12).map (roundIndex 5 12) =
    [10,11,12,13,14,15,16,17,18,19,20,21] := by decide

/-- Padding length for pad10*1(x, m) (§5.1). -/
abbrev padLen.j (x m : Nat) := ((-(m : Int) - 2) % x).toNat
abbrev padLen x m := 1 + padLen.j x m + 1

/-- Algorithm 9: pad10*1(x, m) (§5.1). Returns `Vector Bool (padLen x m)`.
    1. j = (−m − 2) mod x
    2. Return 1 || 0^j || 1 -/
def «pad10*1» x m : Vector Bool (padLen x m) :=
  #v[1]  ‖ .replicate (padLen.j x m) 0 ‖ #v[1]

/-- Padding always produces a total length divisible by x.
    Used to discharge the `blocks` divisibility precondition.
    Proof: `pad10*1(x, m)` has length `j + 2` where `j = (−m − 2) mod x`,
    so `m + j + 2 ≡ m + (−m − 2) + 2 ≡ 0 (mod x)`. -/
theorem padLen_dvd (r n : Nat) (hr : 0 < r := by grind) : (n + padLen r n) % r = 0 := by
  simp only [padLen, padLen.j]
  have hnn : (-(↑n : Int) - 2) % ↑r ≥ 0 := Int.emod_nonneg _ (by omega)
  have h_eq : (n : Int) + (1 + ((-(↑n : Int) - 2) % ↑r).toNat + 1) =
    ((-(↑n : Int) - 2) % ↑r + ↑n + 2) := by omega
  have h_mod : ((-(↑n : Int) - 2) % ↑r + ↑n + 2) % ↑r = 0 := by
    have := Int.emod_add_mul_ediv (-(n : Int) - 2) r
    rw [show (-(↑n : Int) - 2) % ↑r + ↑n + 2 = -(↑r * ((-(↑n : Int) - 2) / ↑r)) from by omega]
    exact Int.neg_mul_emod_right r _
  grind



/-- Successive states during squeezing, including the initial state (Algorithm 8, steps 8–10). -/
def squeezeStates (f : α → α) (S : α) : (k : Nat) → Vector α (k + 1)
  | 0 => #v[S]
  | k + 1 => let states := squeezeStates f S k
             states.push (f states[k])

/-- The state at position i does not depend on how many later states are requested. -/
theorem squeezeStates_prefix (f : α → α) (S : α) (k j i : Nat) (hi : i ≤ k) (hj : k ≤ j) :
    (squeezeStates f S j)[i] = (squeezeStates f S k)[i] := by
  induction j with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ j ih =>
    by_cases h : k ≤ j
    · simp only [squeezeStates, Vector.getElem_push]
      rw [dite_eq_left (by omega)]
      exact ih h
    · have : k = j + 1 := by omega
      subst k
      rfl

/-- The first d output bits; the state prefix is computed once and shared by all bits. -/
def squeeze {b : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (S : Vector Bool b) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  let states := squeezeStates f S (d / r)
  Vector.ofFn fun (i : Fin d) =>
    have hs : i.val / r < d / r + 1 := Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.isLt))
    (states[i.val / r]'hs)[i.val % r]'(by have := Nat.mod_lt i.val hr.1; omega)

/-- Squeezing a shorter output is exactly a prefix of a longer output. -/
theorem squeeze_prefix {b : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (S : Vector Bool b) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (squeeze f r S e hr) 0 d (by omega) = squeeze f r S d hr := by
  apply Vector.ext
  intro i hi
  simp only [slice, squeeze, Vector.getElem_ofFn, Nat.zero_add]
  congr 1
  apply squeezeStates_prefix
  · exact Nat.div_le_div_right (by omega)
  · exact Nat.div_le_div_right h

/-- Algorithm 8 with indexed input. It reads one rate block at a time, so byte-oriented
callers need not allocate an expanded Boolean vector for the entire message. The two
padding ones are at positions n and n+padLen(r,n)-1 (Algorithm 9). -/
def SPONGE_fn {b : Nat} (f : Vector Bool b → Vector Bool b) (r n : Nat)
    (N : Fin n → Bool) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  let total := n + padLen r n
  let S := Fin.foldl (total / r) (fun S block =>
    f (Vector.ofFn fun j => S[j] ^^ (if j.val < r then
      let k := block.val * r + j.val
      if h : k < n then N ⟨k, h⟩ else decide (k = n ∨ k + 1 = total)
      else false))) (Vector.replicate b false)
  squeeze f r S d hr

/-- SPONGE[f, pad10*1, r], Algorithm 8. Padding is applied exactly once. -/
def SPONGE {b n : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (N : Vector Bool n) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  SPONGE_fn f r n (fun i => N[i]) d hr

theorem SPONGE_fn_prefix {b : Nat} (f : Vector Bool b → Vector Bool b) (r n : Nat)
    (N : Fin n → Bool) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (SPONGE_fn f r n N e hr) 0 d (by omega) = SPONGE_fn f r n N d hr :=
  squeeze_prefix f r _ d e hr h

theorem SPONGE_prefix {b n : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (N : Vector Bool n) (d e : Nat) (hr : 0 < r ∧ r < b) (h : d ≤ e) :
    slice (SPONGE f r N e hr) 0 d (by omega) = SPONGE f r N d hr :=
  squeeze_prefix f r _ d e hr h

/-- General Keccak sponge: every supported width, every natural round count, and 0<r<b. -/
def KECCAK (ℓ : Width) (nr r : Nat) (N : Vector Bool n) (d : Nat)
    (hr : 0 < r ∧ r < b ℓ) : Vector Bool d := SPONGE (KECCAK_p ℓ nr) r N d hr

end Wychelean.Hashes.Keccak
