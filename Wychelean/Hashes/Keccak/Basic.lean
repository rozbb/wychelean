import Wychelean.Permutations.Keccak.Basic

/-!
Keccak sponge construction, FIPS 202 §§4–5: https://doi.org/10.6028/NIST.FIPS.202
Generalized from Microsoft SymCrypt's SHA3 spec:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
MIT notice: Wychelean/Hashes/SHA3/LICENSE.SymCrypt.
-/
namespace Wychelean.Hashes.Keccak
open Wychelean
open Wychelean.Permutations.Keccak
open scoped Wychelean.Notations

/-- Padding length for pad10*1(x, m) (§5.1). -/
abbrev padLen.j (x m : Nat) := ((-(m : Int) - 2) % x).toNat
abbrev padLen x m := 1 + padLen.j x m + 1

/-- Algorithm 9: pad10*1(x, m) (§5.1). Returns `Vector Bool (padLen x m)`.
    1. j = (−m − 2) mod x
    2. Return 1 || 0^j || 1 -/
def «pad10*1» x m : Vector Bool (padLen x m) :=
  #v[1]  ‖ .replicate (padLen.j x m) 0 ‖ #v[1]

/-- Successive states during squeezing, including the initial state (Algorithm 8, steps 8–10). -/
def squeezeStates (f : α → α) (S : α) : (k : Nat) → Vector α (k + 1)
  | 0 => #v[S]
  | k + 1 => let states := squeezeStates f S k
             states.push (f states[k])

/-- The first d output bits; the state prefix is computed once and shared by all bits. -/
def squeeze {b : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (S : Vector Bool b) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  let states := squeezeStates f S (d / r)
  Vector.ofFn fun (i : Fin d) =>
    have hs : i.val / r < d / r + 1 := Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.isLt))
    (states[i.val / r]'hs)[i.val % r]'(by have := Nat.mod_lt i.val hr.1; omega)

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

/-- General Keccak sponge: every supported width, every natural round count, and 0<r<b. -/
def KECCAK (ℓ : Width) (nr r : Nat) (N : Vector Bool n) (d : Nat)
    (hr : 0 < r ∧ r < b ℓ) : Vector Bool d := SPONGE (KECCAK_p ℓ nr) r N d hr

end Wychelean.Hashes.Keccak
