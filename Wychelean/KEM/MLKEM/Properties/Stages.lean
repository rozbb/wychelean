import Wychelean.KEM.MLKEM.NTT

/-! Algorithms 9–11 restated as folds over stages and blocks, the form used in the proofs;
`Properties/Loops.lean` proves them equal to the FIPS loops. -/

namespace Wychelean.KEM.MLKEM

namespace NTT

/-- The seven lengths of Algorithm 9, in traversal order. -/
def len (s : Fin 7) : ℕ := 2 ^ (7 - s.val)

abbrev blocks (s : Fin 7) : ℕ := 2 ^ s.val

theorem len_pos (s : Fin 7) : 0 < len s := Nat.two_pow_pos _

theorem blocks_mul_len (s : Fin 7) : blocks s * (2 * len s) = 256 := by
  unfold blocks len
  rw [← pow_succ', ← pow_add]
  have : s.val + (7 - s.val + 1) = 8 := by omega
  rw [this]
  rfl

theorem index_lt (s : Fin 7) (b : Fin (blocks s)) (j : Fin (len s)) :
    2 * len s * b.val + j.val + len s < 256 := by
  have h := blocks_mul_len s
  have hb : b.val + 1 ≤ blocks s := b.isLt
  have := Nat.mul_le_mul_left (2 * len s) hb
  have := j.isLt
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 * len s) (blocks s), h] at *
  omega

/-- Algorithm 9: one block, with its twiddle counter increment. -/
def forwardBlock (s : Fin 7) (state : Vector Zq 256 × ℕ) (b : Fin (blocks s)) :
    Vector Zq 256 × ℕ :=
  let zeta : Zq := ζ ^ bitRev 7 state.2
  let i := state.2 + 1
  let a := Fin.foldl (len s) (fun a j =>
    let k := 2 * len s * b.val + j.val
    have hk : k + len s < 256 := index_lt s b j
    have hk' : k < 256 := by omega
    let u := a[k]
    let t := zeta * a[k + len s]
    let a := a.set (k + len s) (u - t)
    a.set k (u + t)) state.1
  (a, i)

def forwardStage (state : Vector Zq 256 × ℕ) (s : Fin 7) : Vector Zq 256 × ℕ :=
  Fin.foldl (blocks s) (forwardBlock s) state

/-- Algorithm 9. -/
def forward (f : Vector Zq 256) : Vector Zq 256 :=
  (Fin.foldl 7 forwardStage (f, 1)).1

/-- Algorithm 10: one block, with its twiddle counter decrement. -/
def inverseBlock (s : Fin 7) (state : Vector Zq 256 × ℕ) (b : Fin (blocks s)) :
    Vector Zq 256 × ℕ :=
  let zeta : Zq := ζ ^ bitRev 7 state.2
  let i := state.2 - 1
  let a := Fin.foldl (len s) (fun a j =>
    let k := 2 * len s * b.val + j.val
    have hk : k + len s < 256 := index_lt s b j
    have hk' : k < 256 := by omega
    let t := a[k]
    let u := a[k + len s]
    let a := a.set k (t + u)
    a.set (k + len s) (zeta * (u - t))) state.1
  (a, i)

def inverseStage (state : Vector Zq 256 × ℕ) (s : Fin 7) : Vector Zq 256 × ℕ :=
  Fin.foldl (blocks s) (inverseBlock s) state

/-- Algorithm 10. -/
def inverse (a : Vector Zq 256) : Vector Zq 256 :=
  let a := (Fin.foldl 7 (fun state s => inverseStage state ⟨6 - s.val, by omega⟩) (a, 127)).1
  a.map (· * 3303)

/-- Algorithm 12. -/
def baseCaseMultiply (a₀ a₁ b₀ b₁ γ : Zq) : Vector Zq 2 :=
  #v[a₀ * b₀ + a₁ * b₁ * γ, a₀ * b₁ + a₁ * b₀]

/-- Algorithm 11. Each adjacent pair uses its prescribed quadratic factor. -/
def multiply (a b : Tq) : Tq :=
  ⟨(Vector.ofFn fun i : Fin 128 =>
    baseCaseMultiply a[2 * i.val] a[2 * i.val + 1] b[2 * i.val] b[2 * i.val + 1]
      (ζ ^ (2 * bitRev 7 i.val + 1))).flatten⟩

end NTT

end Wychelean.KEM.MLKEM
