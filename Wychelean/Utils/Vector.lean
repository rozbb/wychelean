/-!
`Vector` helpers not provided by core Lean.
-/

universe u

namespace Vector

/-- Split a vector of length `n * m` into `n` consecutive chunks of length `m`. -/
def toChunks {α : Type u} {n : Nat} (m : Nat) (v : Vector α (n * m)) :
    Vector (Vector α m) n :=
  Vector.ofFn fun (i : Fin n) => Vector.ofFn fun (j : Fin m) =>
    v[i.val * m + j.val]'(by
      calc i.val * m + j.val < i.val * m + m := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * m := (Nat.succ_mul _ _).symm
        _ ≤ n * m := Nat.mul_le_mul_right m i.isLt)

end Vector
