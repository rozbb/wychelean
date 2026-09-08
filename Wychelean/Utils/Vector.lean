/-!
`Vector` helpers not provided by core Lean.
-/

universe u

namespace Vector

/-- Split a vector of length `n` into `n / m` consecutive chunks of length `m`; `m` must divide `n`. -/
def toChunks {α : Type u} {n : Nat} (m : Nat) (v : Vector α n) (_ : n % m = 0) :
    Vector (Vector α m) (n / m) :=
  Vector.ofFn fun (i : Fin (n / m)) => Vector.ofFn fun (j : Fin m) =>
    v[i.val * m + j.val]'(by
      calc i.val * m + j.val < i.val * m + m := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * m := (Nat.succ_mul _ _).symm
        _ ≤ n / m * m := Nat.mul_le_mul_right m i.isLt
        _ ≤ n := Nat.div_mul_le_self n m)

end Vector
