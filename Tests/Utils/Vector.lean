import Wychelean.Utils.Vector

private def v6 : Vector Nat 6 := #v[1, 2, 3, 4, 5, 6]

/-- Chunks as a list of lists, for comparison. -/
private def chunks {α : Type} {n m : Nat} (v : Vector (Vector α m) n) : List (List α) :=
  v.toList.map (·.toList)

example : chunks (v6.toChunks 2 (by decide)) = [[1, 2], [3, 4], [5, 6]] := by native_decide
example : chunks (v6.toChunks 6 (by decide)) = [[1, 2, 3, 4, 5, 6]] := by native_decide
example : chunks (v6.toChunks 1 (by decide)) = [[1], [2], [3], [4], [5], [6]] := by native_decide
example : chunks ((#v[] : Vector Nat 0).toChunks 4 (by decide)) = [] := by native_decide
