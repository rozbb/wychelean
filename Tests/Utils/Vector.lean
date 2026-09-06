import Wychelean.Utils.Vector

private def v6 : Vector Nat 6 := #v[1, 2, 3, 4, 5, 6]

/-- Chunks as a list of lists, for comparison. -/
private def chunks {α : Type} {n m : Nat} (v : Vector (Vector α m) n) : List (List α) :=
  v.toList.map (·.toList)

example : chunks (v6.toChunks 3 2) = [[1, 2], [3, 4], [5, 6]] := by native_decide
example : chunks (v6.toChunks 1 6) = [[1, 2, 3, 4, 5, 6]] := by native_decide
example : chunks (v6.toChunks 6 1) = [[1], [2], [3], [4], [5], [6]] := by native_decide
example : chunks ((#v[] : Vector Nat 0).toChunks 0 4) = [] := by native_decide
example : chunks ((#v[] : Vector Nat 0).toChunks 2 0) = [[], []] := by native_decide
