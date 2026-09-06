import Wychelean.Utils.Vector
import Tests.Harness

namespace Tests.Utils.Vector

/-- Chunks as a list of lists, for comparison. -/
private def chunks {α : Type} {n m : Nat} (v : Vector (Vector α m) n) : List (List α) :=
  v.toList.map (·.toList)

private def v6 : Vector Nat 6 := #v[1, 2, 3, 4, 5, 6]

def tests : List Test := [
  expectEq "toChunks 3 2" (chunks (v6.toChunks 3 2)) [[1, 2], [3, 4], [5, 6]],
  expectEq "toChunks 1 6" (chunks (v6.toChunks 1 6)) [[1, 2, 3, 4, 5, 6]],
  expectEq "toChunks 6 1" (chunks (v6.toChunks 6 1)) [[1], [2], [3], [4], [5], [6]],
  expectEq "toChunks 0 4 of empty" (chunks ((#v[] : Vector Nat 0).toChunks 0 4)) [],
  expectEq "toChunks 2 0 of empty" (chunks ((#v[] : Vector Nat 0).toChunks 2 0)) [[], []]
]

end Tests.Utils.Vector
