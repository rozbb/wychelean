import Tests.Hashes.SHA256.Basic
import Tests.Hashes.SHA256.NistShortMsg
import Tests.Hashes.SHA256.NistLongMsg

/-!
NIST CAVP SHA-256 byte-oriented tests: ShortMsg and LongMsg.
-/

namespace Tests.Hashes.SHA256.Nist

open Wychelean
open Wychelean.Hashes.SHA256

/-- Indices of the vectors whose digest does not match. -/
def failures (vectors : Array HashVector) : List Nat :=
  vectors.toList.zipIdx.filterMap fun (v, i) =>
    if sha256Hex (Hex.decode v.msg).get! == v.digest then none else some i

example : failures shortMsg = [] := by native_decide
example : failures longMsg = [] := by native_decide

end Tests.Hashes.SHA256.Nist
