/-!
Hex encoding of byte strings.
-/

namespace Wychelean.Hex

/-- Lowercase hex encoding. -/
def encode (bytes : Array UInt8) : String :=
  bytes.foldl (init := "") fun s b =>
    (s.push (Nat.digitChar (b.toNat / 16))).push (Nat.digitChar (b.toNat % 16))

private def digitValue (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Decode a hex string of even length, upper or lower case. `none` if malformed. -/
def decode (s : String) : Option (Array UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then none
  let mut out := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    let hi ← digitValue cs[2 * i]!
    let lo ← digitValue cs[2 * i + 1]!
    out := out.push (hi * 16 + lo)
  return out

end Wychelean.Hex
