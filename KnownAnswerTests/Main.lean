import Wychelean

structure ScalarMulTest where
  name: String
  point: Vector UInt8 32
  scalar: Vector UInt8 32
  expected: Vector UInt8 32

def scalarMulTests: List ScalarMulTest := [
  { name := "RFC 7748 5.2 vector 1",
    point := #v[
  230, 219, 104, 103, 88, 48, 48, 219, 53, 148, 193, 164, 36, 177, 95, 124, 114, 102, 36, 236,
     38, 179, 53, 59, 16, 169, 3, 166, 208, 171, 28, 76],
    scalar := #v[
  165, 70, 227, 107, 240, 82, 124, 157, 59, 22, 21, 75, 130, 70, 94, 221, 98, 20, 76, 10, 193,
     252, 90, 24, 80, 106, 34, 68, 186, 68, 154, 196],
    expected := #v[
  195, 218, 85, 55, 157, 233, 198, 144, 142, 148, 234, 77, 242, 141, 8, 79, 50, 236, 207, 3,
     73, 28, 113, 247, 84, 180, 7, 85, 119, 162, 133, 82] },
  { name := "RFC 7748 5.2 vector 2",
    point := #v[
  229, 33, 15, 18, 120, 104, 17, 211, 244, 183, 149, 157, 5, 56, 174, 44, 49, 219, 231, 16,
     111, 192, 60, 62, 252, 76, 213, 73, 199, 21, 164, 147],
    scalar := #v[
  75, 102, 233, 212, 209, 180, 103, 60, 90, 210, 38, 145, 149, 125, 106, 245, 193, 27, 100, 33,
     224, 234, 1, 212, 44, 164, 22, 158, 121, 24, 186, 13],
    expected := #v[
  149, 203, 222, 148, 118, 232, 144, 125, 122, 173, 228, 92, 180, 184, 115, 248, 139, 89, 90,
     104, 121, 159, 161, 82, 230, 248, 247, 100, 122, 172, 121, 87] },
  { name := "twist point u = 2",
    point := #v[
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    scalar := #v[
  165, 70, 227, 107, 240, 82, 124, 157, 59, 22, 21, 75, 130, 70, 94, 221, 98, 20, 76, 10, 193,
     252, 90, 24, 80, 106, 34, 68, 186, 68, 154, 196],
    expected := #v[
  113, 202, 203, 160, 182, 93, 175, 83, 221, 249, 194, 31, 180, 52, 188, 88, 238, 92, 250, 57,
     84, 209, 182, 66, 252, 81, 85, 4, 143, 3, 70, 111] }
]

def main: IO UInt32 := do
  let mut failed := 0
  for t in scalarMulTests do
    let got := scalarMul t.point t.scalar
    if got.toList == t.expected.toList then
      IO.println s!"ok   {t.name}"
    else
      failed := failed + 1
      IO.println s!"FAIL {t.name}\n  expected {t.expected.toList}\n  got      {got.toList}"
  if failed == 0 then
    IO.println s!"all {scalarMulTests.length} known answer tests passed"
    return 0
  else
    IO.println s!"{failed} known answer test(s) failed"
    return 1
