import Wychelean

/-!
# Axiom checker

This model checks that all the axioms used in Wychelean are in a small allowlist.
-/

open Lean

-- We only allow three axioms, and they're all built into Lean
def allowlist : List String :=
  [-- Lean builtin. Propositional extensionality, `(a ↔ b) → a = b`
   "propext",
   -- Lean builtin. Axiom of choice
   "Classical.choice",
   -- Lean builtin. Elements related by R are definitionally equal in quotient space over rel R
   "Quot.sound"]

-- Go through every constant declared in a `Wychelean.*` module and dump its axioms
run_cmd do
  let env ← getEnv
  let decls := env.constants.toList.filterMap fun (c, _) => do
    let idx ← env.getModuleIdxFor? c
    let mod ← env.header.moduleNames[idx.toNat]?
    guard ((`Wychelean).isPrefixOf mod)
    return c
  if decls.isEmpty then
    throwError "NO AUDIT SURFACE — no declarations found in `Wychelean.*` modules. Has the library \
      been renamed, or did its import fail?"
  -- Each axiom we find, with one declaration that uses it
  let mut found : Array (String × Name) := #[]
  for d in decls do
    for a in (← collectAxioms d) do
      let s := a.toString
      unless found.any (·.1 == s) do found := found.push (s, d)
  let unexpected := found.filter (fun (a, _) => !allowlist.contains a)
  let unused := allowlist.filter (fun a => !found.any (·.1 == a))
  unless unexpected.isEmpty && unused.isEmpty do
    throwError "AXIOM SET CHANGED — AxiomCheck.lean is out of date.\n\
      New assumptions not in the allowlist (axiom, a declaration using it): \
      {unexpected.toList}\n\
      Audited assumptions no longer used: {unused}"
