import Wychelean.KEM.MLKEM.Scheme

/-! The specification stands alone: it imports neither the ring library nor its own proofs. -/

open Lean in
run_meta do
  let deps := (← getEnv).allImportedModuleNames.filter fun m =>
    (`Wychelean.Utils.PolyRing).isPrefixOf m || (`Wychelean.KEM.MLKEM.Properties).isPrefixOf m
  unless deps.isEmpty do
    throwError m!"the ML-KEM specification imports {deps.toList}"
