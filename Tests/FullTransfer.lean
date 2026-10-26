import CIL.Interface.FullTransfer

/-! Exact-expression checks for shared full-verification term transfer. -/
namespace Tests.FullTransfer
open Lean Elab Command

/-- Binder spelling and implicitness must survive sharing. -/
def binders : (Nat → Nat) × ({_number : Nat} → Nat) :=
  (fun left => left, fun {right} => right)

/-- A proof with repeated arithmetic subexpressions. -/
theorem repeated (number : Nat) : number + 0 = number := Nat.add_zero number
#print axioms repeated

run_cmd do
  let environment ← getEnv
  let source ← match CIL.Interface.FullTransfer.capture environment
      environment.header.moduleNames `Transferred
      #[`Tests.FullTransfer.binders, `Tests.FullTransfer.repeated] with
    | .ok source => pure source
    | .error error => throwError error
  for command in (source.splitOn "\nrun_cmd").drop 1 do
    let parsed ← match Parser.runParserCategory (← getEnv) `command ("run_cmd" ++ command) with
      | .ok parsed => pure parsed
      | .error error => throwError error
    elabCommand parsed
  for name in #[`Tests.FullTransfer.binders, `Tests.FullTransfer.repeated] do
    let some original := environment.find? name | throwError "missing original"
    let some transferred := (← getEnv).find? (`Transferred ++ name) |
      throwError "missing transferred"
    unless original.type.equal transferred.type do throwError "changed declaration type"
    let some originalValue := original.value? (allowOpaque := true) | throwError "missing original value"
    let some transferredValue := transferred.value? (allowOpaque := true) | throwError "missing transferred value"
    unless originalValue.equal transferredValue do throwError "changed declaration value"

end Tests.FullTransfer
