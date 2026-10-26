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

/-- Universe parameters and successor levels retain their exact structure. -/
def universeIdentity.{level} {α : Sort level} (value : α) : α := value

/-- Projection and local let expressions remain intact. -/
def projected (pair : Nat × Nat) : Nat := let value := pair.1; value + value

/-- String literals retain escaping and embedded line breaks. -/
def text : String := "quoted \"text\"\n"

run_cmd do
  let environment ← getEnv
  let source ← match CIL.Interface.FullTransfer.capture environment
      environment.header.moduleNames `Transferred
      #[`Tests.FullTransfer.binders, `Tests.FullTransfer.repeated,
        `Tests.FullTransfer.universeIdentity, `Tests.FullTransfer.projected, `Tests.FullTransfer.text] with
    | .ok source => pure source
    | .error error => throwError error
  for command in (source.splitOn "\nrun_cmd").drop 1 do
    let parsed ← match Parser.runParserCategory (← getEnv) `command ("run_cmd" ++ command) with
      | .ok parsed => pure parsed
      | .error error => throwError error
    elabCommand parsed
  for name in #[`Tests.FullTransfer.binders, `Tests.FullTransfer.repeated,
        `Tests.FullTransfer.universeIdentity, `Tests.FullTransfer.projected, `Tests.FullTransfer.text] do
    let some original := environment.find? name | throwError "missing original"
    let some transferred := (← getEnv).find? (`Transferred ++ name) |
      throwError "missing transferred"
    unless original.type.equal transferred.type do throwError "changed declaration type"
    let some originalValue := original.value? (allowOpaque := true) |
      throwError "missing original value"
    let some transferredValue := transferred.value? (allowOpaque := true) |
      throwError "missing transferred value"
    unless originalValue.equal transferredValue do throwError "changed declaration value"

run_cmd do
  for source in ["[]", "[{\"app\":{\"fn\":0,\"argument\":0}}]",
      "[{\"alias\":{\"index\":1}}]"] do
    match CIL.Interface.FullTransfer.decode source 0 0 with
    | .error "Invalid full-verification expression reference" => pure ()
    | other => throwError "invalid reference was not rejected: {repr other}"
  let invalidBinder := "[{\"bvar\":{\"index\":0}}," ++
    "{\"lam\":{\"name\":\"anonymous\",\"type\":0,\"body\":0,\"binder\":4}}]"
  match CIL.Interface.FullTransfer.decode invalidBinder 1 1 with
  | .error "Invalid full-verification binder annotation" => pure ()
  | other => throwError "invalid binder was not rejected: {repr other}"

end Tests.FullTransfer
