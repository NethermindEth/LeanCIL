import Lean
import CIL.Safety.Obligations

/-!
# Failure records

What a LeanCIL tactic established when it stops: the method and pc it reached, the instruction
there, the obligation its goal is, the reached and expected states, and the shape of the fact it
lacks. With the option `cil.diagnostics` set, a failing tactic appends these as one line to its
error, after `failureMarker`, as a JSON object, which `leancil verify --format json` reads instead
of the error's prose. With the option unset the error is unchanged and no record is built.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

/-- Whether a failing LeanCIL tactic appends its `FailureRecord` to its error. -/
register_option cil.diagnostics : Bool := {
  defValue := false
  descr := "append a machine-readable record of what a failing LeanCIL tactic established"
}

/-- The text that starts the line of a failure record in an error message, version 1. -/
def failureMarker : String := "[LeanCIL failure v1] "

/-- What a stopped LeanCIL tactic established. A field it could not determine is `none`, with the
    reason in `unknown` under the field's name; suggestions are kept apart from these facts. -/
structure FailureRecord where
  /-- The tactic that stopped. -/
  tactic : String
  /-- The index of the method the goal steps, when a literal. -/
  method : Option Nat := none
  /-- The pc the goal reached, when a literal. -/
  pc : Option Nat := none
  /-- The instruction at `pc`. -/
  instruction : Option Expr := none
  /-- The parts of the reached state, by name (`pc`, `frame`, `stack`, `memory`). -/
  reached : Array (String × Expr) := #[]
  /-- The parts of the expected state that differ from the reached one, by name. -/
  expected : Array (String × Expr) := #[]
  /-- The kind of fact the step lacks, named by `MissingFact.name`. -/
  missing : Option String := none
  /-- The terms the step reduces to, which the missing fact must prove. -/
  residual : Array Expr := #[]
  /-- What to try next. Advice, never a fact of the proof state. -/
  suggestions : Array MessageData := #[]
  /-- The fields left `none`, each with the reason it could not be determined. -/
  unknown : Array (String × String) := #[]

/-- The tag of the main goal when it names an obligation of `obligationTags`. -/
def mainObligation? : TacticM (Option Name) := do
  let some goal := (← getGoals).head? | return none
  let tag := (← goal.getTag).eraseMacroScopes
  return (obligationOf? tag).map fun _ => tag

/-- `record` as one line of JSON, with its expressions printed in the main goal's context. -/
def FailureRecord.render (record : FailureRecord) : TacticM String := withMainContext do
  let text (data : MessageData) : TacticM Json :=
    return Json.str (← (← addMessageContext data).toString)
  let parts (entries : Array (String × Expr)) : TacticM Json := do
    return Json.mkObj (← entries.toList.mapM fun (name, value) => do
      return (name, ← text m!"{value}"))
  let obligation ← mainObligation?
  -- Every field left null says why, even when the tactic gave no reason of its own.
  let unreported := [("method", record.method.isNone), ("pc", record.pc.isNone),
      ("instruction", record.instruction.isNone), ("missing", record.missing.isNone)].filterMap
    fun (field, absent) => if absent && !record.unknown.any (·.1 == field) then
      some (field, s!"{record.tactic} does not determine it at this failure") else none
  let unknown := record.unknown ++ unreported.toArray ++
    (if obligation.isNone then #[("obligation", "the goal carries no obligation tag")] else #[])
  let fields : List (String × Json) := [
    ("tactic", Json.str record.tactic),
    ("method", toJson record.method),
    ("pc", toJson record.pc),
    ("instruction", ← match record.instruction with
      | some op => text m!"{op}"
      | none => pure Json.null),
    ("obligation", toJson (obligation.map (·.toString))),
    ("reached", ← parts record.reached),
    ("expected", ← parts record.expected),
    ("missing", toJson record.missing),
    ("residual", Json.arr (← record.residual.mapM fun term => text m!"{term}")),
    ("suggestions", Json.arr (← record.suggestions.mapM text)),
    ("unknown", Json.mkObj (unknown.toList.map fun (field, reason) => (field, Json.str reason)))]
  return (Json.mkObj fields).compress

/-- Throw `message`, followed when `cil.diagnostics` is set by the line of the record `record`
    builds; `record` runs only then, so an unset option costs nothing. -/
def throwFailure {α : Type} (message : MessageData) (record : TacticM FailureRecord) :
    TacticM α := do
  unless cil.diagnostics.get (← getOptions) do throwError message
  let line ← try (← record).render catch error =>
    pure (Json.mkObj [("tactic", Json.null), ("unknown", Json.mkObj
      [("record", Json.str (← error.toMessageData.toString))])]).compress
  throwError m!"{message}\n{failureMarker}{line}"

end CIL.Safety
