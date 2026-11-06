import Lean
import CIL.Safety.Obligations
import CIL.Safety.ObserveOptions

/-!
# Failure records

What a LeanCIL tactic had established where it stopped: the method and pc it reached, the
instruction there, the obligation it was handed, the reached and expected states, and the shape of
the fact it lacked. `CIL.Observe` builds a record for each error a LeanCIL tactic raises, and for
each goal one leaves unsolved, and logs it as one line of JSON after `failureMarker`, which
`leancil verify --format json` reads instead of the error's prose. Only an importer of
`CIL.Observe` with `cil.diagnostics` set builds records; the tactics themselves build none.
-/

namespace CIL.Safety

open Lean Meta

/-- The text that starts the line of a failure record, version 1. -/
def failureMarker : String := "[LeanCIL failure v1] "

/-- Where a LeanCIL tactic failed or stopped. A field it could not determine is `none`, with the
    reason in `unknown` under the field's name; suggestions are kept apart from these facts. -/
structure FailureRecord where
  /-- The tactic that failed or stopped. -/
  tactic : String
  /-- The line and column of the error the record explains. -/
  error : Option Position := none
  /-- Whether the tactic succeeded and left the goal open rather than raising the error. -/
  stopped : Bool := false
  /-- The obligation the tactic was handed, by its tag. -/
  obligation : Option Name := none
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

/-- `record` as one line of JSON, with its expressions printed in the current context. -/
def FailureRecord.render (record : FailureRecord) : MetaM String := do
  let text (data : MessageData) : MetaM Json :=
    return Json.str (← (← addMessageContext data).toString)
  let parts (entries : Array (String × Expr)) : MetaM Json := do
    return Json.mkObj (← entries.toList.mapM fun (name, value) => do
      return (name, ← text m!"{value}"))
  let untagged := "the goal the tactic was handed carries no obligation tag"
  -- Every field left null says why, even when the analysis gave no reason of its own.
  let unreported := [("method", record.method.isNone), ("pc", record.pc.isNone),
      ("instruction", record.instruction.isNone), ("missing", record.missing.isNone),
      ("obligation", record.obligation.isNone)].filterMap
    fun (field, absent) => if absent && !record.unknown.any (·.1 == field) then
      some (field, if field == "obligation" then untagged
        else s!"the goal {record.tactic} left does not determine it") else none
  let error := match record.error with
    | some position => Json.mkObj [("line", position.line), ("column", position.column)]
    | none => Json.null
  let fields : List (String × Json) := [
    ("tactic", Json.str record.tactic),
    ("error", error),
    ("stopped", Json.bool record.stopped),
    ("method", toJson record.method),
    ("pc", toJson record.pc),
    ("instruction", ← match record.instruction with
      | some op => text m!"{op}"
      | none => pure Json.null),
    ("obligation", toJson (record.obligation.map (·.toString))),
    ("reached", ← parts record.reached),
    ("expected", ← parts record.expected),
    ("missing", toJson record.missing),
    ("residual", Json.arr (← record.residual.mapM fun term => text m!"{term}")),
    ("suggestions", Json.arr (← record.suggestions.mapM text)),
    ("unknown", Json.mkObj ((record.unknown ++ unreported.toArray).toList.map
      fun (field, reason) => (field, Json.str reason)))]
  return (Json.mkObj fields).compress

end CIL.Safety
