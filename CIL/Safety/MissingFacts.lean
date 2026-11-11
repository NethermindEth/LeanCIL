import CIL.Safety.SymbolicExecution

/-!
# The fact a stuck step lacks

When a LeanCIL step does not close, the residual of its step equation names the checked operation
it could not decide. `missingFactOf` reads that residual into a `MissingFact`, whose `hint` is the
fact to supply. The loop tactics word their error with it (`loopMissingHint`), and `CIL.Observe`
reports its `name` in the failure record, so both read one list. `stepResidual` gives the residual
to both.
-/

namespace CIL.Safety

open Lean

/-- The kind of fact a stuck step lacks, read from the terms its residual mentions. -/
inductive MissingFact where
  /-- A span's validity at the step's memory. -/
  | spanValidity
  /-- A span slice. -/
  | spanSlice
  /-- A span element's address. -/
  | spanElement
  /-- The allocation of a class instance against the heap budget. -/
  | objectAllocation
  /-- That an object reference forms, or reaches a field of the object's type. -/
  | objectForm
  /-- What a reference field of a class instance holds, or that it accepts a stored reference. -/
  | objectSlot
  /-- An `Unsafe.Add` result. -/
  | unsafeAdd
  /-- That a reference forms. -/
  | referenceForm
  /-- The checked access or permission required at this memory. -/
  | authority
  /-- A checked value or initialized-content snapshot at this memory. -/
  | contentSnapshot
  /-- The premise of a checked helper contract. -/
  | helperPrecondition
  /-- The step equation of a store. -/
  | storeStep
  /-- A local's frame fact, or a store's step equation, when the residual names neither. -/
  | frameOrStore

/-- The stable name of a missing fact's kind, as failure records report it. -/
def MissingFact.name : MissingFact → String
  | .spanValidity => "spanValidity"
  | .spanSlice => "spanSlice"
  | .spanElement => "spanElement"
  | .objectAllocation => "objectAllocation"
  | .objectForm => "objectForm"
  | .objectSlot => "objectSlot"
  | .unsafeAdd => "unsafeAdd"
  | .referenceForm => "referenceForm"
  | .authority => "authority"
  | .contentSnapshot => "contentSnapshot"
  | .helperPrecondition => "helperPrecondition"
  | .storeStep => "storeStep"
  | .frameOrStore => "frameOrStore"

/-- What to supply for a missing fact of this kind. -/
def MissingFact.hint : MissingFact → MessageData
  | .spanValidity => m!"the span's validity at this memory: a `CheckedSpan` of the caller's \
      memory, which the loop tactics read in every frame memory, or \
      `view.validate memory = .ok ()`"
  | .spanSlice => m!"the slice: `view.slice memory start length = .ok sliced`, such as from \
      `CheckedSpan.tail` at the caller's memory"
  | .spanElement => m!"the element's address: `view.element memory index = .ok item`, such as \
      from `CheckedSpan.head`"
  | .objectAllocation => m!"the allocation: `allocateObject memory type size = .ok (object, \
      after)` from `allocateObject_ok` with a heap budget covering the size, or the \
      `allocationFailure` from `allocateObject_insufficient`"
  | .objectSlot => m!"the reference field's slot: `readable.facts held targetLive` or \
      `readable.load_null held` of a named `ReferenceField.Readable`, `owned.store targetLive` of \
      an `Owned` one, or a `loadSlot` or `storeSlot` fact"
  | .objectForm => m!"that the object is live at this memory: a hypothesis `live : LiveObject \
      memory object`, or the `Readable` of a field the extraction names, such as \
      `Account.Balance.Readable memory object`, which also locates the field"
  | .unsafeAdd => m!"the `Unsafe.Add` result: `add memory base width offset = .ok reference` at \
      this memory or the caller's, such as `Writable.add_int`"
  | .referenceForm => m!"that the reference forms: `form memory reference = .ok reference`, or \
      an `access` or `add` fact it follows from, at this memory or the caller's"
  | .authority => m!"checked access at this memory, including the required permission, bounds \
      and alignment. A missing proof does not establish that access is forbidden; derive it \
      from `ValidCall`, the frame's writable homes or a preserved access fact"
  | .contentSnapshot => m!"a checked read or current content snapshot for this local or region. \
      Readable or writable access alone does not identify initialized contents. After an \
      overlapping write, use the updated snapshot; recover an unchanged snapshot only with \
      the required disjointness or confinement evidence. A snapshot may retain unknown bytes. \
      The missing fact does not prove \
      that the value changed or that the read is invalid"
  | .helperPrecondition => m!"the helper's precondition at the call's current memory. \
      Establish its access and content premises separately; a missing proof does not \
      establish that the helper's precondition is false"
  | .storeStep => m!"the step equation of a store with this stack"
  | .frameOrStore => m!"a `LoopFrame` at this memory for a local, or the step equation of a \
      store with this stack"

/-- The constants whose mention in a step's residual decides its `MissingFact`, in the order
    `missingFactOf` tests them. An object field's residual also mentions the byte operations
    under it, so the object kinds come first. A name here is checked against the environment
    by `Tests.LoopDiagnostics`. -/
def missingFactMentions : List (MissingFact × List Name) := [
  (.helperPrecondition, [`CIL.Safety.MethodContract.pre, `CIL.Safety.ValidCall]),
  (.authority, [`CIL.Safety.access, `CIL.Safety.permitted, `CIL.Safety.Writable,
    `CIL.Safety.WritableHomes, `CIL.Safety.CompleteWritableHomes]),
  (.spanValidity, [`CIL.Safety.SpanView.validate]),
  (.spanSlice, [`CIL.Safety.SpanView.slice]),
  (.spanElement, [`CIL.Safety.SpanView.element]),
  (.objectAllocation, [`CIL.Safety.allocateObject]),
  (.objectForm, [`CIL.Safety.formObject, `CIL.Safety.objectFieldAddress]),
  (.objectSlot, [`CIL.Safety.loadSlot, `CIL.Safety.storeSlot]),
  (.unsafeAdd, [`CIL.Safety.add]),
  (.referenceForm, [`CIL.Safety.form, `CIL.Safety.formValue]),
  (.contentSnapshot, [`CIL.Safety.loadValue, `CIL.Safety.read, `CIL.Safety.loadLocal,
    `CIL.Safety.loadSnapshot, `CIL.Safety.readSnapshot,
    `CIL.Safety.LocalSnapshots, `CIL.Safety.WordSnapshots, `CIL.Safety.Contents,
    `CIL.Safety.Filled]),
  (.storeStep, [`CIL.Safety.storeLocal, `CIL.Safety.storeValue, `CIL.Safety.write,
    `CIL.Safety.writeSnapshot])]

/-- The kind of fact a stuck step needs, from the residual of that step. -/
def missingFactOf (residual : Array Expr) : MissingFact :=
  let mentions (name : Name) : Bool :=
    residual.any fun goal => (goal.find? fun term => term.isConstOf name).isSome
  let spanLocal := residual.any fun goal => (goal.find? fun term =>
    term.isAppOf `CIL.Safety.loadLocal && term.getAppNumArgs >= 2 &&
      (term.getArg! 1).isAppOf `CIL.Safety.LocalSlot.span).isSome
  if spanLocal then .spanValidity
  else match missingFactMentions.find? (·.2.any mentions) with
    | some (fact, _) => fact
    | none => .frameOrStore

/-- A missing fact's explanation with the unresolved checked operation, which retains its
    memory, local or region arguments rather than inferring that any check has failed. -/
def missingFactHint (residual : Array Expr) : MessageData := Id.run do
  let fact := missingFactOf residual
  let contextual := ["authority", "contentSnapshot", "helperPrecondition"].contains fact.name
  unless contextual do return fact.hint
  let some (_, names) := missingFactMentions.find? (·.1.name == fact.name) | return fact.hint
  for goal in residual do
    if let some operation := goal.find? fun term =>
        term.isApp && term.getAppFn.constName?.any names.contains then
      return m!"{fact.hint}. The unresolved operation is{indentExpr operation}"
  return fact.hint

set_option hygiene false in
open Lean Elab Tactic Meta in
/-- The step goal `step` rewritten as far as the step equations and `prepared` go: the goals left,
    or `none` when rewriting cannot produce a residual. -/
def stepResidual (step : MVarId) (prepared : Array Term) : TacticM (Option (Array Expr)) := do
  let saved ← saveState
  try
    -- Normalization keeps the observer's unknown result open for the missing-fact diagnosis.
    let remaining ← Tactic.run step <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| (
        simp only [cil_instruction_step, cil_step, cil_guard, CIL.Safety.instructionStep,
          $[$prepared:term],*]
        cil_checked_normalize [$[$prepared:term],*])))
    let goals ← remaining.mapM fun goal => do instantiateMVars (← goal.getType)
    saved.restore
    return some goals.toArray
  catch _ =>
    saved.restore
    return none

end CIL.Safety
