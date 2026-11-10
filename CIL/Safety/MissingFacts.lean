import Lean

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
  /-- What a load reads. -/
  | load
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
  | .load => "load"
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
  | .load => m!"what the load reads: a `loadValue` fact at this memory, such as from \
      `(span.within wellFormed frame).head`"
  | .storeStep => m!"the step equation of a store with this stack"
  | .frameOrStore => m!"a `LoopFrame` at this memory for a local, or the step equation of a \
      store with this stack"

/-- The constants whose mention in a step's residual decides its `MissingFact`, in the order
    `missingFactOf` tests them. An object field's residual also mentions the byte operations
    under it, so the object kinds come first. A name here is checked against the environment
    by `Tests.LoopDiagnostics`. -/
def missingFactMentions : List (MissingFact × List Name) := [
  (.spanValidity, [`CIL.Safety.SpanView.validate]),
  (.spanSlice, [`CIL.Safety.SpanView.slice]),
  (.spanElement, [`CIL.Safety.SpanView.element]),
  (.objectAllocation, [`CIL.Safety.allocateObject]),
  (.objectForm, [`CIL.Safety.formObject, `CIL.Safety.objectFieldAddress]),
  (.objectSlot, [`CIL.Safety.loadSlot, `CIL.Safety.storeSlot]),
  (.unsafeAdd, [`CIL.Safety.add]),
  (.referenceForm, [`CIL.Safety.form, `CIL.Safety.formValue]),
  (.load, [`CIL.Safety.loadValue, `CIL.Safety.read]),
  (.storeStep, [`CIL.Safety.storeLocal, `CIL.Safety.storeValue, `CIL.Safety.write])]

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

-- The lemma and simp set names resolve where the proof runs; this module imports none of them.
set_option hygiene false in
open Lean Elab Tactic Meta in
/-- The step goal `step` rewritten as far as the step equations and `prepared` go: the goals left,
    or `none` when nothing rewrites it, as when the proof does not import the step equations. -/
def stepResidual (step : MVarId) (prepared : Array Term) : TacticM (Option (Array Expr)) := do
  let saved ← saveState
  try
    let remaining ← Tactic.run step <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| (
        simp only [cil_instruction_step, cil_step, cil_guard, CIL.Safety.instructionStep,
          $[$prepared:term],*]
        try simp [cil_guard, cil_checked, CIL.Safety.checkedValue, CIL.Safety.numericValue,
          CIL.Safety.scalars, CIL.Safety.formValue, CIL.Safety.checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure, $[$prepared:term],*])))
    let goals ← remaining.mapM fun goal => do instantiateMVars (← goal.getType)
    saved.restore
    return some goals.toArray
  catch _ =>
    saved.restore
    return none

end CIL.Safety
