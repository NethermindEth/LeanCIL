import CIL.Safety.StaticMemoryEquivalence
import CIL.Safety.NativeMethodTableEquivalence
import CIL.Safety.Execution
import CIL.Safety.StackAllocationEquivalence

/-!
# The checked interpreter respects memory equivalence

`step`, `run` and `invoke` give equivalent results on `Memory.Equivalent` memories: the same
faults, the same control flow and values, and equivalent final memory. Memory equivalence
ignores how the view list is represented, so `write_run_equivalent` lets the optimized
`write` replace the reference `writeAlwaysPrepend` without changing any checked execution.
-/

namespace CIL.Safety

/-- Reference truth tests depend only on the allocation metadata of equivalent memories. -/
theorem Memory.Equivalent.referenceNonNull {m n : Memory} (same : m.Equivalent n)
    (value : ManagedReference) : referenceNonNull m value = referenceNonNull n value := by
  simp only [CIL.Safety.referenceNonNull, same.formValue]

#print axioms Memory.Equivalent.referenceNonNull

/-- Reference equality ignores permission-list representation and byte contents. -/
theorem Memory.Equivalent.referenceEqual {m n : Memory} (same : m.Equivalent n)
    (left right : ManagedReference) : referenceEqual m left right = referenceEqual n left right := by
  simp only [CIL.Safety.referenceEqual, same.formValue, liveAllocation, same.allocations]

#print axioms Memory.Equivalent.referenceEqual

/-- Equivalent memories give the same unsigned pointer ordering. -/
theorem Memory.Equivalent.referenceLess {m n : Memory} (same : m.Equivalent n)
    (left right : ManagedReference) : referenceLess m left right = referenceLess n left right := by
  simp only [CIL.Safety.referenceLess, same.referencePositions]
#print axioms Memory.Equivalent.referenceLess

/-- Pointer offsets preserve allocation equivalence without inspecting byte contents. -/
theorem Memory.Equivalent.referenceSubtract {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (offset : CIL.Value) :
    referenceSubtract m reference offset = referenceSubtract n reference offset := by
  simp only [CIL.Safety.referenceSubtract, displaceReference, checkedAt, same.add]
#print axioms Memory.Equivalent.referenceSubtract
theorem Memory.Equivalent.checkedValue {m n : Memory} (same : m.Equivalent n)
    (value : Value) : checkedValue m value = checkedValue n value := by
  cases value <;> simp only [CIL.Safety.checkedValue, same.formValue, same.spanValidate,
    same.arrayValidate]

theorem Memory.Equivalent.checkedValues {m n : Memory} (same : m.Equivalent n)
    (values : List Value) :
    values.mapM (CIL.Safety.checkedValue m) = values.mapM (CIL.Safety.checkedValue n) := by
  have equality : CIL.Safety.checkedValue m = CIL.Safety.checkedValue n := funext same.checkedValue
  rw [equality]

/-- Control, values and frames agree exactly; only the representation of memory
    views may differ. -/
inductive FrameActionEquivalent : FrameAction → FrameAction → Prop where
  | next {m n : Memory} (same : m.Equivalent n) (pc stack frame) :
      FrameActionEquivalent (.next pc stack frame m) (.next pc stack frame n)
  | call {m n : Memory} (same : m.Equivalent n) (callee args rest) :
      FrameActionEquivalent (.call callee args rest m) (.call callee args rest n)
  | tailCall {m n : Memory} (same : m.Equivalent n) (callee args) :
      FrameActionEquivalent (.tailCall callee args m) (.tailCall callee args n)
  | construct {m n : Memory} (same : m.Equivalent n) (callee args rest frame temporary kind) :
      FrameActionEquivalent (.construct callee args rest frame temporary kind m)
        (.construct callee args rest frame temporary kind n)
  | returned {m n : Memory} (same : m.Equivalent n) (values) :
      FrameActionEquivalent (.returned values m) (.returned values n)

/-- Managed dispatch observes only stable identities and equivalent checked arguments. -/
theorem Memory.Equivalent.managedStep {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.ManagedOp) (pc : Nat) (frame : Frame) (stack : List Value) :
    ResultEquivalent FrameActionEquivalent (managedStep operation pc frame stack m)
      (managedStep operation pc frame stack n) := by
  unfold CIL.Safety.managedStep
  split <;> try simp only [same.checkedValues, same.addNativeTable, same.loadNativeTable]
  all_goals repeat' first
    | exact .error _
    | exact .ok (.next same _ _ _)
    | exact .ok (.call same _ _ _)
    | exact .ok (.tailCall same _ _)
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.managedStep

/-- Fresh array bytes and authority do not depend on the old view-list representation. -/
theorem Memory.Equivalent.allocateArray {m n : Memory} (same : m.Equivalent n)
    (element : CIL.ArrayElement) (length : Nat) :
    ResultEquivalent MemoryLastEquivalent (allocateArray m element length)
      (allocateArray n element length) := by
  unfold CIL.Safety.allocateArray
  repeat first
    | exact .error _
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind ((same.allocate _).mapError _)
       intro left right related
       obtain ⟨identity, source⟩ := left
       obtain ⟨otherIdentity, target⟩ := right
       obtain ⟨rfl, equivalent⟩ := related
       change source.Equivalent target at equivalent
       apply ResultEquivalent.ok
       refine ⟨rfl, ?_⟩
       have initialized : Memory.Equivalent
           { source with cells := fun other offset =>
               if other == identity then ⟨0, true⟩ else source.cells other offset }
           { target with cells := fun other offset =>
               if other == identity then ⟨0, true⟩ else target.cells other offset } :=
         ⟨equivalent.allocations, by simp only [equivalent.cells], equivalent.permissions,
           equivalent.nextIdentity, equivalent.staticBindings, equivalent.stackLimit⟩
       exact initialized.prependView _)
    | unfold checkedAt
    | split
#print axioms Memory.Equivalent.allocateArray

/-- Array length decoding and allocation preserve exact outcomes over equivalent memories. -/
theorem Memory.Equivalent.newArray {m n : Memory} (same : m.Equivalent n)
    (element : CIL.ArrayElement) (length : CIL.Value) :
    ResultEquivalent MemoryLastEquivalent (newArray m element length)
      (newArray n element length) := by
  cases length <;> simp only [CIL.Safety.newArray, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals repeat first
    | exact .error _
    | exact same.allocateArray _ _
    | split
#print axioms Memory.Equivalent.newArray

theorem Memory.Equivalent.step {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) :
    ResultEquivalent FrameActionEquivalent (step body op pc args frame stack m)
      (step body op pc args frame stack n) := by
  unfold CIL.Safety.step
  dsimp only
  split <;> try simp only [same.checkedValue, same.checkedValues, same.loadLocal, same.localAddress,
    same.referenceNonNull, same.referenceEqual, same.referenceDifference,
    same.referenceLess, same.referenceSubtract]
  all_goals repeat' first
    | exact same.managedStep _ _ _ _
    | (apply ResultEquivalent.bind (same.newArray _ _)
       intro left right related
       obtain ⟨view, memory⟩ := left
       obtain ⟨otherView, otherMemory⟩ := right
       obtain ⟨rfl, equivalent⟩ := related
       exact .ok (.next equivalent _ _ _))
    | (apply ResultEquivalent.bind (same.allocateStack _ _ _)
       intro left right related
       obtain ⟨reference, owner, allocated⟩ := left
       obtain ⟨otherReference, otherOwner, otherAllocated⟩ := right
       obtain ⟨rfl, rfl, equivalent⟩ := related
       exact .ok (.next equivalent _ _ _))
    | exact .error _
    | exact .ok (.next same _ _ _)
    | exact .ok (.call same _ _ _)
    | exact .ok (.tailCall same _ _)
    | exact .ok (.returned same _)
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.storeLocal _ _)
       intro left right related
       obtain ⟨slot, memory⟩ := left
       obtain ⟨otherSlot, otherMemory⟩ := right
       obtain ⟨rfl, equivalent⟩ := related
       exact .ok (.next equivalent _ _ _))
    | (apply ResultEquivalent.bind (same.memoryInstruction _ _)
       intro left right related
       obtain ⟨memory, values⟩ := left
       obtain ⟨otherMemory, otherValues⟩ := right
       obtain ⟨equivalent, rfl⟩ := related
       cases values with
       | nil => exact .error _
       | cons value rest =>
         apply ResultEquivalent.bind (equivalent.storeLocal _ _)
         intro left right related
         obtain ⟨slot, memory⟩ := left
         obtain ⟨otherSlot, otherMemory⟩ := right
         obtain ⟨rfl, stored⟩ := related
         exact .ok (.next stored _ _ _))
    | (apply ResultEquivalent.bind (same.staticInstruction _ _ _ _)
       intro left right related
       obtain ⟨memory, values⟩ := left
       obtain ⟨otherMemory, otherValues⟩ := right
       obtain ⟨equivalent, rfl⟩ := related
       exact .ok (.next equivalent _ _ _))
    | (apply ResultEquivalent.bind (same.instruction _ _)
       intro left right related
       obtain ⟨memory, values⟩ := left
       obtain ⟨otherMemory, otherValues⟩ := right
       obtain ⟨equivalent, rfl⟩ := related
       exact .ok (.next equivalent _ _ _))
    | split
  all_goals
    apply ResultEquivalent.bind (same.allocateHome _ _ _)
    intro left right related
    obtain ⟨reference, memory⟩ := left
    obtain ⟨otherReference, otherMemory⟩ := right
    obtain ⟨rfl, equivalent⟩ := related
    first
      | (apply ResultEquivalent.bind (equivalent.storeValue _ _)
         intro left right related
         exact .ok (.construct related _ _ _ _ _ _))
      | (apply ResultEquivalent.bind (equivalent.storeLocal _ _)
         intro left right related
         obtain ⟨slot, memory⟩ := left
         obtain ⟨otherSlot, otherMemory⟩ := right
         obtain ⟨rfl, stored⟩ := related
         exact .ok (.construct stored _ _ _ _ _ _))

/-- Equivalent memories give the same run outcome: the same fault, or equivalent final
    memory with the same returned values. -/
theorem Memory.Equivalent.run {m n : Memory} (same : m.Equivalent n)
    (program : CIL.Program) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (run program fuel method pc args frame stack m)
      (run program fuel method pc args frame stack n) := by
  induction fuel generalizing m n method pc args frame stack with
  | zero => exact .error _
  | succ fuel ih =>
    simp only [CIL.Safety.run]
    split <;> try exact .error _
    split <;> try exact .error _
    apply ResultEquivalent.bind ((same.step _ _ _ _ _ _).mapError _)
    intro left right related
    cases related with
    | next equivalent target values nextFrame => exact ih equivalent _ _ _ _ _
    | returned equivalent values =>
      have leftFrame := equivalent.leaveFrame frame
      simp only [leftFrame.checkedValues]
      apply ResultEquivalent.bind_same
      intro result
      exact .ok ⟨leftFrame, rfl⟩
    | call equivalent callee arguments rest =>
      dsimp only
      split <;> try exact .error _
      apply ResultEquivalent.bind ((equivalent.enterFrame _ _).mapError _)
      intro left right related
      obtain ⟨childFrame, memory⟩ := left
      obtain ⟨otherFrame, otherMemory⟩ := right
      obtain ⟨rfl, entered⟩ := related
      apply ResultEquivalent.bind (ih entered _ _ _ _ _)
      intro left right related
      obtain ⟨memory, result⟩ := left
      obtain ⟨otherMemory, otherResult⟩ := right
      obtain ⟨finished, rfl⟩ := related
      exact ih finished _ _ _ _ _
    | tailCall equivalent callee arguments =>
      dsimp only
      split <;> try exact .error _
      split <;> try exact .error _
      have retired := equivalent.leaveFrame frame
      simp only [retired.checkedValues]
      apply ResultEquivalent.bind_same
      intro checked
      apply ResultEquivalent.bind ((retired.enterFrame _ _).mapError _)
      intro left right related
      obtain ⟨childFrame, memory⟩ := left
      obtain ⟨otherFrame, otherMemory⟩ := right
      obtain ⟨rfl, entered⟩ := related
      exact ih entered _ _ _ _ _
    | construct equivalent callee arguments rest nextFrame temporary kind =>
      dsimp only
      split <;> try exact .error _
      apply ResultEquivalent.bind ((equivalent.enterFrame _ _).mapError _)
      intro left right related
      obtain ⟨childFrame, memory⟩ := left
      obtain ⟨otherFrame, otherMemory⟩ := right
      obtain ⟨rfl, entered⟩ := related
      apply ResultEquivalent.bind (ih entered _ _ _ _ _)
      intro left right related
      obtain ⟨memory, result⟩ := left
      obtain ⟨otherMemory, otherResult⟩ := right
      obtain ⟨finished, rfl⟩ := related
      split
      · exact .error _
      · simp only [finished.loadLocal]
        apply ResultEquivalent.bind_same
        intro value
        exact ih finished _ _ _ _ _

theorem Memory.Equivalent.invoke {m n : Memory} (same : m.Equivalent n)
    (program : CIL.Program) (fuel method : Nat) (args : List Value) :
    ResultEquivalent MemoryFirstEquivalent (invoke program fuel method args m)
      (invoke program fuel method args n) := by
  unfold CIL.Safety.invoke
  split <;> try exact .error _
  simp only [same.checkedValues]
  apply ResultEquivalent.bind_same
  intro values
  apply ResultEquivalent.bind ((same.enterFrame _ _).mapError _)
  intro left right related
  obtain ⟨frame, memory⟩ := left
  obtain ⟨otherFrame, otherMemory⟩ := right
  obtain ⟨rfl, entered⟩ := related
  exact entered.run _ _ _ _ _ _ _

/-- Replacing the reference `writeAlwaysPrepend` by `write` preserves every subsequent
    checked execution, including its exact located failure or returned values. -/
theorem write_run_equivalent (memory : Memory) (reference : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (locate : Fault → LocatedFault)
    (program : CIL.Program) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent
      (((write memory reference bytes alignment).mapError locate).bind fun updated =>
        run program fuel method pc args frame stack updated)
      (((writeAlwaysPrepend memory reference bytes alignment).mapError locate).bind fun updated =>
        run program fuel method pc args frame stack updated) := by
  apply ResultEquivalent.bind
    ((write_equivalent_alwaysPrepend memory reference bytes alignment).mapError locate)
  intro left right same
  exact same.run program fuel method pc args frame stack

#print axioms write_run_equivalent
#print axioms Memory.Equivalent.run
#print axioms Memory.Equivalent.invoke
#print axioms Memory.Equivalent.step
#print axioms Memory.Equivalent.checkedValues

end CIL.Safety
