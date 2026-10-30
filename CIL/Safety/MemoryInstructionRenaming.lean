import CIL.Safety.CheckedValueRenaming
import CIL.Safety.ViewPositionRenaming
import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.ReferenceRenaming
import CIL.Safety.CheckedReferenceBounds

/-!
# Memory instruction simulation

Successful memory instructions transport their checked effects and evaluation stacks across
an allocation renaming. Local-home insertion does not change scalar computation or access checks.
-/

namespace CIL.Safety

/-- An observable checked outcome is successful or raises a named CLR exception. -/
def SuccessOrThrow : ExecutionResult α → Prop
  | .ok _ => True
  | .error (.thrown _) => True
  | .error _ => False

/-- A successful or throwing sequence cannot start with an unobservable failure. -/
theorem SuccessOrThrow.bind_left {first : ExecutionResult α}
    {next : α → ExecutionResult β} (observable : SuccessOrThrow (first >>= next)) :
    SuccessOrThrow first := by
  cases first with
  | ok value => trivial
  | error fault => cases fault <;> exact observable
#print axioms SuccessOrThrow.bind_left

/-- Validating a byte view preserves both the checked fault and its allocation-relative location. -/
theorem Memory.Renamed.checkedSpanValidate {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit) (width : Nat := 0) :
    ResultRenamed mapping Eq (checkedAt view.reference width (view.validate source))
      (checkedAt (mapping.managedReference view.reference) width
        ((mapping.spanView view).validate target)) := by
  rw [related.spanValidate view bound]
  exact (ResultEquivalent.eq_refl _).checkedAt _ _
#print axioms Memory.Renamed.checkedSpanValidate

/-- Snapshot copies transport source reads, destination writes and the exact success flag. -/
private theorem Memory.Renamed.spanCopyInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (width : Nat) (tryCopy : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (spanCopyInstruction width tryCopy stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (spanCopyInstruction width tryCopy stack source)
      (spanCopyInstruction width tryCopy (stack.map mapping.value) target) := by
  unfold CIL.Safety.spanCopyInstruction at observable ⊢
  split at observable
  · rename_i destinationView sourceView rest
    simp only [List.map_cons, AllocationRenaming.value]
    dsimp only [AllocationRenaming.spanView]
    simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
    obtain ⟨destinationBound, sourceBound, restBound⟩ := bounds
    apply (related.checkedSpanValidate sourceView sourceBound).bindWithSuccess
    intro first second sourceStep same
    subst second
    apply (related.checkedSpanValidate destinationView destinationBound).bindWithSuccess
    intro first second destinationStep same
    subst second
    cases sourceAddress : sourceView.reference <;>
      cases destinationAddress : destinationView.reference
    all_goals simp only [sourceAddress, destinationAddress, ManagedReference.Below]
      at sourceBound destinationBound
    all_goals cases tryCopy <;>
      simp only [sourceAddress, destinationAddress, AllocationRenaming.managedReference,
        writeIndexed_eq, Bool.false_eq_true, Bool.true_eq, ite_true, ite_false]
    all_goals repeat' first
      | exact .ok ⟨related, rfl⟩
      | exact .error _
      | (apply (related.checkedRead _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep same
         subst second)
      | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
         intro first second sourceStep memoryRelated
         exact .ok ⟨memoryRelated, rfl⟩)
      | (split <;> try simp only [*, Bind.bind, Except.bind])
  · repeat first | contradiction | cases observable | split at observable
#print axioms Memory.Renamed.spanCopyInstructionResult

/-- Repeating snapshot bytes preserves allocation renaming and initialization masks. -/
theorem Memory.Renamed.spanFillSnapshot {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit) (element : List (BitVec 8 × Bool)) :
    ResultEquivalent (Memory.Renamed mapping scopes)
      (view.fillSnapshot source element) ((mapping.spanView view).fillSnapshot target element) := by
  unfold SpanView.fillSnapshot SpanView.fillWith
  rw [related.spanValidate view bound]
  apply ResultEquivalent.bind_same
  intro checked
  dsimp only [AllocationRenaming.spanView]
  repeat' first
    | exact .error _
    | exact .ok related
    | (apply ResultEquivalent.bind_same; intro)
    | (split <;> simp only [*, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Bool.false_eq_true, ite_true, ite_false])
    | (cases reference : view.reference <;>
        simp only [AllocationRenaming.managedReference])
    | exact related.writeSnapshot _
        (by simpa only [*, ManagedReference.Below] using bound) _ _
#print axioms Memory.Renamed.spanFillSnapshot

/-- Fill and clear preserve their exact checked write under allocation renaming. -/
private theorem Memory.Renamed.spanFillInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (width : Nat) (clear : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (spanFillInstruction width clear stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (spanFillInstruction width clear stack source)
      (spanFillInstruction width clear (stack.map mapping.value) target) := by
  cases clear <;> simp only [CIL.Safety.spanFillInstruction] at observable ⊢
  all_goals split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try dsimp only [AllocationRenaming.spanView]
  all_goals try solve | repeat first | contradiction | cases observable | split at observable
  all_goals clear observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | (apply ((related.spanFillSnapshot _ (by assumption) _).checkedAt _ _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
    | exact .error _
    | (apply ((related.spanFill _ (by assumption) _).checkedAt _ _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
    | (split <;> try simp only [*, Bind.bind, Except.bind])
#print axioms Memory.Renamed.spanFillInstructionResult

/-- Array filling transports through the existing slice and fill allocation-renaming rules. -/
private theorem Memory.Renamed.arrayFillInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (element : CIL.ArrayElement) (counted : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (arrayFillInstruction element counted stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (arrayFillInstruction element counted stack source)
      (arrayFillInstruction element counted (stack.map mapping.value) target) := by
  unfold arrayFillInstruction at observable ⊢
  split at observable
  · rename_i value input rest
    simp only [List.map_cons, AllocationRenaming.value, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at observable ⊢
    split at observable
    · rename_i view
      dsimp +instances only [AllocationRenaming.arrayView]
      simp only [mapping.isNull]
      split at observable
      · simp only [*, ite_true]; exact .error _
      · simp only [*, Bool.false_eq_true, ite_false]
        apply (related.checkedSpanValidate view.storage
          (by simpa only [List.mem_cons, forall_eq_or_imp, Value.Below, ArrayView.storage] using
            (bounds (.array view) (by simp)))).bindWithSuccess
        intro checked renamed sourceStep same
        cases checked
        cases renamed
        change checkedAt view.reference 0 (view.validate source) = .ok () at sourceStep
        simp only [sourceStep, Bind.bind, Except.bind] at observable
        split at observable
        · simp only [*, ite_true]; exact .error _
        · simp only [*, Bool.false_eq_true, ite_false]
          have renamed := related.spanFillInstructionResult element.width false
            (.scalar value :: .bufferSpan view.storage :: rest)
            (by simpa only [List.mem_cons, forall_eq_or_imp, Value.Below, ArrayView.storage]
                  using bounds) observable
          simpa only [List.map_cons, AllocationRenaming.value, AllocationRenaming.spanView,
            ArrayView.storage] using renamed
    · simp only [AllocationRenaming.value, AllocationRenaming.managedReference]
      exact .error _
    · cases observable
  · rename_i count start value input rest
    simp only [List.map_cons, AllocationRenaming.value, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at observable ⊢
    split at observable
    · rename_i view
      dsimp +instances only [AllocationRenaming.arrayView]
      simp only [mapping.isNull]
      simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
      split at observable
      · simp only [*, ite_true]; exact .error _
      · simp only [*, Bool.false_eq_true, ite_false]
        apply (related.checkedSpanValidate view.storage bounds.2.2.2.1).bindWithSuccess
        intro checked renamed sourceStep same
        cases checked
        cases renamed
        change checkedAt view.reference 0 (view.validate source) = .ok () at sourceStep
        simp only [sourceStep, Bind.bind, Except.bind] at observable
        split at observable
        · simp only [*, ite_true]; exact .error _
        · simp only [*, Bool.false_eq_true, ite_false]
          split at observable
          · rename_i validRange
            simp only [validRange, ite_true, Bind.bind, Except.bind,
              Pure.pure, Except.pure]
            apply ((related.spanSlice view.storage bounds.2.2.2.1
              start.toNat count.toNat).checkedAt view.reference 0).bindWithSuccess
            intro first second sourceStep same
            subst second
            have slicedBound : first.reference.Below mapping.sourceLimit := by
              rw [related.sourceLimit]
              exact formed.span_below first (checkedSpanSlice_valid _ _ _ _ _ sourceStep)
            have renamed := related.spanFillInstructionResult element.width false
              (.scalar value :: .bufferSpan first :: rest)
              (by simpa only [List.mem_cons, forall_eq_or_imp, Value.Below]
                    using And.intro trivial (And.intro slicedBound bounds.2.2.2.2))
              (by simpa only [sourceStep, Bind.bind, Except.bind] using observable)
            simpa only [List.map_cons, AllocationRenaming.value] using renamed
          · rename_i invalidRange
            simp only [invalidRange, ite_false, Bind.bind, Except.bind]
            exact .error _
    · simp only [AllocationRenaming.value, AllocationRenaming.managedReference]
      exact .error _
    · cases observable
  · simp only [Bind.bind, Except.bind] at observable
    cases observable
#print axioms Memory.Renamed.arrayFillInstructionResult

/-- Typed array loads and stores transport the exact snapshot mask and checked authority. -/
private theorem Memory.Renamed.arrayTransferInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (element : CIL.ArrayElement) (store : Bool) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (arrayTransferInstruction element store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (arrayTransferInstruction element store stack source)
      (arrayTransferInstruction element store (stack.map mapping.value) target) := by
  cases store <;> simp only [arrayTransferInstruction, Bool.false_eq_true, ite_false, ite_true]
    at observable ⊢
  all_goals simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at observable ⊢
  all_goals split at observable
  all_goals repeat' first
    | contradiction
    | cases observable
    | exact .error _
    | exact .ok ⟨by assumption, rfl⟩
    | (try simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
       rcases bounds with ⟨_, bounds⟩)
    | (apply (related.arrayElement _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       have addressBound : first.allocation < mapping.sourceLimit := by
         rw [related.sourceLimit]
         exact (checkedArrayElement_valid _ _ _ _ _ sourceStep).below formed
       subst second)
    | (apply (related.loadTransfer _ (by assumption) _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.storeTransfer _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep memoryRelated)
    | (split at observable <;> try simp only [*, List.map_cons, AllocationRenaming.value,
        AllocationRenaming.arrayView, AllocationRenaming.managedReference,
        Bool.false_eq_true, ite_false, ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure]
        at observable ⊢)
#print axioms Memory.Renamed.arrayTransferInstructionResult
/-- Checked reference addition transports either operand order to the same allocation. -/
private theorem Memory.Renamed.referenceAddInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (size : Nat) (signed : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (referenceAddInstruction size signed stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (referenceAddInstruction size signed stack source)
      (referenceAddInstruction size signed (stack.map mapping.value) target) := by
  unfold CIL.Safety.referenceAddInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try solve | cases observable
  all_goals clear observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨related, rfl⟩
    | (apply (mapping.referenceAt _).bindWithSuccess
       intro first second sourceStep same
       have addressBound := referenceAt_below (by assumption) sourceStep
       subst second)
    | (apply (related.checkedAdd _ (by assumption) _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (split <;> try simp only [*, Bind.bind, Except.bind])
#print axioms Memory.Renamed.referenceAddInstructionResult

/-- Ordinary memory effects transport independently of the whole-span dispatch families. -/
private theorem Memory.Renamed.otherMemoryInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.MemoryOp)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (otherMemoryInstruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (otherMemoryInstruction operation stack source)
      (otherMemoryInstruction operation (stack.map mapping.value) target) := by
  unfold otherMemoryInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try dsimp +instances only [AllocationRenaming.arrayView, AllocationRenaming.spanView]
  all_goals try solve | repeat first | contradiction | cases observable | split at observable
  all_goals clear observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals have imageEquality : ∀ left right, left < mapping.sourceLimit →
      right < mapping.sourceLimit → (mapping.image left = mapping.image right ↔ left = right) :=
    fun left right leftBound rightBound =>
      ⟨mapping.injective left right leftBound rightBound, congrArg mapping.image⟩
  all_goals try solve
    | apply (related.checkedSpanValidate _ (by first | assumption | trivial)).bindWithSuccess
      intro first second sourceStep same
      subst second
      repeat first
        | exact .ok ⟨by assumption, rfl⟩
        | exact .error _
        | (apply (related.loadTransfer _ (by assumption) _).bindWithSuccess
           intro first second sourceStep same
           subst second)
        | (apply (related.storeTransfer _ (by assumption) _ _).bindWithSuccess
           intro first second sourceStep memoryRelated)
        | (split <;> try simp only [*, AllocationRenaming.managedReference, Bind.bind, Except.bind])
  all_goals repeat first
    | exact .ok ⟨related, rfl⟩
    | exact .error _
    | (apply ((related.spanFill _ (by assumption) _).checkedAt _ _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
    | (apply (related.referenceDifference _ _ (by assumption) (by assumption)).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply (related.formValue _ (by assumption)).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply (related.storeValue _ (by assumption) _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
    | (apply (related.loadValue _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply (mapping.bitcastValue _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply ((related.spanSlice _ (by assumption) _ _).checkedAt _ _).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply ((related.spanElement _ (by assumption) _).checkedAt _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (mapping.referenceAt _).bindWithSuccess
       intro first second sourceStep same
       have addressBound := referenceAt_below (by assumption) sourceStep
       subst second)
    | (apply (related.checkedAdd _ (by assumption) _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second
       exact .ok ⟨related, rfl⟩)
    | (apply (related.checkedRead _ (by assumption) _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.checkedAccess _ (by assumption) _ _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.checkedWrite _ (by assumption) _ _ _ _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
    | (apply (related.checkedSpan _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.checkedArray _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.arrayElement _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       have addressBound : first.allocation < mapping.sourceLimit := by
         rw [related.sourceLimit]
         exact (checkedArrayElement_valid _ _ _ _ _ sourceStep).below formed
       subst second)
    | dsimp +instances only [AllocationRenaming.reference]
    | simp only [mapping.isNull, imageEquality]
    | (split <;> try simp only [*, mapping.isNull, AllocationRenaming.managedReference,
        Bind.bind, Except.bind])
#print axioms Memory.Renamed.otherMemoryInstructionResult

/-- View observations preserve reference provenance under allocation renaming. -/
private theorem Memory.Renamed.viewObservationInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (observation : CIL.ViewObservation)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (viewObservationInstruction observation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (viewObservationInstruction observation stack source)
      (viewObservationInstruction observation (stack.map mapping.value) target) := by
  unfold viewObservationInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try dsimp only [AllocationRenaming.arrayView, AllocationRenaming.spanView]
  all_goals try solve | repeat first | contradiction | cases observable | split at observable
  all_goals clear observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .ok ⟨related, rfl⟩
    | exact .error _
    | (apply (related.checkedSpanValidate _ (by assumption)).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.checkedArray _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.formValue _ (by first | assumption | trivial)).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | simp only [mapping.isNull]
    | (split <;> try simp only [*, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
        AllocationRenaming.managedReference, Bind.bind, Except.bind])
  all_goals try simp_all [CIL.Safety.formValue, Pure.pure, Except.pure, Bind.bind, Except.bind]
  all_goals subst_vars
  all_goals try solve | split <;> exact .ok ⟨related, rfl⟩
  all_goals
    apply (related.formValue _ (by assumption)).bindWithSuccess
    intro first second sourceStep same
    subst second
    split <;> exact .ok ⟨related, rfl⟩
#print axioms Memory.Renamed.viewObservationInstructionResult

/-- Byte reordering cannot introduce a fault containing allocation identities. -/
private theorem AllocationRenaming.endianValue (mapping : AllocationRenaming)
    (width : Nat) (signed bigEndian : Bool) (value : CIL.Value) :
    ResultRenamed mapping Eq (endianValue width signed bigEndian value)
      (endianValue width signed bigEndian value) := by
  unfold CIL.Safety.endianValue
  split <;> first | exact .ok rfl | exact .error _
#print axioms AllocationRenaming.endianValue

/-- Fixed-width endian transfers preserve checked reads and writes under allocation renaming. -/
private theorem Memory.Renamed.binaryTransferInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (width : Nat) (signed bigEndian read trying : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow
      (binaryTransferInstruction width signed bigEndian read trying stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (binaryTransferInstruction width signed bigEndian read trying stack source)
      (binaryTransferInstruction width signed bigEndian read trying (stack.map mapping.value) target) := by
  unfold binaryTransferInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try dsimp only [AllocationRenaming.spanView]
  all_goals try solve | repeat first | contradiction | cases observable | split at observable
  all_goals clear observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .ok ⟨by assumption, rfl⟩
    | exact .error _
    | (apply (related.checkedSpanValidate _ (by assumption)).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.loadTransfer _ (by assumption) _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.storeTransfer _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep memoryRelated)
    | (apply (mapping.endianValue _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (split <;> try simp only [*, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
        AllocationRenaming.managedReference, Bind.bind, Except.bind])
#print axioms Memory.Renamed.binaryTransferInstructionResult

/-- A single-reference view preserves its allocation identity under renaming. -/
private theorem Memory.Renamed.singleSpanInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (width : Nat) (writable : Bool)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (singleSpanInstruction width writable stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (singleSpanInstruction width writable stack source)
      (singleSpanInstruction width writable (stack.map mapping.value) target) := by
  unfold singleSpanInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .ok ⟨related, rfl⟩
    | exact .error _
    | (apply (related.checkedSpanValidate _ (by assumption) width).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (split <;> try simp only [*, Bind.bind, Except.bind])
  all_goals repeat first | contradiction | cases observable | split at observable
#print axioms Memory.Renamed.singleSpanInstructionResult

/-- Aligned pointer transfers preserve allocation-relative accesses and typed values. -/
private theorem Memory.Renamed.pointerTransferInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (kind : CIL.TransferKind)
    (alignment : Nat) (store : Bool) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (pointerTransferInstruction kind alignment store stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (pointerTransferInstruction kind alignment store stack source)
      (pointerTransferInstruction kind alignment store (stack.map mapping.value) target) := by
  unfold pointerTransferInstruction at observable ⊢
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value]
  all_goals try solve | repeat first | contradiction | cases observable | split at observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .ok ⟨related, rfl⟩
    | exact .error _
    | (apply (mapping.referenceAt _).bindWithSuccess
       intro first second sourceStep same
       have addressBound := referenceAt_below (by assumption) sourceStep
       subst second)
    | (apply (related.checkedAccess _ (by assumption) _ _ _ _ _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.loadTransfer _ (by assumption) _).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | (apply (related.storeTransfer _ (by assumption) _ _).bindWithSuccess
       intro first second sourceStep memoryRelated
       exact .ok ⟨memoryRelated, rfl⟩)
#print axioms Memory.Renamed.pointerTransferInstructionResult

/-- A memory instruction's successful effect is preserved on the corresponding allocations. -/
theorem Memory.Renamed.memoryInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (operation : CIL.MemoryOp)
    (formed : source.WellFormed)
    (stack : List Value) (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (memoryInstruction operation stack source)) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = left.2.map mapping.value)
      (memoryInstruction operation stack source)
      (memoryInstruction operation (stack.map mapping.value) target) := by
  unfold CIL.Safety.memoryInstruction at observable ⊢
  rw [mapping.unspecifiedOperands]
  split at observable
  · cases observable
  · rename_i observed
    simp only [observed, Bool.false_eq_true, ite_false]
    split at observable
    · exact related.referenceAddInstructionResult _ _ _ bounds observable
    · exact related.pointerTransferInstructionResult _ _ _ _ bounds observable
    · exact related.arrayTransferInstructionResult formed _ _ _ bounds observable
    · exact related.binaryTransferInstructionResult _ _ _ _ _ _ bounds observable
    · exact related.binaryTransferInstructionResult _ _ _ _ _ _ bounds observable
    · exact related.singleSpanInstructionResult _ _ _ bounds observable
    · exact related.viewObservationInstructionResult _ _ bounds observable
    · exact related.spanCopyInstructionResult _ _ _ bounds observable
    · exact related.spanFillInstructionResult _ _ _ bounds observable
    · exact related.arrayFillInstructionResult formed _ _ _ bounds observable
    · exact related.otherMemoryInstructionResult _ formed _ bounds observable

#print axioms Memory.Renamed.memoryInstructionResult

end CIL.Safety
