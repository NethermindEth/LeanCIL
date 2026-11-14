import CIL.Safety.Execution

/-!
# Steps under trailing local slots

Each instruction preserves successful and throwing outcomes when unused slots are appended
to the frame. The per-operation proofs keep constructor checking independent of the dispatcher.
-/

namespace CIL.Safety

open CIL

/-- `frame` with the slots `extra` placed after its locals. -/
def Frame.appendLocals (frame : Frame) (extra : List LocalSlot) : Frame :=
  { frame with locals := frame.locals ++ extra }

/-- Padding with no slots leaves a frame unchanged. -/
@[simp] theorem Frame.appendLocals_nil (frame : Frame) : frame.appendLocals [] = frame := by
  simp [Frame.appendLocals]

#print axioms CIL.Safety.Frame.appendLocals_nil

/-- The action with `extra` slots after the locals of the frame it resumes in. -/
def FrameAction.appendLocals (extra : List LocalSlot) : FrameAction → FrameAction
  | .next target stack frame memory => .next target stack (frame.appendLocals extra) memory
  | .construct callee args rest frame temporary kind memory =>
    .construct callee args rest (frame.appendLocals extra) temporary kind memory
  | action => action

/-- A step outcome the padded simulation carries: a success or a thrown exception. -/
def StepKept : ExecutionResult α → Prop
  | .ok _ => True
  | .error fault => ∃ exception, fault = .thrown exception

/-- A local present in `frame` is the same slot after padding. -/
theorem Frame.appendLocals_getElem? {frame : Frame} {extra : List LocalSlot} {index : Nat}
    {slot : LocalSlot} (found : frame.locals[index]? = some slot) :
    (frame.appendLocals extra).locals[index]? = some slot := by
  simp only [Frame.appendLocals]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

#print axioms CIL.Safety.Frame.appendLocals_getElem?

/-- Storing to a local present in `frame` commutes with padding. -/
theorem Frame.appendLocals_set {frame : Frame} {extra : List LocalSlot} {index : Nat}
    {slot old : LocalSlot} (found : frame.locals[index]? = some old) :
    { frame.appendLocals extra with
        locals := (frame.appendLocals extra).locals.set index slot } =
      { frame with locals := frame.locals.set index slot }.appendLocals extra := by
  simp only [Frame.appendLocals]
  rw [List.set_append_left _ _ (List.getElem?_eq_some_iff.mp found).1]

#print axioms CIL.Safety.Frame.appendLocals_set

/-- A dynamic stack allocation reads only the frame's activation and reserved bytes, so it
    does the same in a padded frame and returns that frame padded. -/
theorem allocateStack_appendLocals (memory : Memory) (frame : Frame) (extra : List LocalSlot)
    (size : Nat) (initLocals : Bool) :
    allocateStack memory (frame.appendLocals extra) size initLocals =
      (fun allocated => (allocated.1, allocated.2.1.appendLocals extra, allocated.2.2)) <$>
        allocateStack memory frame size initLocals := by
  unfold allocateStack
  simp only [Frame.appendLocals]
  by_cases limit : (size ≥ nativeLimit || memory.stackLimit > maxDynamicStack) = true
  · simp [limit, Bind.bind, Except.bind, Functor.map, Except.map]
  by_cases empty : (size == 0) = true
  · simp [limit, empty, Functor.map, Except.map, Pure.pure, Except.pure]
  by_cases full : (frame.stackBytes > memory.stackLimit ||
      stackReservation size > memory.stackLimit - frame.stackBytes) = true
  · simp [limit, empty, full, Bind.bind, Except.bind, Functor.map, Except.map]
  cases allocateHome memory frame.activation size stackAlignment <;>
    cases initLocals <;>
    simp [limit, empty, full, Bind.bind, Except.bind, Functor.map, Except.map, Pure.pure,
      Except.pure] <;> split <;> simp_all

#print axioms allocateStack_appendLocals

/-- Closes `step` on a padded frame against the unpadded step mapped through the padding.
    Shared binds are normalized before splitting results; a missing unpadded local still fails. -/
local macro "frame_natural" : tactic => `(tactic| (
  simp only [map_bind, map_pure, FrameAction.appendLocals, Frame.appendLocals]
  repeat' first
  | rfl
  | contradiction
  | (simp only [map_bind, map_pure, FrameAction.appendLocals, Frame.appendLocals]; done)
  | (apply bind_congr; intro)
  | split
  | simp only [map_bind]))

/-- The shared dispatcher tail carries the frame unchanged through pure and memory operations. -/
theorem fallback_appendLocals (profile : FeatureProfile) (op : Instruction) (pc : Nat)
    (stack : List Value) (frame : Frame) (extra : List LocalSlot) (memory : Memory) :
    (match pureArity op with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState else do
        let values ← scalars (stack.take argc)
        let some (.next target result _) :=
          CIL.step op false pc [] values (fun _ => none) profile |
            Except.error ExecutionFault.invalidState
        let result ← (result.map Value.scalar).mapM (checkedValue memory)
        pure (FrameAction.next target (result ++ stack.drop argc) (frame.appendLocals extra) memory)
    | none => do
      let (memory, values) ← instruction op stack memory
      pure (FrameAction.next (pc + 1) values (frame.appendLocals extra) memory)) =
    FrameAction.appendLocals extra <$>
      (match pureArity op with
      | some argc =>
        if stack.length < argc then Except.error ExecutionFault.invalidState else do
          let values ← scalars (stack.take argc)
          let some (.next target result _) :=
            CIL.step op false pc [] values (fun _ => none) profile |
            Except.error ExecutionFault.invalidState
          let result ← (result.map Value.scalar).mapM (checkedValue memory)
          pure (FrameAction.next target (result ++ stack.drop argc) frame memory)
      | none => do
        let (memory, values) ← instruction op stack memory
        pure (FrameAction.next (pc + 1) values frame memory)) := by
  frame_natural

#print axioms fallback_appendLocals

/-- The unspecified-bits guard preserves any frame-padding equation. -/
theorem observed_appendLocals (observed : Bool) (extra : List LocalSlot)
    (padded original : ExecutionResult FrameAction)
    (same : padded = FrameAction.appendLocals extra <$> original) :
    (if observed then .error (.unsupported "Instruction observes unspecified vector bits")
      else padded) = FrameAction.appendLocals extra <$>
      (if observed then .error (.unsupported "Instruction observes unspecified vector bits")
        else original) := by
  cases observed <;> simp [same, Functor.map, Except.map]

#print axioms observed_appendLocals
/-- An instruction preserves successful and throwing steps under trailing local slots. -/
def StepAppendLocals (op : Instruction) : Prop :=
  ∀ (body : Method) (pc : Nat) (args : List Value) (frame : Frame)
    (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction),
    step body op pc args frame stack memory = outcome → StepKept outcome →
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome

set_option hygiene false in
/-- Closes dispatcher-tail cases before splitting an irrelevant second operand. -/
local macro "append_stack_cases" " using " fallback:term : tactic => `(tactic| (
  rcases stack with _ | ⟨first, rest⟩ <;> (try cases first)
  all_goals first
    | exact $fallback
    | (rcases rest with _ | ⟨second, rest⟩ <;> (try cases second)
       all_goals first | exact $fallback | frame_natural)))

/-- `nativeBinary` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_nativeBinary (operation : Instruction) :
    StepAppendLocals (.nativeBinary operation) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.nativeBinary operation) pc _ frame extra memory

#print axioms step_appendLocals_nativeBinary

set_option hygiene false in
/-- Proves `StepAppendLocals op` for one faulting arithmetic constructor `op`; the fallback
    names `op`, since inferring it from the dispatcher does not terminate in budget. -/
local macro "faulting_appendLocals " op:term : tactic => `(tactic| (
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile $op pc _ frame extra memory))

/-- Division, remainder and overflow-checked arithmetic preserve outcomes under trailing local
    slots. -/
theorem step_appendLocals_faulting (op : Instruction)
    (faulting : op.divideKind?.isSome || op.checkedKind?.isSome) : StepAppendLocals op := by
  cases op <;> simp only [Instruction.divideKind?, Instruction.checkedKind?, Option.isSome_none,
    Option.isSome_some, Bool.or_false, Bool.false_or, Bool.false_eq_true] at faulting
  case div => faulting_appendLocals .div
  case div_un => faulting_appendLocals .div_un
  case rem => faulting_appendLocals .rem
  case rem_un => faulting_appendLocals .rem_un
  case add_ovf => faulting_appendLocals .add_ovf
  case add_ovf_un => faulting_appendLocals .add_ovf_un
  case sub_ovf => faulting_appendLocals .sub_ovf
  case sub_ovf_un => faulting_appendLocals .sub_ovf_un
  case mul_ovf => faulting_appendLocals .mul_ovf
  case mul_ovf_un => faulting_appendLocals .mul_ovf_un

#print axioms step_appendLocals_faulting

/-- `conv_ovf` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_ovf (target : ConvTarget) :
    StepAppendLocals (.conv_ovf target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.conv_ovf target) pc _ frame extra memory

#print axioms step_appendLocals_conv_ovf

/-- `conv_ovf_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_ovf_un (target : ConvTarget) :
    StepAppendLocals (.conv_ovf_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.conv_ovf_un target) pc _ frame extra memory

#print axioms step_appendLocals_conv_ovf_un

/-- `stackAlloc` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stackAlloc (initLocals : Bool) :
    StepAppendLocals (.stackAlloc initLocals) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, allocateStack_appendLocals, bind_map_left]
  frame_natural

#print axioms step_appendLocals_stackAlloc

/-- Heap array allocation does not inspect or change a frame's local slots. -/
theorem step_appendLocals_newArray (element : CIL.ArrayElement) :
    StepAppendLocals (.newArray element) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, bind_map_left]
  frame_natural

#print axioms step_appendLocals_newArray

/-- Reference array allocation does not inspect or change a frame's local slots. -/
theorem step_appendLocals_newReferenceArray (element : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.newReferenceArray element) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, bind_map_left]
  frame_natural

#print axioms step_appendLocals_newReferenceArray

/-- `nop` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_nop :
    StepAppendLocals .nop := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .nop pc stack frame extra memory

#print axioms step_appendLocals_nop

/-- `neg` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_neg :
    StepAppendLocals .neg := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .neg pc stack frame extra memory

#print axioms step_appendLocals_neg

/-- `cgt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_cgt :
    StepAppendLocals .cgt := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .cgt pc stack frame extra memory

#print axioms step_appendLocals_cgt

/-- `bgt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bgt (target : Nat) :
    StepAppendLocals (.bgt target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.bgt target) pc stack frame extra memory

#print axioms step_appendLocals_bgt

/-- `ble` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ble (target : Nat) :
    StepAppendLocals (.ble target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.ble target) pc stack frame extra memory

#print axioms step_appendLocals_ble

/-- `ble_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ble_un (target : Nat) :
    StepAppendLocals (.ble_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.ble_un target) pc _ frame extra memory

#print axioms step_appendLocals_ble_un

/-- `loadAggregate` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_loadAggregate (size : Nat) :
    StepAppendLocals (.loadAggregate size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.loadAggregate size) pc stack frame extra memory

#print axioms step_appendLocals_loadAggregate

/-- `copyObject` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_copyObject (size : Nat) :
    StepAppendLocals (.copyObject size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.copyObject size) pc stack frame extra memory

#print axioms step_appendLocals_copyObject

/-- `storeAggregate` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_storeAggregate (size : Nat) :
    StepAppendLocals (.storeAggregate size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.storeAggregate size) pc stack frame extra memory

#print axioms step_appendLocals_storeAggregate

/-- `initAggregate` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_initAggregate (size : Nat) :
    StepAppendLocals (.initAggregate size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.initAggregate size) pc stack frame extra memory

#print axioms step_appendLocals_initAggregate

/-- `loadScalar` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_loadScalar (width : Nat) (signed : Bool) :
    StepAppendLocals (.loadScalar width signed) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.loadScalar width signed) pc stack frame extra memory

#print axioms step_appendLocals_loadScalar

/-- `storeScalar` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_storeScalar (width : Nat) :
    StepAppendLocals (.storeScalar width) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.storeScalar width) pc stack frame extra memory

#print axioms step_appendLocals_storeScalar

/-- `fieldAt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_fieldAt (offset width : Nat) (signed : Bool) :
    StepAppendLocals (.fieldAt offset width signed) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.fieldAt offset width signed)
    pc stack frame extra memory

#print axioms step_appendLocals_fieldAt

/-- `fieldAddress` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_fieldAddress (offset : Nat) :
    StepAppendLocals (.fieldAddress offset) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.fieldAddress offset) pc stack frame extra memory

#print axioms step_appendLocals_fieldAddress

/-- `setFieldAt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_setFieldAt (offset width : Nat) :
    StepAppendLocals (.setFieldAt offset width) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.setFieldAt offset width) pc stack frame extra memory

#print axioms step_appendLocals_setFieldAt

/-- `aggregateFieldAt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_aggregateFieldAt (offset size : Nat) :
    StepAppendLocals (.aggregateFieldAt offset size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.aggregateFieldAt offset size)
    pc stack frame extra memory

#print axioms step_appendLocals_aggregateFieldAt

/-- `setAggregateFieldAt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_setAggregateFieldAt (offset size : Nat) :
    StepAppendLocals (.setAggregateFieldAt offset size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.setAggregateFieldAt offset size)
    pc stack frame extra memory

#print axioms step_appendLocals_setAggregateFieldAt

/-- `arg` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_arg (index : Nat) (narrow : Option NarrowKind) :
    StepAppendLocals (.arg index narrow) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_arg

/-- `local` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_local (index : Nat) : StepAppendLocals (.local index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  cases found : frame.locals[index]? with
  | some slot =>
    cases stack <;>
      simp only [step, found, Frame.appendLocals_getElem? found] <;>
      frame_natural
  | none =>
    revert kept
    cases stack <;> simp only [step, found] <;> repeat' split
    all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)

#print axioms step_appendLocals_local

/-- `localAddr` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_localAddr (index : Nat) :
    StepAppendLocals (.localAddr index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  cases found : frame.locals[index]? with
  | some slot =>
    cases stack <;>
      simp only [step, found, Frame.appendLocals_getElem? found] <;>
      frame_natural
  | none =>
    revert kept
    cases stack <;> simp only [step, found] <;> repeat' split
    all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)

#print axioms step_appendLocals_localAddr

/-- `setLocal` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_setLocal (index : Nat) : StepAppendLocals (.setLocal index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  cases found : frame.locals[index]? with
  | some slot =>
    cases stack <;>
      simp only [step, found, Frame.appendLocals_getElem? found,
        Frame.appendLocals_set found] <;>
      frame_natural
  | none =>
    revert kept
    cases stack <;> simp only [step, found] <;> repeat' split
    all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)

#print axioms step_appendLocals_setLocal

/-- Span construction updates only its existing typed local slot. -/
theorem step_appendLocals_initializeSpanLocal (index : Nat) (constructor : CIL.SpanConstructor) :
    StepAppendLocals (.initializeSpanLocal index constructor) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  cases found : frame.locals[index]? with
  | some slot =>
    simp only [step, found, Frame.appendLocals_getElem? found, Frame.appendLocals_set found]
    frame_natural
  | none =>
    revert kept
    simp only [step, found]
    repeat' split
    all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)

#print axioms step_appendLocals_initializeSpanLocal

/-- `ldc_i4` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldc_i4 (value : W32) :
    StepAppendLocals (.ldc_i4 value) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.ldc_i4 value) pc stack frame extra memory

#print axioms step_appendLocals_ldc_i4

/-- `ldc_i8` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldc_i8 (value : W64) :
    StepAppendLocals (.ldc_i8 value) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.ldc_i8 value) pc stack frame extra memory

#print axioms step_appendLocals_ldc_i8

/-- `conv_i1` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_i1 :
    StepAppendLocals .conv_i1 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_i1 pc stack frame extra memory

#print axioms step_appendLocals_conv_i1

/-- `conv_i2` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_i2 :
    StepAppendLocals .conv_i2 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_i2 pc stack frame extra memory

#print axioms step_appendLocals_conv_i2

/-- `conv_u2` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_u2 :
    StepAppendLocals .conv_u2 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_u2 pc stack frame extra memory

#print axioms step_appendLocals_conv_u2

/-- `conv_i8` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_i8 :
    StepAppendLocals .conv_i8 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_i8 pc stack frame extra memory

#print axioms step_appendLocals_conv_i8

/-- `conv_i4` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_i4 :
    StepAppendLocals .conv_i4 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_i4 pc stack frame extra memory

#print axioms step_appendLocals_conv_i4

/-- `conv_u1` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_u1 :
    StepAppendLocals .conv_u1 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_u1 pc stack frame extra memory

#print axioms step_appendLocals_conv_u1

/-- `conv_u4` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_u4 :
    StepAppendLocals .conv_u4 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_u4 pc stack frame extra memory

#print axioms step_appendLocals_conv_u4

/-- `conv_u8` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_u8 :
    StepAppendLocals .conv_u8 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_u8 pc stack frame extra memory

#print axioms step_appendLocals_conv_u8

/-- `conv_u` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_u :
    StepAppendLocals .conv_u := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_u pc stack frame extra memory

#print axioms step_appendLocals_conv_u

/-- `conv_i` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_conv_i :
    StepAppendLocals .conv_i := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .conv_i pc stack frame extra memory

#print axioms step_appendLocals_conv_i

/-- `not` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_not :
    StepAppendLocals .not := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .not pc stack frame extra memory

#print axioms step_appendLocals_not

/-- `add` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_add :
    StepAppendLocals .add := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .add pc stack frame extra memory

#print axioms step_appendLocals_add

/-- `sub` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_sub :
    StepAppendLocals .sub := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile .sub pc _ frame extra memory

#print axioms step_appendLocals_sub

/-- `mul` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_mul :
    StepAppendLocals .mul := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .mul pc stack frame extra memory

#print axioms step_appendLocals_mul

/-- `and` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_and :
    StepAppendLocals .and := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .and pc stack frame extra memory

#print axioms step_appendLocals_and

/-- `or` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_or :
    StepAppendLocals .or := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .or pc stack frame extra memory

#print axioms step_appendLocals_or

/-- `xor` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_xor :
    StepAppendLocals .xor := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .xor pc stack frame extra memory

#print axioms step_appendLocals_xor

/-- `shl` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_shl :
    StepAppendLocals .shl := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .shl pc stack frame extra memory

#print axioms step_appendLocals_shl

/-- `shr` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_shr :
    StepAppendLocals .shr := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .shr pc stack frame extra memory

#print axioms step_appendLocals_shr

/-- `shr_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_shr_un :
    StepAppendLocals .shr_un := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .shr_un pc stack frame extra memory

#print axioms step_appendLocals_shr_un

/-- `clt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_clt :
    StepAppendLocals .clt := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .clt pc stack frame extra memory

#print axioms step_appendLocals_clt

/-- `clt_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_clt_un :
    StepAppendLocals .clt_un := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile .clt_un pc _ frame extra memory

#print axioms step_appendLocals_clt_un

/-- `cgt_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_cgt_un :
    StepAppendLocals .cgt_un := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile .cgt_un pc _ frame extra memory

#print axioms step_appendLocals_cgt_un

/-- `ceq` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ceq :
    StepAppendLocals .ceq := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile .ceq pc _ frame extra memory

#print axioms step_appendLocals_ceq

/-- `load64` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_load64 :
    StepAppendLocals .load64 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .load64 pc stack frame extra memory

#print axioms step_appendLocals_load64

/-- `store64` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_store64 :
    StepAppendLocals .store64 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .store64 pc stack frame extra memory

#print axioms step_appendLocals_store64

/-- `dup` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_dup :
    StepAppendLocals .dup := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .dup pc stack frame extra memory

#print axioms step_appendLocals_dup

/-- `pop` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_pop :
    StepAppendLocals .pop := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .pop pc stack frame extra memory

#print axioms step_appendLocals_pop

/-- `br` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_br (target : Nat) :
    StepAppendLocals (.br target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.br target) pc stack frame extra memory

#print axioms step_appendLocals_br

/-- `switch` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_switch (targets : List Nat) :
    StepAppendLocals (.switch targets) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.switch targets) pc stack frame extra memory

#print axioms step_appendLocals_switch

/-- `brfalse` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_brfalse (target : Nat) :
    StepAppendLocals (.brfalse target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.brfalse target) pc _ frame extra memory

#print axioms step_appendLocals_brfalse

/-- `brtrue` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_brtrue (target : Nat) :
    StepAppendLocals (.brtrue target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.brtrue target) pc _ frame extra memory

#print axioms step_appendLocals_brtrue

/-- `objectTest` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_objectTest (type : CIL.Extraction.TypeExpr) (throwing : Bool) :
    StepAppendLocals (.objectTest type throwing) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.objectTest type throwing) pc _ frame extra memory

#print axioms step_appendLocals_objectTest

/-- `blt_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_blt_un (target : Nat) :
    StepAppendLocals (.blt_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.blt_un target) pc _ frame extra memory

#print axioms step_appendLocals_blt_un

/-- `bge_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bge_un (target : Nat) :
    StepAppendLocals (.bge_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.bge_un target) pc _ frame extra memory

#print axioms step_appendLocals_bge_un

/-- `bgt_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bgt_un (target : Nat) :
    StepAppendLocals (.bgt_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.bgt_un target) pc _ frame extra memory

#print axioms step_appendLocals_bgt_un

/-- `bge` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bge (target : Nat) :
    StepAppendLocals (.bge target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.bge target) pc stack frame extra memory

#print axioms step_appendLocals_bge

/-- `blt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_blt (target : Nat) :
    StepAppendLocals (.blt target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.blt target) pc stack frame extra memory

#print axioms step_appendLocals_blt

/-- `beq` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_beq (target : Nat) :
    StepAppendLocals (.beq target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.beq target) pc _ frame extra memory

#print axioms step_appendLocals_beq

/-- `bne_un` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bne_un (target : Nat) :
    StepAppendLocals (.bne_un target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.bne_un target) pc _ frame extra memory

#print axioms step_appendLocals_bne_un

/-- `call` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_call (method : Nat) (argc : Nat) :
    StepAppendLocals (.call method argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_call

/-- `callInstance` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_callInstance (method : Nat) (argc : Nat) :
    StepAppendLocals (.callInstance method argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_callInstance

/-- `callVirtual` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_callVirtual (targets : List (CIL.Extraction.TypeExpr × Nat))
    (argc : Nat) : StepAppendLocals (.callVirtual targets argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_callVirtual

/-- `tailCall` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_tailCall (method : Nat) (argc : Nat) :
    StepAppendLocals (.tailCall method argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_tailCall

/-- `newAggregate` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_newAggregate (constructor : Nat) (argc : Nat) (size : Fin (2^64)) :
    StepAppendLocals (.newAggregate constructor argc size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_newAggregate

/-- `newObject` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_newObject (constructor argc : Nat) (owner : Extraction.TypeExpr)
    (bases : List Extraction.TypeExpr) (size : Nat) :
    StepAppendLocals (.newObject constructor argc owner bases size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_newObject

/-- `skipInit` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_skipInit :
    StepAppendLocals .skipInit := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .skipInit pc stack frame extra memory

#print axioms step_appendLocals_skipInit

/-- `feature` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_feature (id : Feature) :
    StepAppendLocals (.feature id) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.feature id) pc stack frame extra memory

#print axioms step_appendLocals_feature

/-- `intrinsic` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_intrinsic (operation : Intrinsic) (argc : Nat) :
    StepAppendLocals (.intrinsic operation argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_intrinsic

/-- `memory` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_memory (operation : MemoryOp) :
    StepAppendLocals (.memory operation) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_memory

/-- `ret` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ret (narrow : Option NarrowKind) :
    StepAppendLocals (.ret narrow) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_ret

/-- `throw` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_throw (exception : String) :
    StepAppendLocals (.throw exception) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_throw

/-- `unsupported` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_unsupported (description : String) :
    StepAppendLocals (.unsupported description) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_unsupported

/-- Managed pointers and tables never inspect the unused trailing frame slots. -/
theorem step_appendLocals_managed (operation : ManagedOp) :
    StepAppendLocals (.managed operation) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  unfold managedStep
  split
  all_goals repeat' first
    | rfl
    | contradiction
    | (simp only [map_bind, map_pure, FrameAction.appendLocals, Frame.appendLocals]; done)
    | (apply bind_congr; intro)
    | split
    | simp only [map_bind]
#print axioms step_appendLocals_managed

/-- Every instruction preserves successful and throwing steps under trailing local slots. -/
theorem step_appendLocals (body : Method) (op : Instruction) (pc : Nat) (args : List Value)
    (frame : Frame) (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction)
    (stepped : step body op pc args frame stack memory = outcome) (kept : StepKept outcome) :
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome := by
  have padded : StepAppendLocals op := by
    cases op
    case managed operation => exact step_appendLocals_managed operation
    case nativeBinary operation =>
      exact step_appendLocals_nativeBinary operation
    case div | div_un | rem | rem_un | add_ovf | add_ovf_un | sub_ovf | sub_ovf_un | mul_ovf
      | mul_ovf_un => exact step_appendLocals_faulting _ rfl
    case conv_ovf target =>
      exact step_appendLocals_conv_ovf target
    case conv_ovf_un target =>
      exact step_appendLocals_conv_ovf_un target
    case stackAlloc initLocals =>
      exact step_appendLocals_stackAlloc initLocals
    case newArray element => exact step_appendLocals_newArray element
    case newReferenceArray element => exact step_appendLocals_newReferenceArray element
    case nop =>
      exact step_appendLocals_nop
    case neg =>
      exact step_appendLocals_neg
    case cgt =>
      exact step_appendLocals_cgt
    case bgt target =>
      exact step_appendLocals_bgt target
    case ble target =>
      exact step_appendLocals_ble target
    case ble_un target =>
      exact step_appendLocals_ble_un target
    case loadAggregate size =>
      exact step_appendLocals_loadAggregate size
    case copyObject size =>
      exact step_appendLocals_copyObject size
    case storeAggregate size =>
      exact step_appendLocals_storeAggregate size
    case initAggregate size =>
      exact step_appendLocals_initAggregate size
    case loadScalar width signed =>
      exact step_appendLocals_loadScalar width signed
    case storeScalar width =>
      exact step_appendLocals_storeScalar width
    case fieldAt offset width signed =>
      exact step_appendLocals_fieldAt offset width signed
    case fieldAddress offset =>
      exact step_appendLocals_fieldAddress offset
    case setFieldAt offset width =>
      exact step_appendLocals_setFieldAt offset width
    case aggregateFieldAt offset size =>
      exact step_appendLocals_aggregateFieldAt offset size
    case setAggregateFieldAt offset size =>
      exact step_appendLocals_setAggregateFieldAt offset size
    case arg index narrow =>
      exact step_appendLocals_arg index narrow
    case «local» index =>
      exact step_appendLocals_local index
    case initializeSpanLocal index constructor =>
      exact step_appendLocals_initializeSpanLocal index constructor
    case localAddr index =>
      exact step_appendLocals_localAddr index
    case setLocal index =>
      exact step_appendLocals_setLocal index
    case ldc_i4 value =>
      exact step_appendLocals_ldc_i4 value
    case ldc_i8 value =>
      exact step_appendLocals_ldc_i8 value
    case conv_i1 =>
      exact step_appendLocals_conv_i1
    case conv_i2 =>
      exact step_appendLocals_conv_i2
    case conv_u2 =>
      exact step_appendLocals_conv_u2
    case conv_i8 =>
      exact step_appendLocals_conv_i8
    case conv_i4 =>
      exact step_appendLocals_conv_i4
    case conv_u1 =>
      exact step_appendLocals_conv_u1
    case conv_u4 =>
      exact step_appendLocals_conv_u4
    case conv_u8 =>
      exact step_appendLocals_conv_u8
    case conv_u =>
      exact step_appendLocals_conv_u
    case conv_i =>
      exact step_appendLocals_conv_i
    case not =>
      exact step_appendLocals_not
    case add =>
      exact step_appendLocals_add
    case sub =>
      exact step_appendLocals_sub
    case mul =>
      exact step_appendLocals_mul
    case and =>
      exact step_appendLocals_and
    case or =>
      exact step_appendLocals_or
    case xor =>
      exact step_appendLocals_xor
    case shl =>
      exact step_appendLocals_shl
    case shr =>
      exact step_appendLocals_shr
    case shr_un =>
      exact step_appendLocals_shr_un
    case clt =>
      exact step_appendLocals_clt
    case clt_un =>
      exact step_appendLocals_clt_un
    case cgt_un =>
      exact step_appendLocals_cgt_un
    case ceq =>
      exact step_appendLocals_ceq
    case load64 =>
      exact step_appendLocals_load64
    case store64 =>
      exact step_appendLocals_store64
    case dup =>
      exact step_appendLocals_dup
    case pop =>
      exact step_appendLocals_pop
    case br target =>
      exact step_appendLocals_br target
    case switch targets =>
      exact step_appendLocals_switch targets
    case brfalse target =>
      exact step_appendLocals_brfalse target
    case brtrue target =>
      exact step_appendLocals_brtrue target
    case objectTest type throwing =>
      exact step_appendLocals_objectTest type throwing
    case blt_un target =>
      exact step_appendLocals_blt_un target
    case bge_un target =>
      exact step_appendLocals_bge_un target
    case bgt_un target =>
      exact step_appendLocals_bgt_un target
    case bge target =>
      exact step_appendLocals_bge target
    case blt target =>
      exact step_appendLocals_blt target
    case beq target =>
      exact step_appendLocals_beq target
    case bne_un target =>
      exact step_appendLocals_bne_un target
    case call method argc =>
      exact step_appendLocals_call method argc
    case callInstance method argc =>
      exact step_appendLocals_callInstance method argc
    case callVirtual targets argc =>
      exact step_appendLocals_callVirtual targets argc
    case tailCall method argc =>
      exact step_appendLocals_tailCall method argc
    case newAggregate constructor argc size =>
      exact step_appendLocals_newAggregate constructor argc size
    case newObject constructor argc owner bases size =>
      exact step_appendLocals_newObject constructor argc owner bases size
    case skipInit =>
      exact step_appendLocals_skipInit
    case feature id =>
      exact step_appendLocals_feature id
    case intrinsic operation argc =>
      exact step_appendLocals_intrinsic operation argc
    case memory operation =>
      exact step_appendLocals_memory operation
    case ret narrow =>
      exact step_appendLocals_ret narrow
    case throw exception =>
      exact step_appendLocals_throw exception
    case unsupported description =>
      exact step_appendLocals_unsupported description
  exact padded body pc args frame extra stack memory outcome stepped kept

#print axioms step_appendLocals

end CIL.Safety
