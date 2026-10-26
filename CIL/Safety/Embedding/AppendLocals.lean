import CIL.Safety.Embedding.Step

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
theorem fallback_appendLocals (profile : FeatureProfile) (op : Op) (pc : Nat)
    (stack : List Value) (frame : Frame) (extra : List LocalSlot) (memory : Memory) :
    (match pureArity op with
    | some argc =>
      if stack.length < argc then Except.error ExecutionFault.invalidState else do
        let values ← scalars (stack.take argc)
        let some (.next target result _) :=
          CIL.step op false pc [] 0 values (fun _ => none) profile |
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
            CIL.step op false pc [] 0 values (fun _ => none) profile |
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
def StepAppendLocals (op : Op) : Prop :=
  ∀ (body : Method) (pc : Nat) (args : List Value) (frame : Frame)
    (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction),
    step body op pc args frame stack memory = outcome → StepKept outcome →
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome

/-- `nativeBinary` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_nativeBinary (operation : Op) :
    StepAppendLocals (.nativeBinary operation) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.nativeBinary operation) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_nativeBinary

/-- `divide` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_divide (signed remainder : Bool) :
    StepAppendLocals (.divide signed remainder) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.divide signed remainder) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_divide

/-- `checkedArithmetic` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool) :
    StepAppendLocals (.checkedArithmetic kind signed) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.checkedArithmetic kind signed)
        pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_checkedArithmetic

/-- `checkedConvert` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_checkedConvert (width : Nat) (signed unsignedInput : Bool) :
    StepAppendLocals (.checkedConvert width signed unsignedInput) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.checkedConvert width signed unsignedInput)
        pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_checkedConvert

/-- `stackAlloc` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stackAlloc (initLocals : Bool) :
    StepAppendLocals (.stackAlloc initLocals) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, allocateStack_appendLocals, bind_map_left]
  frame_natural

#print axioms step_appendLocals_stackAlloc

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

/-- `gt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_gt :
    StepAppendLocals .gt := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .gt pc stack frame extra memory

#print axioms step_appendLocals_gt

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

/-- `bleu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bleu (target : Nat) :
    StepAppendLocals (.bleu target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.bleu target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_bleu

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

/-- `vectorArg` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_vectorArg (index : Nat) :
    StepAppendLocals (.vectorArg index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_vectorArg

/-- `vectorArgAddr` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_vectorArgAddr (index : Nat) :
    StepAppendLocals (.vectorArgAddr index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_vectorArgAddr

/-- `local` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_local (index : Nat) (narrow : Option NarrowKind) :
    StepAppendLocals (.local index narrow) := by
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

/-- `vectorLocal` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_vectorLocal (index : Nat) :
    StepAppendLocals (.vectorLocal index) := by
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

#print axioms step_appendLocals_vectorLocal

/-- `vectorLocalAddr` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_vectorLocalAddr (index : Nat) :
    StepAppendLocals (.vectorLocalAddr index) := by
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

#print axioms step_appendLocals_vectorLocalAddr

/-- `setVectorLocal` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_setVectorLocal (index : Nat) :
    StepAppendLocals (.setVectorLocal index) := by
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

#print axioms step_appendLocals_setVectorLocal

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
theorem step_appendLocals_setLocal (index : Nat) (narrow : Option NarrowKind) :
    StepAppendLocals (.setLocal index narrow) := by
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

/-- `lane` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_lane (index : Fin 4) :
    StepAppendLocals (.lane index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.lane index) pc stack frame extra memory

#print axioms step_appendLocals_lane

/-- `laneAddress` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_laneAddress (index : Fin 4) :
    StepAppendLocals (.laneAddress index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.laneAddress index) pc stack frame extra memory

#print axioms step_appendLocals_laneAddress

/-- `setLane` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_setLane (index : Fin 4) :
    StepAppendLocals (.setLane index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.setLane index) pc stack frame extra memory

#print axioms step_appendLocals_setLane

/-- `const32` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_const32 (word : W32) :
    StepAppendLocals (.const32 word) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.const32 word) pc stack frame extra memory

#print axioms step_appendLocals_const32

/-- `const64` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_const64 (word : W64) :
    StepAppendLocals (.const64 word) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.const64 word) pc stack frame extra memory

#print axioms step_appendLocals_const64

/-- `convI1` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convI1 :
    StepAppendLocals .convI1 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convI1 pc stack frame extra memory

#print axioms step_appendLocals_convI1

/-- `convI2` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convI2 :
    StepAppendLocals .convI2 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convI2 pc stack frame extra memory

#print axioms step_appendLocals_convI2

/-- `convU2` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convU2 :
    StepAppendLocals .convU2 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convU2 pc stack frame extra memory

#print axioms step_appendLocals_convU2

/-- `convI8` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convI8 :
    StepAppendLocals .convI8 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convI8 pc stack frame extra memory

#print axioms step_appendLocals_convI8

/-- `convI4` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convI4 :
    StepAppendLocals .convI4 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convI4 pc stack frame extra memory

#print axioms step_appendLocals_convI4

/-- `convU1` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convU1 :
    StepAppendLocals .convU1 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convU1 pc stack frame extra memory

#print axioms step_appendLocals_convU1

/-- `convU4` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convU4 :
    StepAppendLocals .convU4 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convU4 pc stack frame extra memory

#print axioms step_appendLocals_convU4

/-- `convU8` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convU8 :
    StepAppendLocals .convU8 := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convU8 pc stack frame extra memory

#print axioms step_appendLocals_convU8

/-- `convU` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_convU :
    StepAppendLocals .convU := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .convU pc stack frame extra memory

#print axioms step_appendLocals_convU

/-- `bnot` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bnot :
    StepAppendLocals .bnot := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .bnot pc stack frame extra memory

#print axioms step_appendLocals_bnot

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
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile .sub pc _ frame extra memory
    | frame_natural

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

/-- `band` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_band :
    StepAppendLocals .band := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .band pc stack frame extra memory

#print axioms step_appendLocals_band

/-- `bor` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bor :
    StepAppendLocals .bor := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .bor pc stack frame extra memory

#print axioms step_appendLocals_bor

/-- `bxor` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bxor :
    StepAppendLocals .bxor := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .bxor pc stack frame extra memory

#print axioms step_appendLocals_bxor

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

/-- `shrUn` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_shrUn :
    StepAppendLocals .shrUn := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .shrUn pc stack frame extra memory

#print axioms step_appendLocals_shrUn

/-- `lt` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_lt :
    StepAppendLocals .lt := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .lt pc stack frame extra memory

#print axioms step_appendLocals_lt

/-- `ltu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ltu :
    StepAppendLocals .ltu := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile .ltu pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_ltu

/-- `gtu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_gtu :
    StepAppendLocals .gtu := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile .gtu pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_gtu

/-- `eq` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_eq :
    StepAppendLocals .eq := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile .eq pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_eq

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

/-- `branch` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_branch (target : Nat) :
    StepAppendLocals (.branch target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.branch target) pc stack frame extra memory

#print axioms step_appendLocals_branch

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

/-- `brzero` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_brzero (target : Nat) :
    StepAppendLocals (.brzero target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.brzero target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_brzero

/-- `brnonzero` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_brnonzero (target : Nat) :
    StepAppendLocals (.brnonzero target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.brnonzero target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_brnonzero

/-- `bltu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bltu (target : Nat) :
    StepAppendLocals (.bltu target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.bltu target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_bltu

/-- `bgeu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bgeu (target : Nat) :
    StepAppendLocals (.bgeu target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.bgeu target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_bgeu

/-- `bgtu` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bgtu (target : Nat) :
    StepAppendLocals (.bgtu target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.bgtu target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_bgtu

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
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.beq target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_beq

/-- `bne` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_bne (target : Nat) :
    StepAppendLocals (.bne target) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    (try cases first) <;> (try cases second)
  all_goals first
    | exact fallback_appendLocals body.profile (.bne target) pc _ frame extra memory
    | frame_natural

#print axioms step_appendLocals_bne

/-- `call` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_call (method : Nat) (argc : Nat) :
    StepAppendLocals (.call method argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_call

/-- `newVector256` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_newVector256 (constructor : Nat) (argc : Nat) :
    StepAppendLocals (.newVector256 constructor argc) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_newVector256

/-- `newAggregate` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_newAggregate (constructor : Nat) (argc : Nat) (size : Fin (2^64)) :
    StepAppendLocals (.newAggregate constructor argc size) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_newAggregate

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

/-- `asRef` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_asRef :
    StepAppendLocals .asRef := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .asRef pc stack frame extra memory

#print axioms step_appendLocals_asRef

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

/-- Every instruction preserves successful and throwing steps under trailing local slots. -/
theorem step_appendLocals (body : Method) (op : Op) (pc : Nat) (args : List Value)
    (frame : Frame) (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction)
    (stepped : step body op pc args frame stack memory = outcome) (kept : StepKept outcome) :
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome := by
  have padded : StepAppendLocals op := by
    cases op
    case nativeBinary operation =>
      exact step_appendLocals_nativeBinary operation
    case divide signed remainder =>
      exact step_appendLocals_divide signed remainder
    case checkedArithmetic kind signed =>
      exact step_appendLocals_checkedArithmetic kind signed
    case checkedConvert width signed unsignedInput =>
      exact step_appendLocals_checkedConvert width signed unsignedInput
    case stackAlloc initLocals =>
      exact step_appendLocals_stackAlloc initLocals
    case nop =>
      exact step_appendLocals_nop
    case neg =>
      exact step_appendLocals_neg
    case gt =>
      exact step_appendLocals_gt
    case bgt target =>
      exact step_appendLocals_bgt target
    case ble target =>
      exact step_appendLocals_ble target
    case bleu target =>
      exact step_appendLocals_bleu target
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
    case vectorArg index =>
      exact step_appendLocals_vectorArg index
    case vectorArgAddr index =>
      exact step_appendLocals_vectorArgAddr index
    case «local» index narrow =>
      exact step_appendLocals_local index narrow
    case vectorLocal index =>
      exact step_appendLocals_vectorLocal index
    case vectorLocalAddr index =>
      exact step_appendLocals_vectorLocalAddr index
    case setVectorLocal index =>
      exact step_appendLocals_setVectorLocal index
    case localAddr index =>
      exact step_appendLocals_localAddr index
    case setLocal index narrow =>
      exact step_appendLocals_setLocal index narrow
    case lane index =>
      exact step_appendLocals_lane index
    case laneAddress index =>
      exact step_appendLocals_laneAddress index
    case setLane index =>
      exact step_appendLocals_setLane index
    case const32 word =>
      exact step_appendLocals_const32 word
    case const64 word =>
      exact step_appendLocals_const64 word
    case convI1 =>
      exact step_appendLocals_convI1
    case convI2 =>
      exact step_appendLocals_convI2
    case convU2 =>
      exact step_appendLocals_convU2
    case convI8 =>
      exact step_appendLocals_convI8
    case convI4 =>
      exact step_appendLocals_convI4
    case convU1 =>
      exact step_appendLocals_convU1
    case convU4 =>
      exact step_appendLocals_convU4
    case convU8 =>
      exact step_appendLocals_convU8
    case convU =>
      exact step_appendLocals_convU
    case bnot =>
      exact step_appendLocals_bnot
    case add =>
      exact step_appendLocals_add
    case sub =>
      exact step_appendLocals_sub
    case mul =>
      exact step_appendLocals_mul
    case band =>
      exact step_appendLocals_band
    case bor =>
      exact step_appendLocals_bor
    case bxor =>
      exact step_appendLocals_bxor
    case shl =>
      exact step_appendLocals_shl
    case shr =>
      exact step_appendLocals_shr
    case shrUn =>
      exact step_appendLocals_shrUn
    case lt =>
      exact step_appendLocals_lt
    case ltu =>
      exact step_appendLocals_ltu
    case gtu =>
      exact step_appendLocals_gtu
    case eq =>
      exact step_appendLocals_eq
    case load64 =>
      exact step_appendLocals_load64
    case store64 =>
      exact step_appendLocals_store64
    case dup =>
      exact step_appendLocals_dup
    case pop =>
      exact step_appendLocals_pop
    case branch target =>
      exact step_appendLocals_branch target
    case switch targets =>
      exact step_appendLocals_switch targets
    case brzero target =>
      exact step_appendLocals_brzero target
    case brnonzero target =>
      exact step_appendLocals_brnonzero target
    case bltu target =>
      exact step_appendLocals_bltu target
    case bgeu target =>
      exact step_appendLocals_bgeu target
    case bgtu target =>
      exact step_appendLocals_bgtu target
    case bge target =>
      exact step_appendLocals_bge target
    case blt target =>
      exact step_appendLocals_blt target
    case beq target =>
      exact step_appendLocals_beq target
    case bne target =>
      exact step_appendLocals_bne target
    case call method argc =>
      exact step_appendLocals_call method argc
    case newVector256 constructor argc =>
      exact step_appendLocals_newVector256 constructor argc
    case newAggregate constructor argc size =>
      exact step_appendLocals_newAggregate constructor argc size
    case skipInit =>
      exact step_appendLocals_skipInit
    case asRef =>
      exact step_appendLocals_asRef
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
