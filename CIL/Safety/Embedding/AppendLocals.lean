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
          CIL.step op false none pc values (fun _ => none) profile |
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
            CIL.step op false none pc values (fun _ => none) profile |
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
/-- `padded` is `original` resumed in padded frames, or `original` is no kept outcome. A home
    past the original frame's slots reads a padded slot, so only such a home's fault differs. -/
def PaddedAgrees (extra : List LocalSlot) (padded original : ExecutionResult FrameAction) :
    Prop :=
  padded = FrameAction.appendLocals extra <$> original ∨ ¬ StepKept original

/-- A read in the padded frame that gives the original result, or the original read failed
    without throwing. -/
def ReadAgrees {α : Type} (padded original : ExecutionResult α) : Prop :=
  padded = original ∨ ∃ fault, original = .error fault ∧ ∀ exception, fault ≠ .thrown exception

/-- A kept original outcome is the padded one, with padded frames. -/
theorem PaddedAgrees.kept {extra : List LocalSlot} {padded original : ExecutionResult FrameAction}
    (agrees : PaddedAgrees extra padded original) (kept : StepKept original) :
    padded = FrameAction.appendLocals extra <$> original :=
  agrees.resolve_right fun lost => lost kept

/-- Equal results with padded frames agree. -/
theorem PaddedAgrees.of_eq {extra : List LocalSlot} {padded original : ExecutionResult FrameAction}
    (same : padded = FrameAction.appendLocals extra <$> original) :
    PaddedAgrees extra padded original :=
  Or.inl same

#print axioms PaddedAgrees.of_eq

/-- A step continues alike after a read that agrees, since a failed original read throws
    nothing. -/
theorem PaddedAgrees.bind {α : Type} {extra : List LocalSlot} {padded original : ExecutionResult α}
    {next other : α → ExecutionResult FrameAction} (read : ReadAgrees padded original)
    (rest : ∀ value, PaddedAgrees extra (next value) (other value)) :
    PaddedAgrees extra (padded >>= next) (original >>= other) := by
  rcases read with same | ⟨fault, failed, unthrown⟩
  · rw [same]
    cases original with
    | error fault => exact Or.inl rfl
    | ok value => exact rest value
  · subst failed
    right
    intro kept
    obtain ⟨exception, thrown⟩ := kept
    exact unthrown exception thrown

/-- A step continues alike after the same computation in both frames. -/
theorem PaddedAgrees.bind_same {α : Type} {extra : List LocalSlot} {first : ExecutionResult α}
    {next other : α → ExecutionResult FrameAction}
    (rest : ∀ value, PaddedAgrees extra (next value) (other value)) :
    PaddedAgrees extra (first >>= next) (first >>= other) :=
  PaddedAgrees.bind (Or.inl rfl) rest

#print axioms PaddedAgrees.kept
#print axioms PaddedAgrees.bind
#print axioms PaddedAgrees.bind_same

/-- A home read in the padded frame reads the same slot, unless the original frame has none. -/
theorem spanView_appendLocals (frame : Frame) (extra : List LocalSlot) (memory : Memory)
    (value : Value) :
    ReadAgrees (spanView (frame.appendLocals extra) memory value)
      (spanView frame memory value) := by
  cases value with
  | spanHome index =>
    cases found : frame.locals[index]? with
    | some slot =>
      left
      simp only [spanView, Frame.appendLocals_getElem? found, found]
    | none =>
      right
      refine ⟨.invalidState, by simp only [spanView, found], fun _ thrown => ?_⟩
      cases thrown
  | _ => exact Or.inl rfl

/-- A call argument reads alike in the padded frame, unless the original read fails. -/
theorem callArgument_appendLocals (frame : Frame) (extra : List LocalSlot) (memory : Memory)
    (value : Value) :
    ReadAgrees (callArgument (frame.appendLocals extra) memory value)
      (callArgument frame memory value) := by
  unfold callArgument
  rcases spanView_appendLocals frame extra memory value with same | ⟨fault, failed, unthrown⟩
  · exact Or.inl (by rw [same])
  · exact Or.inr ⟨fault, by rw [failed]; rfl, unthrown⟩

/-- A list read one value at a time agrees when each read agrees. -/
theorem ReadAgrees.mapM {α β : Type} {padded original : α → ExecutionResult β}
    (each : ∀ value, ReadAgrees (padded value) (original value)) :
    ∀ values : List α, ReadAgrees (values.mapM padded) (values.mapM original)
  | [] => Or.inl rfl
  | value :: rest => by
    simp only [List.mapM_cons]
    rcases each value with same | ⟨fault, failed, unthrown⟩
    · rw [same]
      cases original value with
      | error fault => exact Or.inl rfl
      | ok head =>
        rcases ReadAgrees.mapM each rest with tail | ⟨fault, failed, unthrown⟩
        · exact Or.inl (by rw [tail])
        · exact Or.inr ⟨fault, by simp only [failed]; rfl, unthrown⟩
    · exact Or.inr ⟨fault, by simp only [failed]; rfl, unthrown⟩

/-- A call's arguments read alike in the padded frame, unless an original read fails. -/
theorem callArguments_appendLocals (frame : Frame) (extra : List LocalSlot) (memory : Memory)
    (values : List Value) :
    ReadAgrees (values.mapM (callArgument (frame.appendLocals extra) memory))
      (values.mapM (callArgument frame memory)) :=
  ReadAgrees.mapM (callArgument_appendLocals frame extra memory) values

/-- A span operation's operands read alike in the padded frame, unless an original read
    fails. -/
theorem viewOperands_appendLocals (frame : Frame) (extra : List LocalSlot) (memory : Memory) :
    ∀ (count : Nat) (stack : List Value),
      ReadAgrees (viewOperands (frame.appendLocals extra) memory count stack)
        (viewOperands frame memory count stack)
  | 0, _ => Or.inl rfl
  | _ + 1, [] => Or.inl rfl
  | count + 1, value :: rest => by
    simp only [viewOperands]
    rcases spanView_appendLocals frame extra memory value with same | ⟨fault, failed, unthrown⟩
    · rw [same]
      cases spanView frame memory value with
      | error fault => exact Or.inl rfl
      | ok head =>
        rcases viewOperands_appendLocals frame extra memory count rest with
          tail | ⟨fault, failed, unthrown⟩
        · exact Or.inl (by rw [tail])
        · exact Or.inr ⟨fault, by simp only [failed]; rfl, unthrown⟩
    · exact Or.inr ⟨fault, by simp only [failed]; rfl, unthrown⟩

/-- `initobj` through a home writes the same slot in the padded frame, unless the original frame
    has no such slot. -/
theorem initializeSpanHome_appendLocals (pc : Nat) (frame : Frame) (extra : List LocalSlot)
    (stack : List Value) (memory : Memory) :
    PaddedAgrees extra (initializeSpanHome pc (frame.appendLocals extra) stack memory)
      (initializeSpanHome pc frame stack memory) := by
  unfold initializeSpanHome
  split
  · rename_i index rest
    cases found : frame.locals[index]? with
    | none =>
      right
      simp only [StepKept]
      intro ⟨_, thrown⟩
      cases thrown
    | some slot =>
      left
      have bound := (List.getElem?_eq_some_iff.mp found).1
      cases slot with
      | span width writable view =>
        simp only [Frame.appendLocals_getElem? found]
        cases stored : storeLocal memory (.span width writable view)
            (.bufferSpan ⟨.null, 0, width, writable⟩) with
        | error fault =>
          simp only [Bind.bind, Except.bind, Functor.map, Except.map]
        | ok result =>
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map,
            Except.map, FrameAction.appendLocals, Frame.appendLocals,
            List.set_append_left _ _ bound]
      | _ => simp only [Frame.appendLocals_getElem? found]; rfl
  · exact Or.inl rfl

/-- A span constructor run in place writes the same slot in the padded frame, unless the original
    frame has no such slot. -/
theorem spanInPlaceCall_appendLocals (constructor : CIL.SpanConstructor) (pc : Nat)
    (frame : Frame) (extra : List LocalSlot) (stack : List Value) (memory : Memory) :
    PaddedAgrees extra (spanInPlaceCall constructor pc (frame.appendLocals extra) stack memory)
      (spanInPlaceCall constructor pc frame stack memory) := by
  unfold spanInPlaceCall
  apply PaddedAgrees.bind_same
  intro constructed
  obtain ⟨afterMemory, values⟩ := constructed
  dsimp only
  rcases values with _ | ⟨value, _ | ⟨home, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  cases home
  case spanHome index =>
    dsimp only
    cases found : frame.locals[index]? with
    | none =>
      right
      simp only [StepKept]
      intro ⟨_, thrown⟩
      cases thrown
    | some slot =>
      left
      have bound := (List.getElem?_eq_some_iff.mp found).1
      cases slot with
      | span width writable view =>
        simp only [Frame.appendLocals_getElem? found]
        cases stored : storeLocal afterMemory (.span width writable view) value with
        | error fault =>
          simp only [Bind.bind, Except.bind, Functor.map, Except.map]
          split <;> rfl
        | ok result =>
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map,
            Except.map, FrameAction.appendLocals, Frame.appendLocals,
            List.set_append_left _ _ bound]
          split <;> rfl
      | _ => simp only [Frame.appendLocals_getElem? found]; rfl
  all_goals exact Or.inl rfl

#print axioms spanView_appendLocals
#print axioms callArgument_appendLocals
#print axioms ReadAgrees.mapM
#print axioms callArguments_appendLocals
#print axioms viewOperands_appendLocals
#print axioms initializeSpanHome_appendLocals
#print axioms spanInPlaceCall_appendLocals

set_option hygiene false in
/-- Closes a padded step whose reads may see padded slots: each home read agrees or fails without
    throwing, and every other computation is the same in both frames. -/
local macro "padded_natural" : tactic => `(tactic| (
  repeat' first
  | contradiction
  | (apply PaddedAgrees.of_eq; rfl)
  | dsimp only
  | (apply PaddedAgrees.of_eq
     simp only [map_bind, map_pure, FrameAction.appendLocals, Frame.appendLocals]
     done)
  | exact initializeSpanHome_appendLocals _ _ _ _ _
  | exact spanInPlaceCall_appendLocals _ _ _ _ _ _
  | (apply PaddedAgrees.bind (callArguments_appendLocals _ _ _ _); intro)
  | (apply PaddedAgrees.bind (viewOperands_appendLocals _ _ _ _ _); intro)
  | (apply PaddedAgrees.bind_same; intro)
  | split))

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

/-- `localloc` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_localloc : StepAppendLocals .localloc := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, localAllocation, allocateStack_appendLocals, bind_map_left]
  frame_natural

#print axioms step_appendLocals_localloc

/-- Heap array allocation does not inspect or change a frame's local slots. -/
theorem step_appendLocals_newarr (element : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.newarr element) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.newarr element) pc _ frame extra memory

#print axioms step_appendLocals_newarr

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





/-- `ldarg` preserves outcomes under trailing local slots: a homed argument's slot precedes
    them, and an argument value does not involve the frame. -/
theorem step_appendLocals_ldarg (index : Nat) : StepAppendLocals (.ldarg index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  have loaded : loadArgument body index args (frame.appendLocals extra) memory =
      loadArgument body index args frame memory ∨
      loadArgument body index args frame memory = .error .invalidState := by
    unfold loadArgument
    split
    · rename_i slot _
      cases found : frame.locals[slot]? with
      | none => exact Or.inr rfl
      | some home => exact Or.inl (by simp only [Frame.appendLocals_getElem? found])
    all_goals exact Or.inl rfl
  have unfolded : ∀ current : Frame, step body (.ldarg index) pc args current stack memory =
      (do
        let value ← loadArgument body index args current memory
        return FrameAction.next (pc + 1) (value :: stack) current memory) := fun _ => rfl
  revert kept
  rw [unfolded, unfolded]
  rcases loaded with same | missing
  · rw [same]
    intro
    frame_natural
  · rw [missing]
    simp [StepKept, Functor.map, Except.map]

#print axioms step_appendLocals_ldarg

/-- `starg` preserves outcomes under trailing local slots: a homed argument's slot precedes
    them, and an argument without a home faults alike. -/
theorem step_appendLocals_starg (index : Nat) : StepAppendLocals (.starg index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  cases stack with
  | nil =>
    revert kept
    simp only [step]
    repeat' split
    all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)
  | cons value rest =>
    have unfolded : ∀ current : Frame,
        step body (.starg index) pc args current (value :: rest) memory = (do
          let (current, memory) ← storeArgument body index value current memory
          return FrameAction.next (pc + 1) rest current memory) := fun _ => rfl
    revert kept
    rw [unfolded, unfolded]
    unfold storeArgument
    split
    · rename_i slot _
      cases found : frame.locals[slot]? with
      | some home =>
        simp only [Frame.appendLocals_getElem? found, Frame.appendLocals_set found]
        intro
        cases storeLocal memory home value <;> rfl
      | none => simp [StepKept, Bind.bind, Except.bind]
    · simp [StepKept, Bind.bind, Except.bind]

#print axioms step_appendLocals_starg

/-- `ldarga` preserves outcomes under trailing local slots: a homed argument's slot precedes
    them, and an argument without a home faults alike. -/
theorem step_appendLocals_ldarga (index : Nat) : StepAppendLocals (.ldarga index) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  have addressed : addressArgument body index (frame.appendLocals extra) memory =
      addressArgument body index frame memory ∨
      addressArgument body index frame memory = .error .invalidState := by
    unfold addressArgument
    split
    · rename_i slot _
      cases found : frame.locals[slot]? with
      | none => exact Or.inr rfl
      | some home => exact Or.inl (by simp only [Frame.appendLocals_getElem? found])
    · exact Or.inl rfl
  have unfolded : ∀ current : Frame, step body (.ldarga index) pc args current stack memory =
      (do
        let value ← addressArgument body index current memory
        return FrameAction.next (pc + 1) (value :: stack) current memory) := fun _ => rfl
  revert kept
  rw [unfolded, unfolded]
  rcases addressed with same | missing
  · rw [same]
    intro
    frame_natural
  · rw [missing]
    simp [StepKept, Functor.map, Except.map]

#print axioms step_appendLocals_ldarga

/-- `ldloc` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldloc (index : Nat) : StepAppendLocals (.ldloc index) := by
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

#print axioms step_appendLocals_ldloc

/-- `ldloca` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldloca (index : Nat) :
    StepAppendLocals (.ldloca index) := by
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

#print axioms step_appendLocals_ldloca

/-- `stloc` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stloc (index : Nat) : StepAppendLocals (.stloc index) := by
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

#print axioms step_appendLocals_stloc

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

/-- `ldnull` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldnull :
    StepAppendLocals .ldnull := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .ldnull pc stack frame extra memory

#print axioms step_appendLocals_ldnull

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
  append_stack_cases using
    fallback_appendLocals body.profile .add pc _ frame extra memory

#print axioms step_appendLocals_add

/-- `sub` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_sub :
    StepAppendLocals .sub := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step referenceCompareCall referenceSubtractCall
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
  unfold step referenceCompareCall referenceSubtractCall
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
  unfold step referenceCompareCall referenceSubtractCall
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
  unfold step referenceCompareCall referenceSubtractCall
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile .ceq pc _ frame extra memory

#print axioms step_appendLocals_ceq

/-- `ldind` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldind (kind : CIL.NumericKind) :
    StepAppendLocals (.ldind kind) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.ldind kind) pc stack frame extra memory

#print axioms step_appendLocals_ldind

/-- `stind` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stind (kind : CIL.NumericKind) :
    StepAppendLocals (.stind kind) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.stind kind) pc stack frame extra memory

#print axioms step_appendLocals_stind

/-- `ldlen` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldlen :
    StepAppendLocals .ldlen := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .ldlen pc stack frame extra memory

#print axioms step_appendLocals_ldlen

/-- `ldelem` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldelem (kind : CIL.NumericKind) :
    StepAppendLocals (.ldelem kind) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.ldelem kind) pc stack frame extra memory

#print axioms step_appendLocals_ldelem

/-- `ldelem.ref` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldelem_ref :
    StepAppendLocals .ldelem_ref := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .ldelem_ref pc stack frame extra memory

#print axioms step_appendLocals_ldelem_ref

/-- `stelem` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stelem (kind : CIL.NumericKind) :
    StepAppendLocals (.stelem kind) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile (.stelem kind) pc stack frame extra memory

#print axioms step_appendLocals_stelem

/-- `stelem.ref` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stelem_ref :
    StepAppendLocals .stelem_ref := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  exact fallback_appendLocals body.profile .stelem_ref pc stack frame extra memory

#print axioms step_appendLocals_stelem_ref

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

/-- `castclass` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_castclass (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.castclass type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.castclass type) pc _ frame extra memory

#print axioms step_appendLocals_castclass

/-- `isinst` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_isinst (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.isinst type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  apply observed_appendLocals
  append_stack_cases using
    fallback_appendLocals body.profile (.isinst type) pc _ frame extra memory

#print axioms step_appendLocals_isinst

/-- Instance field loads do not inspect or change a frame's local slots. -/
theorem step_appendLocals_ldfld (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.ldfld field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step]
  frame_natural

#print axioms step_appendLocals_ldfld

/-- Instance field stores do not inspect or change a frame's local slots. -/
theorem step_appendLocals_stfld (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.stfld field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step]
  frame_natural

#print axioms step_appendLocals_stfld

/-- Instance field addresses do not inspect or change a frame's local slots. -/
theorem step_appendLocals_ldflda (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.ldflda field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step]
  frame_natural

#print axioms step_appendLocals_ldflda

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
theorem step_appendLocals_call (method : CIL.Extraction.MethodRef) (prefixes : CallPrefixes) :
    StepAppendLocals (.call method prefixes) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step modelStep observedCall runModel intrinsicCall referenceCompareCall
    referenceSubtractCall featureCall typedTransferCall skipInitCall
  padded_natural

#print axioms step_appendLocals_call

/-- Receiver calls preserve outcomes under trailing local slots. -/
theorem step_appendLocals_callvirt (method : CIL.Extraction.MethodRef) :
    StepAppendLocals (.callvirt method) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step
  padded_natural

#print axioms step_appendLocals_callvirt

/-- `newobj` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_newobj (constructor : Extraction.MethodRef) :
    StepAppendLocals (.newobj constructor) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step newobjStep constructAggregate constructObject modelStep observedCall runModel
    intrinsicCall referenceCompareCall referenceSubtractCall featureCall typedTransferCall
    skipInitCall
  padded_natural

#print axioms step_appendLocals_newobj

/-- `memory` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_memory (operation : MemoryOp) :
    StepAppendLocals (.memory operation) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step
  padded_natural

#print axioms step_appendLocals_memory

/-- `ldsfld` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldsfld (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.ldsfld field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_ldsfld

/-- `ldsflda` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldsflda (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.ldsflda field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_ldsflda

/-- A typed ldobj preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldobj (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.ldobj type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step
  padded_natural
#print axioms step_appendLocals_ldobj

/-- A typed stobj preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stobj (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.stobj type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural
#print axioms step_appendLocals_stobj

/-- A typed initobj preserves outcomes under trailing local slots. -/
theorem step_appendLocals_initobj (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.initobj type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step
  padded_natural
#print axioms step_appendLocals_initobj

/-- A typed sizeof preserves outcomes under trailing local slots. -/
theorem step_appendLocals_sizeof (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.sizeof type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural
#print axioms step_appendLocals_sizeof

/-- A typed cpobj preserves outcomes under trailing local slots. -/
theorem step_appendLocals_cpobj (type : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.cpobj type) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural
#print axioms step_appendLocals_cpobj

/-- A typed `ldelem` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldelem_any (element : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.ldelem_any element) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_ldelem_any

/-- A typed `stelem` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_stelem_any (element : CIL.Extraction.TypeExpr) :
    StepAppendLocals (.stelem_any element) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_stelem_any

/-- An `ldelema` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldelema (element : CIL.Extraction.TypeExpr) (readOnly : Bool) :
    StepAppendLocals (.ldelema element readOnly) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_ldelema

/-- `ldtoken` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ldtoken (operand : CIL.TokenOperand) :
    StepAppendLocals (.ldtoken operand) := by
  cases operand <;> intro body pc args frame extra stack memory outcome stepped kept <;>
    subst stepped <;> clear kept <;> unfold step <;> frame_natural

#print axioms step_appendLocals_ldtoken

/-- `stsfld` faults whatever the frame holds. -/
theorem step_appendLocals_stsfld (field : CIL.Extraction.FieldRef) :
    StepAppendLocals (.stsfld field) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_stsfld

/-- `ret` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_ret :
    StepAppendLocals .ret := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  simp only [step, observerCount]
  simp only [returnFrom]
  by_cases unknown : unspecifiedOperands 1 stack = true
  · simp only [unknown, ite_true]
    rfl
  simp only [unknown, Bool.false_eq_true, ite_false]
  repeat' first
    | rfl
    | (simp only [map_bind, map_pure, FrameAction.appendLocals]; done)
    | (apply bind_congr; intro)
    | split

#print axioms step_appendLocals_ret

/-- `throw` preserves outcomes under trailing local slots. -/
theorem step_appendLocals_throw (exception : ExceptionType) :
    StepAppendLocals (.throw exception) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_throw

/-- A hole preserves outcomes under trailing local slots. -/
theorem step_appendLocals_unadmitted (opcode : Nat) :
    StepAppendLocals (.unadmitted opcode) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  clear kept
  unfold step
  frame_natural

#print axioms step_appendLocals_unadmitted

/-- Managed pointers never inspect the unused trailing frame slots. -/
theorem step_appendLocals_calli (signature : ManagedSignature) (tail : Bool) :
    StepAppendLocals (.calli signature tail) := by
  intro body pc args frame extra stack memory outcome stepped kept
  subst stepped
  refine PaddedAgrees.kept ?_ kept
  unfold step calliStep
  padded_natural
#print axioms step_appendLocals_calli

/-- Every instruction preserves successful and throwing steps under trailing local slots. -/
theorem step_appendLocals (body : Method) (op : Instruction) (pc : Nat) (args : List Value)
    (frame : Frame) (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction)
    (stepped : step body op pc args frame stack memory = outcome) (kept : StepKept outcome) :
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome := by
  have padded : StepAppendLocals op := by
    cases op
    case calli signature tail => exact step_appendLocals_calli signature tail
    case div | div_un | rem | rem_un | add_ovf | add_ovf_un | sub_ovf | sub_ovf_un | mul_ovf
      | mul_ovf_un => exact step_appendLocals_faulting _ rfl
    case conv_ovf target =>
      exact step_appendLocals_conv_ovf target
    case conv_ovf_un target =>
      exact step_appendLocals_conv_ovf_un target
    case localloc =>
      exact step_appendLocals_localloc
    case newarr element => exact step_appendLocals_newarr element
    case ldobj type => exact step_appendLocals_ldobj type
    case stobj type => exact step_appendLocals_stobj type
    case initobj type => exact step_appendLocals_initobj type
    case sizeof type => exact step_appendLocals_sizeof type
    case cpobj type => exact step_appendLocals_cpobj type
    case ldelem_any element => exact step_appendLocals_ldelem_any element
    case stelem_any element => exact step_appendLocals_stelem_any element
    case ldelema element readOnly => exact step_appendLocals_ldelema element readOnly
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
    case ldarg index =>
      exact step_appendLocals_ldarg index
    case starg index =>
      exact step_appendLocals_starg index
    case ldarga index =>
      exact step_appendLocals_ldarga index
    case ldloc index =>
      exact step_appendLocals_ldloc index
    case ldloca index =>
      exact step_appendLocals_ldloca index
    case stloc index =>
      exact step_appendLocals_stloc index
    case ldc_i4 value =>
      exact step_appendLocals_ldc_i4 value
    case ldc_i8 value =>
      exact step_appendLocals_ldc_i8 value
    case ldnull =>
      exact step_appendLocals_ldnull
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
    case ldind kind =>
      exact step_appendLocals_ldind kind
    case stind kind =>
      exact step_appendLocals_stind kind
    case ldlen =>
      exact step_appendLocals_ldlen
    case ldelem kind =>
      exact step_appendLocals_ldelem kind
    case ldelem_ref =>
      exact step_appendLocals_ldelem_ref
    case stelem kind =>
      exact step_appendLocals_stelem kind
    case stelem_ref =>
      exact step_appendLocals_stelem_ref
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
    case ldfld field => exact step_appendLocals_ldfld field
    case ldflda field => exact step_appendLocals_ldflda field
    case stfld field => exact step_appendLocals_stfld field
    case castclass type =>
      exact step_appendLocals_castclass type
    case isinst type =>
      exact step_appendLocals_isinst type
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
    case call method prefixes =>
      exact step_appendLocals_call method prefixes
    case callvirt method => exact step_appendLocals_callvirt method
    case newobj constructor =>
      exact step_appendLocals_newobj constructor
    case cpblk | initblk | ldftn | ldstr =>
      intro body pc args frame extra stack memory outcome stepped kept
      subst stepped
      refine PaddedAgrees.kept ?_ kept
      unfold step
      padded_natural
    case memory operation =>
      exact step_appendLocals_memory operation
    case ldsfld field => exact step_appendLocals_ldsfld field
    case ldsflda field => exact step_appendLocals_ldsflda field
    case ldtoken operand => exact step_appendLocals_ldtoken operand
    case stsfld field => exact step_appendLocals_stsfld field
    case ret =>
      exact step_appendLocals_ret
    case throw exception =>
      exact step_appendLocals_throw exception
    case unadmitted opcode =>
      exact step_appendLocals_unadmitted opcode
  exact padded body pc args frame extra stack memory outcome stepped kept

#print axioms step_appendLocals

end CIL.Safety
