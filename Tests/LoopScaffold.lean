import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import Examples.Support
import CIL.StructuralLabels

/-! Kernel-checked frame and cutpoint generation, including rejected ambiguous scaffolds. -/

namespace Tests.LoopScaffold
open CIL.Safety

/-- A numeric local with a single conditional loop edge. -/
def body : CIL.Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true
  code := [.local 0, .brnonzero 0, .ret] }

bind_entry entry := body with [] from Examples.empty
bind_cutpoint header := body matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with entry.frame

/-- Generated homes come from checked allocation and the cutpoint follows compiled instructions. -/
theorem generated_state :
    entry.frame.locals = [.bytes .word32 entry.home0] ∧
    (header [] entry.memory).pc = 1 := by exact ⟨rfl, rfl⟩
#print axioms generated_state

/-- error: Cutpoint must match exactly one instruction -/
#guard_msgs in
bind_cutpoint absent := body matching (fun _ => false) with entry.frame

/-- error: Cutpoint must match exactly one instruction -/
#guard_msgs in
bind_cutpoint ambiguous := body matching (fun _ => true) with entry.frame

/-- Missing vector arguments cannot supply a frame witness. -/
def missingArgument : CIL.Method := {
  code := [.ret], locals := [], returnsValue := false, vectorArgs := [0] }

/-- error: Frame entry must reduce to a successful checked allocation -/
#guard_msgs in
bind_entry invalid := missingArgument with [] from Examples.empty

end Tests.LoopScaffold

namespace Tests.RepeatedCutpoints
open CIL.Safety

/-- Both nested loop latches have the same opcode, so instruction shape is ambiguous. -/
def body : CIL.Method := {
  code := [.nop, .const32 0, .brnonzero 1, .const32 0, .brnonzero 0, .ret]
  locals := [], returnsValue := false }

bind_loop outer := body [0]
bind_loop inner := body [1]
bind_cutpoint outerExit (frame : Frame) := body at outer.latch matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with frame
bind_cutpoint innerExit (frame : Frame) := body at inner.latch matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with frame

/-- Structural labels select distinct checked latches despite identical instruction shapes. -/
theorem distinct_latches : outerExit.pc = 4 ∧ innerExit.pc = 2 := by exact ⟨rfl, rfl⟩
#print axioms distinct_latches

/-- error: Selected cutpoint must exist and match the instruction predicate -/
#guard_msgs in
bind_cutpoint outside (frame : Frame) := body at 99 matching (fun _ => true) with frame

/-- error: Selected cutpoint must exist and match the instruction predicate -/
#guard_msgs in
bind_cutpoint wrongShape (frame : Frame) := body at outer.latch matching
  (fun op => match op with | .ret _ => true | _ => false) with frame

end Tests.RepeatedCutpoints

namespace Tests.SymbolicLoopScaffold
open CIL.Safety

/-- An addressed parameter has a private numeric home in the entry memory. -/
def addressed : CIL.Method := {
  code := [.ret], locals := [], returnsValue := false, parameterHomes := [(0, .word32)] }

bind_entry parameter (value : CIL.W32) := addressed
  with [.scalar (.i32 value)] from Examples.empty

/-- The generated frame equation holds for every parameter value, not just a sample. -/
theorem parameter_entry (value : CIL.W32) :
    enterFrame addressed [.scalar (.i32 value)] Examples.empty =
      .ok (parameter.frame value, parameter.memory value) := parameter.checked value
#print axioms parameter_entry

/-- Vector argument homes preserve a symbolic vector's bytes. -/
def vectorBody : CIL.Method := {
  code := [.ret], locals := [], returnsValue := false, vectorArgs := [0] }

bind_entry vector (bits : BitVec 256) := vectorBody
  with [.scalar (.v256 bits)] from Examples.empty

/-- Vector entry uses the supplied bits and is checked for every vector. -/
theorem vector_entry (bits : BitVec 256) :
    enterFrame vectorBody [.scalar (.v256 bits)] Examples.empty =
      .ok (vector.frame bits, vector.memory bits) := vector.checked bits
#print axioms vector_entry

end Tests.SymbolicLoopScaffold

namespace Tests.SymbolicStorageEntry
open CIL.Safety

/-- Assigned byref and span parameters keep their typed roots in the frame. -/
def body : CIL.Method := {
  code := [.ret], locals := [], returnsValue := false
  parameterHomes := [(0, .reference), (1, .span 4 true)] }

bind_entry entry (memory : Memory) (reference : ManagedReference) (view : SpanView)
    (wellFormed : memory.WellFormed)
    (valid : ValuesValid memory [.reference reference, .bufferSpan view])
    (fits : FrameSetupFits body [.reference reference, .bufferSpan view]) := body
  with [.reference reference, .bufferSpan view] from memory
  using (enterFrame_isSome body _ memory wellFormed valid fits)

/-- Symbolic caller storage remains subject to its validity and frame-shape premises. -/
theorem checked (memory : Memory) (reference : ManagedReference) (view : SpanView)
    (wellFormed : memory.WellFormed)
    (valid : ValuesValid memory [.reference reference, .bufferSpan view])
    (fits : FrameSetupFits body [.reference reference, .bufferSpan view]) :
    enterFrame body [.reference reference, .bufferSpan view] memory =
      .ok (entry.frame memory reference view wellFormed valid fits,
        entry.memory memory reference view wellFormed valid fits) :=
  entry.checked memory reference view wellFormed valid fits
#print axioms checked

end Tests.SymbolicStorageEntry

namespace Tests.TypedHomeFacts
open CIL.Safety

/-- Typed root and span homes require a value before they can be loaded. -/
def body : CIL.Method := {
  code := [.ret], locals := [.unmodeled, .unmodeled], returnsValue := false
  localKinds := [.reference, .span 4 false] }

bind_entry entry := body with [] from Examples.empty

/-- The generated slot aliases expose the exact uninitialized storage from frame entry. -/
theorem initial_slots : entry.slot0 = .root none ∧ entry.slot1 = .span 4 false none :=
  ⟨rfl, rfl⟩
#print axioms initial_slots

/-- Generated span store facts accept a replacement only with its validity and exact mode. -/
theorem replacement (memory : Memory) (view : SpanView)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) :
    storeLocal memory entry.slot1 (.bufferSpan view) =
      .ok (.span 4 false (some view), memory) ∧
    loadLocal memory (.span 4 false (some view)) = .ok (.bufferSpan view) :=
  ⟨entry.store1 memory none view valid width readOnly, entry.load1 memory view valid width readOnly⟩
#print axioms replacement

/-- Generated root facts reuse formation checks and preserve the stored reference. -/
theorem root_replacement (memory : Memory) (reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    storeLocal memory entry.slot0 (.reference reference) =
      .ok (.root (some reference), memory) ∧
    loadLocal memory (.root (some reference)) = .ok (.reference reference) :=
  ⟨entry.store0 memory none reference formed, entry.load0 memory reference formed⟩
#print axioms root_replacement

/-- Home facts do not initialize empty slots or permit a different width or capability. -/
theorem rejected_homes :
    loadLocal Examples.empty entry.slot1 = .error .invalidState ∧
    storeLocal Examples.empty entry.slot1 (.bufferSpan ⟨.null, 0, 8, false⟩) =
      .error .invalidState ∧
    storeLocal Examples.empty entry.slot1 (.bufferSpan ⟨.null, 0, 4, true⟩) =
      .error .invalidState := ⟨rfl, rfl, rfl⟩
#print axioms rejected_homes

end Tests.TypedHomeFacts

namespace Tests.SymbolicHomeKinds
open CIL.Safety

/-- A span local's storage kind can depend on explicit proof parameters. -/
def body (width : Nat) (writable : Bool) : CIL.Method := {
  code := [.ret], locals := [.unmodeled], returnsValue := false
  localKinds := [.span width writable] }

bind_entry entry (width : Nat) (writable : Bool) (bounded : 0 < width ∧ width < 2^64) :=
  (body width writable) with [] from Examples.empty simplifying [body, bounded]

/-- Parameterized home facts retain their storage-kind binders and replacement checks. -/
theorem generated (width : Nat) (writable : Bool) (bounded : 0 < width ∧ width < 2^64)
    (memory : Memory) (view : SpanView) (valid : view.validate memory = .ok ())
    (sameWidth : view.width = width) (sameMode : view.writable = writable) :
    entry.slot0 width writable bounded = .span width writable none ∧
    loadLocal memory (.span width writable (some view)) = .ok (.bufferSpan view) ∧
    storeLocal memory (entry.slot0 width writable bounded) (.bufferSpan view) =
      .ok (.span width writable (some view), memory) :=
  ⟨rfl, entry.load0 width writable bounded memory view valid sameWidth sameMode,
    entry.store0 width writable bounded memory none view valid sameWidth sameMode⟩
#print axioms generated

end Tests.SymbolicHomeKinds

namespace Tests.AllocatingEntry
open CIL.Safety

/-- Two numeric locals allocate homes in symbolic memory before an assigned span parameter. -/
def body : CIL.Method := {
  code := [.ret], locals := [.i64 7, .i32 5], returnsValue := false
  localKinds := [.word64, .word32], parameterHomes := [(0, .span 4 false)] }

bind_entry entry (memory : Memory) (view : SpanView) (wellFormed : memory.WellFormed)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) := body
  with [.bufferSpan view] from memory allocating wellFormed
  simplifying [valid, width, readOnly]

/-- The frame names both homes, and the span parameter's validity carries past their
    allocation; each home keeps its initializer and authority in the entered memory. -/
theorem homes (memory : Memory) (view : SpanView) (wellFormed : memory.WellFormed)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) :
    ∃ first second entered,
      enterFrame body [.bufferSpan view] memory = .ok (entry.frame memory view first second,
        entered) ∧
      (entry.frame memory view first second).locals =
        [.bytes .word64 first, .bytes .word32 second, .span 4 false (some view)] ∧
      read entered first 8 1 = .ok (numberBytes 7 8) ∧
      read entered second 4 1 = .ok (numberBytes 5 4) ∧
      memory.nextIdentity ≤ first.allocation ∧ second.allocation < entered.nextIdentity ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  obtain ⟨first, second, entered, setup, firstHome, secondHome, entryMemory⟩ :=
    entry.checked memory view wellFormed valid width readOnly
  exact ⟨first, second, entered, setup, rfl, firstHome.loaded, secondHome.loaded,
    firstHome.fresh, secondHome.bounded, entryMemory.kept, entryMemory.wellFormed⟩
#print axioms homes

/-- An uninitialized numeric local allocates without a checked initializer. -/
def unmodeled : CIL.Method := {
  code := [.ret], locals := [.unmodeled], returnsValue := false, localKinds := [.word32] }

/-- error: Local 0 allocates a home without a checked numeric initializer -/
#guard_msgs (error) in
bind_entry rejected (memory : Memory) (wellFormed : memory.WellFormed) := unmodeled
  with [] from memory allocating wellFormed

end Tests.AllocatingEntry

namespace Tests.LoopVC
open CIL.Safety

/-- `while (remaining != 0) remaining--; return remaining;` with `remaining` in a frame home. -/
@[cil_code] def countdown : CIL.Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true
  code := [.arg 0, .setLocal 0, .local 0, .brnonzero 6, .local 0, .ret, .local 0, .const32 1,
    .sub, .setLocal 0, .branch 2] }

/-- The program holding only `countdown`. -/
@[cil_code] def program : CIL.Program := [countdown]

bind_entry entry (memory : Memory) (input : CIL.W32) (wellFormed : memory.WellFormed) :=
  countdown with [.scalar (.i32 input)] from memory allocating wellFormed

/-- The remaining count, held in the frame home of the current memory. -/
structure State (memory : Memory) (home : Reference) where
  remaining : CIL.W32
  current : Memory
  frame : EntryMemory memory current
  holds : NumericEntryHome memory current .word32 remaining.toNat home

-- The guard sees the remaining count.
bind_cutpoint header (memory : Memory) (home : Reference) (state : State memory home) :=
  countdown at 3 matching (fun op => match op with | .brnonzero _ => true | _ => false)
  with (entry.frame memory home), [.scalar (.i32 state.remaining)], state.current

/-- The store and exit rules carry the frame part of the state, so the loop proof states only
    its measure; every input terminates with zero and keeps the caller's memory. -/
theorem countdown_returns_zero (memory : Memory) (input : CIL.W32)
    (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 input)] memory =
      .ok (final, [.scalar (.i32 0)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, numeric, entryMemory⟩ := entry.checked memory input wellFormed
  cil_home_store started stored loaded frame holds := (.i32 input) using entryMemory numeric
  refine invoke_loop_results (by rfl) (by rfl) setup (header memory home) (fun _ => True)
    (·.remaining.toNat) ⟨input, started, frame, holds⟩
    (by cil_loop_steps [header, entry.frame, stored, loaded]) trivial ?_
  rintro ⟨remaining, current, frame, holds⟩ -
  have loaded := holds.load (value := .i32 remaining) rfl
  by_cases zero : remaining = 0
  · subst zero
    left
    cil_loop_finish [header, entry.frame, loaded, localResult, frame.leave setup]
  · cil_home_store updated stored nextLoaded nextFrame nextHolds := (.i32 (remaining - 1))
      using frame holds
    cil_loop_continue ⟨remaining - 1, updated, nextFrame, nextHolds⟩
      [header, entry.frame, loaded, localResult, zero, stored, nextLoaded]
    · trivial
    · have positive : remaining.toNat ≠ 0 := fun same => zero (BitVec.eq_of_toNat_eq same)
      have one : (1 : CIL.W32).toNat = 1 := rfl
      show (remaining - 1).toNat < remaining.toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
      omega
#print axioms countdown_returns_zero

/-- error: Tactic `decide` proved that the proposition
  0 < 0
is false -/
#guard_msgs (error) in
/-- A measure that does not decrease leaves a false decrease obligation once the checked path
    and the preservation goal have closed. -/
theorem constant_measure (memory : Memory) (input : CIL.W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 input)] memory =
      .ok (final, [.scalar (.i32 0)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, numeric, entryMemory⟩ := entry.checked memory input wellFormed
  cil_home_store started stored loaded frame holds := (.i32 input) using entryMemory numeric
  refine invoke_loop_results (by rfl) (by rfl) setup (header memory home) (fun _ => True)
    (fun _ => 0) ⟨input, started, frame, holds⟩
    (by cil_loop_steps [header, entry.frame, stored, loaded]) trivial ?_
  rintro ⟨remaining, current, frame, holds⟩ -
  have loaded := holds.load (value := .i32 remaining) rfl
  by_cases zero : remaining = 0
  · subst zero
    left
    cil_loop_finish [header, entry.frame, loaded, localResult, frame.leave setup]
  · cil_home_store updated stored nextLoaded nextFrame nextHolds := (.i32 (remaining - 1))
      using frame holds
    cil_loop_continue ⟨remaining - 1, updated, nextFrame, nextHolds⟩
      [header, entry.frame, loaded, localResult, zero, stored, nextLoaded]
    · trivial
    · decide

/-- error: Tactic `decide` proved that the proposition
  2 - 1 = 2
is false -/
#guard_msgs (error) in
/-- An invariant that holds at entry but is not preserved fails exactly at its preservation
    obligation: from two, the next count is one. -/
theorem stale_invariant (memory : Memory) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 2)] memory =
      .ok (final, [.scalar (.i32 0)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, numeric, entryMemory⟩ := entry.checked memory 2 wellFormed
  cil_home_store started stored loaded frame holds := (.i32 2) using entryMemory numeric
  refine invoke_loop_results (by rfl) (by rfl) setup (header memory home)
    (fun state => state.remaining = 2) (·.remaining.toNat) ⟨2, started, frame, holds⟩
    (by cil_loop_steps [header, entry.frame, stored, loaded]) rfl ?_
  rintro ⟨remaining, current, frame, holds⟩ (invariant : remaining = 2)
  subst invariant
  have loaded := holds.load (value := .i32 2) rfl
  cil_home_store updated stored nextLoaded nextFrame nextHolds := (.i32 (2 - 1))
    using frame holds
  cil_loop_continue ⟨2 - 1, updated, nextFrame, nextHolds⟩
    [header, entry.frame, loaded, localResult, stored, nextLoaded]
  · show (2 - 1 : CIL.W32) = 2
    decide
  · show (2 - 1 : CIL.W32).toNat < (2 : CIL.W32).toNat
    decide

end Tests.LoopVC
