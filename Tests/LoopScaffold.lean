import CIL.Safety.LoopScaffold
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
