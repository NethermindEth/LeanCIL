import CIL.Safety.CallingTransport
import CIL.Safety.AggregateFields

/-!
# By-reference argument facts

`ValidCall` supplies named access evidence for arbitrary, possibly overlapping argument ranges.
These rules derive current snapshots and field steps from that evidence. A write preserves access
through `ValidCall.after_write`; retaining an earlier snapshot still requires unchanged bytes.
-/

namespace CIL.Safety

/-- The current byte values of an argument range, without asserting permission to read them. -/
def ArgumentView.bytes (view : ArgumentView) (memory : Memory) : List (BitVec 8) :=
  (List.range view.width).map fun offset =>
    (memory.cells view.reference.allocation (view.reference.offset + offset)).bits

/-- The current unsigned word at a byte offset within an argument's snapshot. -/
def ArgumentView.word (view : ArgumentView) (memory : Memory) (offset : Nat) : CIL.W64 :=
  BitVec.ofNat 64 (byteNumber (((view.bytes memory).drop offset).take 8))

/-- A valid input's snapshot is obtained by an actual checked read. -/
theorem ValidCall.input_snapshot {memory : Memory} {inputs outputs : List ArgumentView}
    (call : ValidCall memory inputs outputs) (input : ArgumentView) (member : input ∈ inputs) :
    read memory input.reference input.width 1 = .ok (input.bytes memory) := by
  obtain ⟨bytes, loaded⟩ := call.readable input member
  exact loaded.trans (congrArg Except.ok (read_result_snapshot loaded))

#print axioms ValidCall.input_snapshot

/-- Every input reference is formed, independently of any output alias. -/
theorem ValidCall.input_formed {memory : Memory} {inputs outputs : List ArgumentView}
    (call : ValidCall memory inputs outputs) (input : ArgumentView) (member : input ∈ inputs) :
    form memory input.reference = .ok input.reference :=
  read_reference_valid _ _ _ _ _ (call.input_snapshot input member)

#print axioms ValidCall.input_formed

/-- Every output reference is formed without assuming that its bytes are initialized. -/
theorem ValidCall.output_formed {memory : Memory} {inputs outputs : List ArgumentView}
    (call : ValidCall memory inputs outputs) (output : ArgumentView) (member : output ∈ outputs) :
    form memory output.reference = .ok output.reference :=
  access_reference_valid _ _ _ _ _ (call.writable output member)

#print axioms ValidCall.output_formed

/-- Every nonempty slice inside an output is writable, without requiring an initial value. -/
theorem ValidCall.output_slice {memory : Memory} {inputs outputs : List ArgumentView}
    (call : ValidCall memory inputs outputs) (output : ArgumentView) (member : output ∈ outputs)
    (offset width : Nat) (positive : 0 < width) (within : offset + width ≤ output.width) :
    access memory { output.reference with offset := output.reference.offset + offset }
      width 1 true = .ok () := by
  obtain ⟨_, ready⟩ := access_requirements (call.writable output member)
  exact (ready.slice call.wellFormed offset width positive within).access

#print axioms ValidCall.output_slice

/-- An in-range word field loads from the current input snapshot. Both address formation and
    the read are checked; no input/output separation is assumed. -/
theorem ValidCall.input_word_step {memory : Memory} {inputs outputs : List ArgumentView}
    (call : ValidCall memory inputs outputs) (input : ArgumentView) (member : input ∈ inputs)
    (index : Fin (input.width / 8))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.fieldAt (8 * index.val) 8 false) pc args frame
      (.reference (.address input.reference) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 (input.word memory (8 * index.val))) :: rest)
        frame memory) := by
  have length : (input.bytes memory).length = input.width := by simp [ArgumentView.bytes]
  have loaded := call.input_snapshot input member
  rw [← length] at loaded
  exact step_fieldAt_home (field := { offset := 8 * index.val, width := 8 })
    call.wellFormed loaded (by have := index.isLt; simp only [length]; omega)
    (show ScalarWidth 8 by decide) body pc args frame rest

#print axioms ValidCall.input_word_step

end CIL.Safety
