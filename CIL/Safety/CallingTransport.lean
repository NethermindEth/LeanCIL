import CIL.Safety.Calling
import CIL.Safety.AccessBelow
import CIL.Safety.FrameMemoryBelow
import CIL.Safety.MethodContract

/-!
# Transporting call entry requirements

`ValidCall` holds of one memory; these lemmas carry it to a later memory, so a caller can
pass the same buffers again after its own writes, after entering a frame, after memory that
keeps every old allocation's access (`AccessBelow`), and after a call confined to a
footprint the inputs lie apart from. `ValidCall.mono` drops buffers, and
`ValidCall.input_bound` / `ValidCall.output_bound` give the identity bound those
transport premises name.
-/

namespace CIL.Safety

/-- Every input buffer lies in an allocation that exists before `memory.nextIdentity`. -/
theorem ValidCall.input_bound {memory : Memory} {inputs outputs : List ArgumentView}
    (valid : ValidCall memory inputs outputs) {input : ArgumentView} (member : input ∈ inputs) :
    input.reference.allocation < memory.nextIdentity := by
  obtain ⟨bytes, loaded⟩ := valid.2.1 input member
  exact valid.1.access_bound (read_access loaded)

/-- Every output buffer lies in an allocation that exists before `memory.nextIdentity`. -/
theorem ValidCall.output_bound {memory : Memory} {inputs outputs : List ArgumentView}
    (valid : ValidCall memory inputs outputs) {output : ArgumentView}
    (member : output ∈ outputs) :
    output.reference.allocation < memory.nextIdentity :=
  valid.1.access_bound (valid.2.2 output member)

/-- A call valid for some buffers is valid for any of them. -/
theorem ValidCall.mono {memory : Memory}
    {inputs outputs fewerInputs fewerOutputs : List ArgumentView}
    (valid : ValidCall memory inputs outputs)
    (inputsCovered : ∀ input ∈ fewerInputs, input ∈ inputs)
    (outputsCovered : ∀ output ∈ fewerOutputs, output ∈ outputs) :
    ValidCall memory fewerInputs fewerOutputs :=
  ⟨valid.1, fun input member => valid.2.1 input (inputsCovered input member),
    fun output member => valid.2.2 output (outputsCovered output member)⟩

/-- Well-formed memory that keeps the descriptors, authority and initialization of every
    allocation older than `memory.nextIdentity` keeps the call valid; byte values may change. -/
theorem ValidCall.after_below {memory result : Memory} {inputs outputs : List ArgumentView}
    {watermark : Nat} (valid : ValidCall memory inputs outputs)
    (retained : AccessBelow watermark memory result) (covers : memory.nextIdentity ≤ watermark)
    (formed : result.WellFormed) : ValidCall result inputs outputs := by
  have old : ∀ {id}, id < memory.nextIdentity → id < watermark :=
    fun bound => Nat.lt_of_lt_of_le bound covers
  refine ⟨formed, fun input member => ?_, fun output member => ?_⟩
  · obtain ⟨bytes, loaded⟩ := valid.2.1 input member
    exact retained.readable loaded (old (valid.input_bound member))
  · exact retained.access (valid.2.2 output member) (old (valid.output_bound member))

/-- A checked write keeps the call valid, even one into an input or output buffer: it
    revokes no authority and clears no initialized byte. -/
theorem ValidCall.after_write {memory result : Memory} {inputs outputs : List ArgumentView}
    {reference : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (valid : ValidCall memory inputs outputs)
    (written : write memory reference bytes alignment = .ok result) :
    ValidCall result inputs outputs :=
  valid.after_below (write_preserves_access_below written memory.nextIdentity) (Nat.le_refl _)
    (write_preserves_wellFormed _ _ _ _ _ valid.1 written)

/-- Entering a frame keeps the caller's call valid: it only adds fresh allocations. -/
theorem ValidCall.after_enterFrame {memory entered : Memory}
    {inputs outputs : List ArgumentView}
    {body : CIL.Method} {args : List Value} {frame : Frame}
    (valid : ValidCall memory inputs outputs)
    (setup : enterFrame body args memory = .ok (frame, entered)) :
    ValidCall entered inputs outputs :=
  valid.after_below (enterFrame_preserves_caller_memory _ _ _ _ _ setup).accessBelow
    (Nat.le_refl _) (enterFrame_preserves_wellFormed _ _ _ _ _ valid.1 setup)

/-- A call confined to `footprint` keeps the call valid for inputs apart from the footprint;
    inside it `Confined` may revoke read authority, so those inputs are excluded. Outputs
    need no premise, since `Confined` keeps write authority everywhere. -/
theorem ValidCall.after_confined {memory result : Memory} {inputs outputs : List ArgumentView}
    {footprint : List (Reference × Nat)} (valid : ValidCall memory inputs outputs)
    (framed : Confined footprint memory result) (formed : result.WellFormed)
    (apart : ∀ input ∈ inputs, ∀ entry ∈ footprint, Apart input.reference input.width entry) :
    ValidCall result inputs outputs := by
  refine ⟨formed, fun input member => ?_, fun output member => ?_⟩
  · obtain ⟨bytes, loaded⟩ := valid.2.1 input member
    exact ⟨bytes, framed.read_apart valid.1 loaded (apart input member)⟩
  · exact (framed.access_write _ (valid.output_bound member) _ _).trans (valid.2.2 output member)

#print axioms ValidCall.input_bound
#print axioms ValidCall.output_bound
#print axioms ValidCall.mono
#print axioms ValidCall.after_below
#print axioms ValidCall.after_write
#print axioms ValidCall.after_enterFrame
#print axioms ValidCall.after_confined

end CIL.Safety
