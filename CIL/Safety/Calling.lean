import CIL.Safety.MemoryLemmas

/-!
# Call entry requirements

`ValidCall` states what a caller must provide on entry for a list of input and output
buffers: well-formed memory, readable inputs and writable outputs. It mentions no method
body, so it can be checked before any execution.
-/

namespace CIL.Safety

/-- A buffer passed to a call: `width` bytes starting at `reference`. -/
structure ArgumentView where
  reference : Reference
  width : Nat
  deriving DecidableEq, Repr

/-- Ordinary entry requirements, independent of the method body or its future execution.
    Inputs and outputs may overlap arbitrarily. Output initialization is not required, and
    retained access never asserts that an input still holds its earlier contents. -/
structure ValidCall (memory : Memory) (inputs outputs : List ArgumentView) : Prop where
  /-- All allocations, views and reference slots obey the checked memory invariants. -/
  wellFormed : memory.WellFormed
  /-- Each input range is readable and initialized in this memory. -/
  readable : ∀ input ∈ inputs, ∃ bytes, read memory input.reference input.width 1 = .ok bytes
  /-- Each output range is writable, including initially unknown storage. -/
  writable : ∀ output ∈ outputs, access memory output.reference output.width 1 true = .ok ()

/-- Every byte of every input buffer is initialized. -/
theorem validCall_inputs_initialized (m : Memory) (inputs outputs : List ArgumentView)
    (h : ValidCall m inputs outputs) (input : ArgumentView) (hi : input ∈ inputs) :
    ∀ i ∈ List.range input.width,
      (m.cells input.reference.allocation (input.reference.offset + i)).initialized = true := by
  obtain ⟨bytes, hread⟩ := h.readable input hi
  exact read_requires_initialization _ _ _ _ _ hread

/-- Every output buffer lies inside a live allocation. -/
theorem validCall_output_live (m : Memory) (inputs outputs : List ArgumentView)
    (h : ValidCall m inputs outputs) (output : ArgumentView) (ho : output ∈ outputs) :
    ∃ a, m.allocations output.reference.allocation = some a ∧ a.live = true ∧
      output.reference.offset + output.width ≤ a.layout.size := by
  exact access_within_allocation _ _ _ _ _ (h.writable output ho)

end CIL.Safety
