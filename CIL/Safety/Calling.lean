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

end CIL.Safety
