import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import CIL.Safety.AggregateFields

/-! A zeroed 12-byte struct local, stored field by field and read through a byref helper,
    returns its input; the field view carries each store and the frame's memory facts. -/

open CIL.Safety
namespace ExampleProof

bind_entry entry (memory : Memory) (x : CIL.W64) (wellFormed : memory.WellFormed) :=
  Extracted.method0 with [.scalar (.i64 x)] from memory allocating wellFormed

/-- The compiled struct stores and helper call return every input word.
    All caller allocation metadata, bytes, initialization and permissions survive;
    only fresh frame-owned storage may be allocated, written and expired. -/
theorem correctness (memory : Memory) (x : CIL.W64) (wellFormed : memory.WellFormed) :
    ∃ fuel result, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (result, [.scalar (.i64 x)]) ∧ MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, entered, setup, home, entryMemory⟩ := entry.checked memory x wellFormed
  have entryView := FieldView.ofEntry (layout := Extracted.layout0) entryMemory home rfl
  have disjoint : Extracted.layout0.Disjoint := by decide
  obtain ⟨zeroed, zeroStep, zeroView⟩ := entryView.zero (size := 12) rfl
  obtain ⟨payload, storePayload, payloadView⟩ :=
    zeroView.store Extracted.layout0_valid disjoint (index := 0) rfl (.i64 x) rfl
  obtain ⟨tagged, storeTag, taggedView⟩ :=
    payloadView.store Extracted.layout0_valid disjoint (index := 1) rfl (.i32 3) rfl
  have loaded := taggedView.load Extracted.layout0_valid (index := 0) rfl rfl
  refine ⟨CIL.executionBound Extracted.program 0, leaveFrame (entry.frame memory reference) tagged,
    ?_, taggedView.frame.leave setup _ rfl⟩
  apply invoke_of_run (by simp only [cil_code] <;> rfl) rfl setup
  cil_checked_steps [zeroStep, storePayload, storeTag, loaded, localAddress, entry.frame,
    entryView.form, zeroView.form, payloadView.form, taggedView.form, numericOfWidth]

#print axioms correctness
end ExampleProof
