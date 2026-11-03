import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopVC
import CIL.Safety.AggregateFields
import CIL.Safety.LoopFrames

/-! A zeroed 12-byte struct local, stored field by field and read through a byref helper,
    returns its input; the local's snapshot carries each store and its decoded field values. -/

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
  have homes := home.homes
  have slot : [LocalSlot.bytes (.aggregate 12) reference][0]? = _ := rfl
  obtain ⟨zeroed, zeroStep, zeroSnapshots, zeroFormed, zeroBelow, zeroReady, zeroForm, -⟩ :=
    (LocalSnapshots.empty entered _).zero_aggregate homes entryMemory.wellFormed slot home.writable
  obtain ⟨payload, storePayload, payloadSnapshots, payloadFormed, payloadBelow, payloadReady,
    payloadForm, payloadValues, -⟩ := zeroSnapshots.store_field homes zeroFormed slot rfl zeroReady
      Extracted.layout0_valid (by decide) rfl rfl (fieldIndex := 0) rfl (.i64 x) rfl
  obtain ⟨tagged, storeTag, tagSnapshots, tagFormed, tagBelow, -, tagForm, tagValues, -⟩ :=
    payloadSnapshots.store_field homes payloadFormed slot rfl payloadReady
      Extracted.layout0_valid (by decide) rfl payloadValues (fieldIndex := 1) rfl (.i32 3) rfl
  have loaded := tagSnapshots.load_field tagFormed slot rfl Extracted.layout0_valid rfl tagValues
    (fieldIndex := 0) rfl rfl
  refine ⟨CIL.executionBound Extracted.program 0, leaveFrame (entry.frame memory reference) tagged,
    ?_, MemoryBelow.frame_round_trip setup (zeroBelow.trans (payloadBelow.trans tagBelow))⟩
  apply invoke_of_run (by simp only [cil_code] <;> rfl) rfl setup
  cil_checked_steps [zeroStep, storePayload, storeTag, loaded, localAddress, entry.frame,
    access_reference_valid _ _ _ _ _ home.writable, zeroForm, payloadForm, tagForm, numericOfWidth]

#print axioms correctness
end ExampleProof
