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
theorem framed (memory : Memory) (x : CIL.W64) (wellFormed : memory.WellFormed) :
    ∃ fuel result, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (result, [.scalar (.i64 x)]) ∧ Confined [] memory result := by
  obtain ⟨reference, entered, enter⟩ := entry.checked memory x wellFormed
  have frame := enter.frame
  have homes := (frame []).homes
  have slot : [LocalSlot.bytes (.aggregate 12) reference][0]? = _ := rfl
  obtain ⟨zeroed, zeroStep, zeroSnapshots, zeroFormed, zeroBelow, zeroReady, zeroForm, zeroWrite⟩ :=
    (frame []).snapshots.zero_aggregate homes (frame []).wellFormed slot enter.numeric0.writable
  obtain ⟨payload, storePayload, payloadSnapshots, payloadFormed, payloadBelow, payloadReady,
    payloadForm, payloadValues, payloadWrite⟩ := zeroSnapshots.store_field homes zeroFormed slot rfl zeroReady
      Extracted.layout0_valid (by decide) rfl rfl (fieldIndex := 0) rfl (.i64 x) rfl
  obtain ⟨tagged, storeTag, tagSnapshots, tagFormed, tagBelow, -, tagForm, tagValues, tagWrite⟩ :=
    payloadSnapshots.store_field homes payloadFormed slot rfl payloadReady
      Extracted.layout0_valid (by decide) rfl payloadValues (fieldIndex := 1) rfl (.i32 3) rfl
  have loaded := tagSnapshots.load_field tagFormed slot rfl Extracted.layout0_valid rfl tagValues
    (fieldIndex := 0) rfl rfl
  rw [exists_comm]
  simp only [exists_and_right]
  refine ⟨leaveFrame (entry.frame memory reference) tagged,
    ?_, Confined.frame_round_trip enter.setup (zeroBelow.trans (payloadBelow.trans tagBelow)) ?_⟩
  · cil_checked_steps [enter.setup, zeroStep, storePayload, storeTag, loaded, localAddress,
      entry.frame,
      access_reference_valid _ _ _ _ _ enter.numeric0.writable, zeroForm, payloadForm, tagForm,
      numericOfWidth]
  · rw [write_nextIdentity tagWrite, write_nextIdentity payloadWrite, write_nextIdentity zeroWrite]
    exact Nat.le_refl _

#print axioms framed

/-- The return value and preservation of all previously allocated storage. -/
theorem correctness (memory : Memory) (x : CIL.W64) (wellFormed : memory.WellFormed) :
    ∃ fuel result, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (result, [.scalar (.i64 x)]) ∧ MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨fuel, final, ran, preserved⟩ := framed memory x wellFormed
  exact ⟨fuel, final, ran, preserved.nil_memoryBelow⟩

#print axioms correctness

/-- From well-formed caller memory, the input word is returned and all earlier storage is kept. -/
def structContract : MethodContract CIL.W64 where
  args input := [.scalar (.i64 input)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post input initial final values :=
    values = [.scalar (.i64 input)] ∧ MemoryBelow initial.nextIdentity initial final

/-- Every well-formed caller memory meets `structContract`, with no caller storage written. -/
theorem holds : structContract.Holds Extracted.program 0 := by
  intro value memory formed
  obtain ⟨fuel, final, ran, confined⟩ := framed memory value formed
  exact MethodContract.Holds.intro final _ ⟨fuel, ran⟩ confined ⟨rfl, confined.nil_memoryBelow⟩

#print axioms holds
end ExampleProof
