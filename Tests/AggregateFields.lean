import CIL.Safety.AggregateFields
import CIL.Safety.LocalSnapshotSteps

/-!
# Struct field view tests

Field laws on a 12-byte layout with a word at offset 0 and an int at offset 8, checked field
steps through a struct home, and a remembered struct local beside a word local. An overlapping
explicit layout fails the disjointness check, so no field law instantiates on it, and a store
spanning two fields changes both: these stay at the byte level.
-/

namespace Tests.AggregateFields

open CIL.Safety
open CIL (AggregateLayout FieldLayout)

/-- `Packet`: a word at offset 0 and an int at offset 8 in 12 bytes. -/
def packet : AggregateLayout := ⟨12, [⟨0, 8, false⟩, ⟨8, 4, false⟩]⟩

/-- An explicit layout whose int at offset 4 overlaps the word's upper half. -/
def overlapping : AggregateLayout := ⟨12, [⟨0, 8, false⟩, ⟨4, 4, false⟩]⟩

/-- The int field of `packet`. -/
abbrev tag : FieldLayout := ⟨8, 4, false⟩

/-- A store of eight bytes at offset 4, across both fields of `packet`. -/
def straddling : FieldLayout := ⟨4, 8, false⟩

/-- The most bytes a 32-bit store can set. -/
def allOnes : Nat := 2 ^ 32 - 1

/-- Twelve zero bytes. -/
def zeros : List (BitVec 8) := List.replicate 12 0

theorem packet_checked : packet.Valid ∧ packet.Disjoint := by decide

/-- Storing the int replaces its value and keeps the word, for any struct bytes. -/
theorem store_keeps_word (bytes : List (BitVec 8)) (sized : bytes.length = 12) (number : Nat) :
    packet.values (tag.setIn bytes number) =
      (packet.values bytes).set 1 (number % 256 ^ 4) :=
  packet.values_setIn packet_checked.1 packet_checked.2 sized rfl number

#print axioms packet_checked
#print axioms store_keeps_word

/-- The overlapping layout is admitted by `Valid` but fails the disjointness check. -/
theorem overlapping_rejected : overlapping.Valid ∧ ¬ overlapping.Disjoint := by decide

/-- On the overlapping layout an int store changes the word, so the field law cannot hold. -/
theorem overlapping_store_changes_word :
    (⟨0, 8, false⟩ : FieldLayout).numberIn ((⟨4, 4, false⟩ : FieldLayout).setIn zeros allOnes) ≠
      (⟨0, 8, false⟩ : FieldLayout).numberIn zeros := by decide

/-- The layout law instantiates on `packet`; on the overlapping layout it needs a disjointness
    proof that does not exist. -/
theorem overlapping_law_unavailable :
    packet.values (tag.setIn zeros allOnes) = (packet.values zeros).set 1 (allOnes % 256 ^ 4) := by
  fail_if_success
    have := overlapping.values_setIn overlapping_rejected.1 (by decide) (bytes := zeros) rfl
      (index := 1) rfl allOnes
  exact packet.values_setIn packet_checked.1 (by decide) (bytes := zeros) rfl (index := 1) rfl
    allOnes

#print axioms overlapping_rejected
#print axioms overlapping_store_changes_word
#print axioms overlapping_law_unavailable

/-- A store across the word and the int is apart from neither field. -/
theorem straddling_touches_both :
    ¬ straddling.Apart ⟨0, 8, false⟩ ∧ ¬ straddling.Apart tag := by decide

/-- It changes both field values at once, unlike any single field store. -/
theorem straddling_changes_both :
    packet.values (straddling.setIn zeros (2 ^ 64 - 1)) = [2 ^ 64 - 2 ^ 32, allOnes] := by
  decide

/-- An int store keeps the word, but the preservation law does not apply to a store that
    straddles into the int. -/
theorem straddling_law_unavailable :
    (⟨0, 8, false⟩ : FieldLayout).numberIn (tag.setIn zeros allOnes) =
      (⟨0, 8, false⟩ : FieldLayout).numberIn zeros := by
  fail_if_success
    have := FieldLayout.numberIn_setIn_apart (other := tag) (bytes := zeros)
      (field := straddling) (by decide) (by decide) allOnes
  exact FieldLayout.numberIn_setIn_apart (by decide) (by decide) allOnes

#print axioms straddling_touches_both
#print axioms straddling_changes_both
#print axioms straddling_law_unavailable

/-- Storing the int of a remembered `packet` local keeps the word that a later load reads. -/
theorem store_then_load {entered memory : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[0]? = some (.bytes (.aggregate 12) home))
    (specified : known 0 = some (.aggregate bytes))
    (writable : access memory home 12 1 true = .ok ()) (bits : BitVec 32) (word : Nat)
    (present : (packet.values bytes)[0]? = some word) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.setFieldAt 8 4) pc args frame
          (.scalar (.i32 bits) :: .reference (.address home) :: rest) memory =
          .ok (.next (pc + 1) rest frame after)) ∧
      ∀ body pc args frame rest,
        step body (.fieldAt 0 8 false) pc args frame (.reference (.address home) :: rest) after =
          .ok (.next (pc + 1) (.scalar (.i64 (BitVec.ofNat 64 word)) :: rest) frame after) := by
  obtain ⟨after, stored, storedSnapshots, storedFormed, -, -, -, storedValues, -⟩ :=
    snapshots.store_field homes formed slot specified writable packet_checked.1 packet_checked.2
      rfl rfl (fieldIndex := 1) rfl (.i32 bits) rfl
  exact ⟨after, stored, storedSnapshots.load_field storedFormed slot rfl packet_checked.1 rfl
    storedValues (fieldIndex := 0) rfl (by simpa using present)⟩

/-- The same int store goes through on `packet` but needs the disjointness check, which the
    overlapping layout fails. -/
theorem store_unavailable {entered memory : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[0]? = some (.bytes (.aggregate 12) home))
    (specified : known 0 = some (.aggregate bytes))
    (writable : access memory home 12 1 true = .ok ()) :
    ∃ after,
      LocalSnapshots after slots (rememberLocal known 0 (.aggregate (tag.setIn bytes 3))) := by
  fail_if_success
    have := snapshots.store_field homes formed slot specified writable overlapping_rejected.1
      (by decide) rfl rfl (fieldIndex := 1) rfl (.i32 3) rfl
  obtain ⟨after, -, stored, -⟩ := snapshots.store_field homes formed slot specified writable
    packet_checked.1 packet_checked.2 rfl rfl (fieldIndex := 1) rfl (.i32 3) rfl
  exact ⟨after, stored⟩

#print axioms store_then_load
#print axioms store_unavailable

/-- Zero a struct local, store its int field, then store and reload a word local. -/
@[cil_code] def structAndWord : CIL.Method := {
  code := [.localAddr 0, .initAggregate 12, .localAddr 0, .arg 0, .setFieldAt 8 4,
    .arg 1, .setLocal 1, .local 0, .ret]
  locals := [.aggregate zeros, .i64 0], localKinds := [.aggregate 12, .word64],
  returnsValue := true }

/-- The remembered struct local holds exactly the stored int over zeros after a later word
    store to another local. -/
theorem struct_beside_word {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {structHome wordHome : Reference}
    (homes : WritableHomes entered boundary [.aggregate 12, .word64] frame.locals)
    (formed : memory.WellFormed)
    (structSlot : frame.locals[0]? = some (.bytes (.aggregate 12) structHome))
    (wordSlot : frame.locals[1]? = some (.bytes .word64 wordHome))
    (structReady : access memory structHome 12 1 true = .ok ())
    (wordReady : access memory wordHome 8 1 true = .ok ()) (bits : BitVec 32) (word : CIL.W64) :
    ∃ after, run [structAndWord] 10 0 0 [.scalar (.i32 bits), .scalar (.i64 word)] frame []
      memory = .ok (after, [.scalar (.aggregate (tag.setIn zeros bits.toNat))]) := by
  obtain ⟨zeroed, zeroStep, zeroSnapshots, zeroFormed, -, zeroReady, zeroForm, zeroWrite⟩ :=
    (LocalSnapshots.empty memory frame.locals).zero_aggregate homes formed structSlot structReady
  obtain ⟨tagged, tagStep, tagSnapshots, tagFormed, -, -, -, -, tagWrite⟩ :=
    zeroSnapshots.store_field homes zeroFormed structSlot rfl zeroReady packet_checked.1
      packet_checked.2 rfl rfl (fieldIndex := 1) rfl (.i32 bits) rfl
  have wordTagged := snapshot_access_after_write
    (snapshot_access_after_write wordReady zeroWrite) tagWrite
  cil_checked_steps (snapshots := tagSnapshots) [structSlot, wordSlot, tagFormed, zeroStep,
    tagStep, access_reference_valid _ _ _ _ _ structReady, zeroForm, wordTagged, zeros,
    localAddress]

#print axioms struct_beside_word

end Tests.AggregateFields
