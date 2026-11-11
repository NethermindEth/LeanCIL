import CIL.Safety.LocalSnapshotSteps

/-!
# Snapshot-aware checked execution tests

Numeric stores and loads compose through one snapshot fact, with abstract local homes and
caller memory. Missing authority remains a proof obligation.
-/

namespace Tests.LocalSnapshotSteps

open CIL.Safety

/-- Store both inputs, read the vector, and return the stored int32. -/
@[cil_code] def storeBoth : CIL.Method := {
  code := [.arg 0, .setLocal 0, .arg 1, .setLocal 1, .local 0, .pop, .local 1, .ret]
  locals := [.v128 0, .i32 0], returnsValue := true }

/-- A single empty snapshot collection follows stores and reloads through the whole body. -/
theorem store_and_reload {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome intHome : Reference}
    (homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (formed : memory.WellFormed)
    (vectorSlot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[1]? = some (.bytes .word32 intHome))
    (vectorReady : access memory vectorHome 16 1 true = .ok ())
    (intReady : access memory intHome 4 1 true = .ok ())
    (vector : BitVec 128) (count : BitVec 32) :
    ∃ after, run [storeBoth] 9 0 0 [.scalar (.v128 vector), .scalar (.i32 count)]
      frame [] memory = .ok (after, [.scalar (.i32 count)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots) [vectorSlot, intSlot, vectorReady, intReady]

#print axioms store_and_reload

/-- Overwrite the vector after the int32 store, then reload both locals. -/
@[cil_code] def overwriteVector : CIL.Method := {
  code := [.arg 0, .setLocal 0, .arg 1, .setLocal 1, .arg 2, .setLocal 0,
    .local 1, .pop, .local 0, .ret]
  locals := [.v128 0, .i32 0], returnsValue := true }

/-- A later store replaces the remembered vector while preserving the int32 snapshot. -/
theorem overwrite_and_reload {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome intHome : Reference}
    (homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (formed : memory.WellFormed)
    (vectorSlot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[1]? = some (.bytes .word32 intHome))
    (vectorReady : access memory vectorHome 16 1 true = .ok ())
    (intReady : access memory intHome 4 1 true = .ok ())
    (first last : BitVec 128) (count : BitVec 32) :
    ∃ after, run [overwriteVector] 11 0 0
      [.scalar (.v128 first), .scalar (.i32 count), .scalar (.v128 last)] frame [] memory =
        .ok (after, [.scalar (.v128 last)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots) [vectorSlot, intSlot, vectorReady, intReady]

#print axioms overwrite_and_reload

/-- Keep a 256-bit vector across stores and reloads of a 128-bit vector and an int32. -/
@[cil_code] def mixedVectors : CIL.Method := {
  code := [.arg 0, .setLocal 0, .arg 1, .setLocal 1, .arg 2, .setLocal 2,
    .local 1, .pop, .local 2, .pop, .local 0, .ret]
  locals := [.v256 0, .v128 0, .i32 0], returnsValue := true }

/-- Different vector widths share one snapshot invariant and preserve the full wide value. -/
theorem mixed_vector_widths {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {wideHome vectorHome intHome : Reference}
    (homes : WritableHomes entered boundary [.vector256, .vector128, .word32] frame.locals)
    (formed : memory.WellFormed)
    (wideSlot : frame.locals[0]? = some (.bytes .vector256 wideHome))
    (vectorSlot : frame.locals[1]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[2]? = some (.bytes .word32 intHome))
    (wideReady : access memory wideHome 32 1 true = .ok ())
    (vectorReady : access memory vectorHome 16 1 true = .ok ())
    (intReady : access memory intHome 4 1 true = .ok ())
    (wide : BitVec 256) (vector : BitVec 128) (count : BitVec 32) :
    ∃ after, run [mixedVectors] 13 0 0
      [.scalar (.v256 wide), .scalar (.v128 vector), .scalar (.i32 count)] frame [] memory =
        .ok (after, [.scalar (.v256 wide)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots)
    [wideSlot, vectorSlot, intSlot, wideReady, vectorReady, intReady]

#print axioms mixed_vector_widths

/-- A compiled signed-byte local carries its narrow annotation on both instructions. -/
@[cil_code] def narrowLocal : CIL.Method := {
  code := [.arg 0, .setLocal 0 (some .signed8), .local 0 (some .signed8), .ret]
  locals := [.i32 0], localKinds := [.narrow .signed8], returnsValue := true }

/-- The snapshot remembers the truncated and extended value, not the original operand. -/
theorem narrow_round_trip {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {home : Reference}
    (homes : WritableHomes entered boundary [.narrow .signed8] frame.locals)
    (formed : memory.WellFormed)
    (slot : frame.locals[0]? = some (.bytes (.narrow .signed8) home))
    (ready : access memory home 1 1 true = .ok ()) (bits : BitVec 32) :
    ∃ after, run [narrowLocal] 5 0 0 [.scalar (.i32 bits)] frame [] memory =
      .ok (after, [.scalar (.i32 ((bits.setWidth 8).signExtend 32))]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots) [slot, ready]

#print axioms narrow_round_trip

/-- An isolated store has no later argument or load obligations. -/
@[cil_code] def storeOnly : CIL.Method := {
  code := [.setLocal 0, .ret], locals := [.v128 0], returnsValue := false }

/-- A snapshot collection grants no authority; adding exactly that authority permits the run. -/
theorem missing_authority {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome : Reference}
    (homes : WritableHomes entered boundary [.vector128] frame.locals)
    (formed : memory.WellFormed)
    (slot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (vector : BitVec 128) :
    access memory vectorHome 16 1 true = .ok () →
      ∃ after, run [storeOnly] 3 0 0 [] frame [.scalar (.v128 vector)] memory =
        .ok (after, []) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success (cil_strict (
    have : ∃ after,
      run [storeOnly] 3 0 0 [] frame [.scalar (.v128 vector)] memory = .ok (after, []) := by
      solve | cil_checked_steps (snapshots := snapshots) [slot]))
  intro ready
  cil_checked_steps (snapshots := snapshots) [slot, ready]

#print axioms missing_authority

/-- Write authority cannot justify storing an int32 into a vector home. -/
theorem wrong_local_kind {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome : Reference}
    (homes : WritableHomes entered boundary [.vector128] frame.locals)
    (formed : memory.WellFormed)
    (slot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (ready : access memory vectorHome 16 1 true = .ok ()) :
    ∃ after, run [storeOnly] 3 0 0 [] frame [.scalar (.v128 42)] memory = .ok (after, []) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success (cil_strict (
    have : ∃ after,
        run [storeOnly] 3 0 0 [] frame [.scalar (.i32 42)] memory = .ok (after, []) := by
      solve | cil_checked_steps (snapshots := snapshots) [slot, ready]))
  cil_checked_steps (snapshots := snapshots) [slot, ready]

#print axioms wrong_local_kind

/-- An isolated load returns exactly the remembered value. -/
@[cil_code] def loadOnly : CIL.Method := {
  code := [.local 0, .ret], locals := [.v128 0], returnsValue := true }

/-- An empty collection cannot justify a load; a supplied snapshot permits the same run. -/
theorem unknown_load (memory : Memory) (frame : Frame) (vector : BitVec 128) :
    LocalSnapshots memory frame.locals (rememberLocal (fun _ => none) 0 (.v128 vector)) →
      ∃ after, run [loadOnly] 3 0 0 [] frame [] memory = .ok (after, [.scalar (.v128 vector)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success (cil_strict (
    have : ∃ after,
      run [loadOnly] 3 0 0 [] frame [] memory = .ok (after, [.scalar (.v128 vector)]) := by
      solve | cil_checked_steps (snapshots := snapshots) []))
  intro known
  cil_checked_steps (snapshots := known) []

#print axioms unknown_load

/-- Mixed private homes include a narrowed byte and a vector addressed by vector opcodes. -/
@[cil_code] def mixedHomes : CIL.Method := {
  code := [.arg 0, .setLocal 0, .const32 0x1FF, .setLocal 1 (some .unsigned8),
    .arg 1, .setVectorLocal 2, .vectorLocal 2, .pop, .local 1 (some .unsigned8), .pop,
    .local 0, .ret]
  locals := [.i64 0, .i32 0, .v128 0]
  localKinds := [.word64, .narrow .unsigned8, .vector128], returnsValue := true }

/-- Complete homes expose opaque slots on demand; private writes retain caller evidence. -/
theorem mixed_homes_wp (memory : Memory) (slots : List LocalSlot) (boundary : Nat)
    (homes : CompleteWritableHomes memory boundary mixedHomes.localKinds slots)
    (inputs outputs : List ArgumentView) (valid : ValidCall memory inputs outputs)
    (word : BitVec 64) (vector : BitVec 128) :
    WP (Execution (fun fuel => run [mixedHomes] fuel 0 0
      [.scalar (.i64 word), .scalar (.v128 vector)] ⟨0, slots, [], [], 0⟩ [] memory))
      (fun result => result.2 = [.scalar (.i64 word)] ∧ ValidCall result.1 inputs outputs ∧
        MemoryBelow boundary memory result.1 ∧
        AccessBelow memory.nextIdentity memory result.1) := by
  have formed := valid.wellFormed
  have preserved := MemoryBelow.refl boundary memory
  have authority := (MemoryBelow.refl memory.nextIdentity memory).accessBelow
  have snapshots := LocalSnapshots.empty memory slots
  cil_contract_steps (snapshots := snapshots) []
  exact ⟨rfl, by assumption, by assumption, by assumption⟩

#print axioms mixed_homes_wp

/-- Supplied stores retain their chosen memory and can stop before the next instruction. -/
theorem supplied_store_until (before after : Memory) (frame : Frame) (vector : BitVec 128)
    (stored : step storeOnly (.setLocal 0) 0 [] frame [.scalar (.v128 vector)] before =
      .ok (.next 1 [] frame after))
    (_snapshots : LocalSnapshots before frame.locals (fun _ => none))
    (continuation : WP (Execution (fun fuel => run [storeOnly] fuel 0 1 [] frame [] after))
      (fun result => result.1 = leaveFrame frame after ∧ result.2 = [])) :
    WP (Execution (fun fuel => run [storeOnly] fuel 0 0 [] frame
      [.scalar (.v128 vector)] before))
      (fun result => result.1 = leaveFrame frame after ∧ result.2 = []) := by
  cil_contract_steps (snapshots := _snapshots) [stored] until continuation

#print axioms supplied_store_until

/-- The checked slot kind remains authoritative when the extracted store has an annotation. -/
theorem annotated_supplied_store (before after : Memory) (frame : Frame) (bits : BitVec 32)
    (stored : step narrowLocal (.setLocal 0) 1 [.scalar (.i32 bits)] frame
      [.scalar (.i32 bits)] before = .ok (.next 2 [] frame after))
    (continuation : WP (Execution (fun fuel => run [narrowLocal] fuel 0 2
      [.scalar (.i32 bits)] frame [] after)) (fun result => result.1 = leaveFrame frame after)) :
    WP (Execution (fun fuel => run [narrowLocal] fuel 0 1 [.scalar (.i32 bits)] frame
      [.scalar (.i32 bits)] before)) (fun result => result.1 = leaveFrame frame after) := by
  cil_contract_steps [stored] until continuation

#print axioms annotated_supplied_store

/-- Reduced literal operands match quantified checked stores without changing their memory. -/
theorem constructor_supplied_store (before after : Memory) (frame : Frame)
    (stored : ∀ (pc : Nat) (args rest : List Value),
      step narrowLocal (.setLocal 0) pc args frame (.scalar (.i32 0) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (continuation : WP (Execution (fun fuel => run [narrowLocal] fuel 0 2 [] frame [] after))
      (fun result => result.1 = leaveFrame frame after)) :
    WP (Execution (fun fuel => run [narrowLocal] fuel 0 1 [] frame
      [.scalar (.i32 {toFin := Fin.ofNat (2 ^ 32) 0})] before))
      (fun result => result.1 = leaveFrame frame after) := by
  cil_contract_steps [stored] until continuation

#print axioms constructor_supplied_store

/-- A named instruction exposes the same local lookup as a literal opcode. -/
def rememberedLoad : CIL.Op := .local 0

/-- Named generated instructions still consume the exact current snapshot. -/
theorem named_snapshot_load (memory : Memory) (frame : Frame) (bits : BitVec 32)
    (known : LocalSnapshots memory frame.locals (rememberLocal (fun _ => none) 0 (.i32 bits)))
    (body : CIL.Method) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some rememberedLoad)
    (continuation : WP (Execution (fun fuel =>
      run program fuel method 1 [] frame [.scalar (.i32 bits)] memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame [] memory))
      (fun _ => True) := by
  cil_contract_steps (snapshots := known) [found, instruction] until continuation

#print axioms named_snapshot_load

/-- A template body can remain named while its instruction lookup computes by reflexivity. -/
def rememberedBody : CIL.Method := narrowLocal

/-- Computed code lookups determine the opcode before snapshot premises are inspected. -/
theorem computed_snapshot_load (memory : Memory) (frame : Frame) (bits : BitVec 32)
    (known : LocalSnapshots memory frame.locals (rememberLocal (fun _ => none) 0 (.i32 bits)))
    (program : CIL.Program) (method : Nat) (found : program[method]? = some rememberedBody)
    (continuation : WP (Execution (fun fuel =>
      run program fuel method 3 [] frame [.scalar (.i32 bits)] memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 2 [] frame [] memory))
      (fun _ => True) := by
  cil_contract_steps (snapshots := known) [found] until continuation

#print axioms computed_snapshot_load

/-- A finite remembered range can start at a symbolic local index. -/
def rangedValues (base : Nat) (words : Fin 4 → BitVec 64) : Nat → Option CIL.Value :=
  fun index => if ready : base ≤ index ∧ index - base < 4 then
    some (.i64 (words ⟨index - base, ready.2⟩)) else none

/-- Indexed snapshot lookups simplify the offset while retaining the symbolic limb value. -/
theorem symbolic_snapshot_index (memory : Memory) (frame : Frame) (base : Nat)
    (words : Fin 4 → BitVec 64)
    (known : LocalSnapshots memory frame.locals (rangedValues base words))
    (body : CIL.Method) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some (.local (base + 1)))
    (continuation : WP (Execution (fun fuel =>
      run program fuel method 1 [] frame [.scalar (.i64 (words 1))] memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame [] memory))
      (fun _ => True) := by
  cil_contract_steps (snapshots := known) [found, instruction, rangedValues] until continuation

#print axioms symbolic_snapshot_index

/-- An annotated supplied fact also applies to the same checked store without an annotation. -/
theorem annotated_fact_to_plain (before after : Memory) (frame : Frame) (vector : BitVec 128)
    (stored : step storeOnly (.setLocal 0 (some .unsigned8)) 0 [] frame
      [.scalar (.v128 vector)] before = .ok (.next 1 [] frame after))
    (continuation : WP (Execution (fun fuel => run [storeOnly] fuel 0 1 [] frame [] after))
      (fun result => result.1 = leaveFrame frame after)) :
    WP (Execution (fun fuel => run [storeOnly] fuel 0 0 [] frame
      [.scalar (.v128 vector)] before)) (fun result => result.1 = leaveFrame frame after) := by
  cil_contract_steps [stored] until continuation

#print axioms annotated_fact_to_plain

/-- An empty snapshot collection grants neither a readable value nor permission to write. -/
theorem wp_unknown_load (memory : Memory) (frame : Frame) (vector : BitVec 128)
    (known : LocalSnapshots memory frame.locals
      (rememberLocal (fun _ => none) 0 (.v128 vector))) :
    WP (Execution (fun fuel => run [loadOnly] fuel 0 0 [] frame [] memory))
      (fun result => result.2 = [.scalar (.v128 vector)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success (clear known; cil_contract_steps (snapshots := snapshots) [])
  cil_contract_steps (snapshots := known) []
  rfl

#print axioms wp_unknown_load

/-- Complete byte homes are still required when the physical slot list is opaque. -/
theorem wp_missing_authority (memory : Memory) (frame : Frame) (vector : BitVec 128)
    (formed : memory.WellFormed)
    (homes : CompleteWritableHomes memory 0 [.vector128] frame.locals) :
    WP (Execution (fun fuel => run [storeOnly] fuel 0 0 [] frame
      [.scalar (.v128 vector)] memory)) (fun result => result.2 = []) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success (clear homes; cil_contract_steps (snapshots := snapshots) [])
  cil_contract_steps (snapshots := snapshots) []
  rfl

#print axioms wp_missing_authority

/-- Initialized numeric homes also supply opaque slots, and byte loads retain signed extension. -/
theorem numeric_narrow_wp (memory : Memory) (frame : Frame) (bits : BitVec 32)
    (homes : NumericHomes memory 0 [⟨.narrow .signed8, .i32 0, 0, rfl⟩] frame.locals)
    (formed : memory.WellFormed) :
    WP (Execution (fun fuel => run [narrowLocal] fuel 0 0 [.scalar (.i32 bits)]
      frame [] memory))
      (fun result => result.2 = [.scalar (.i32 ((bits.setWidth 8).signExtend 32))]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_contract_steps (snapshots := snapshots) []
  rfl

#print axioms numeric_narrow_wp

end Tests.LocalSnapshotSteps
