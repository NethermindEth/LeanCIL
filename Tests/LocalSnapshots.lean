import CIL.Safety.LocalSnapshots
import CIL.Safety.ConfinedSnapshots
import CIL.Safety.SymbolicExecution

/-! Remembered locals of every numeric kind, checked without an extraction: vector, int32,
    byte and narrow locals stay known across stores, overwrites, writes elsewhere, frame
    round trips and confined calls, so their loads step to the stored values; word stores
    carry across the bridges between `WordSnapshots` and `LocalSnapshots`. -/
namespace Tests.LocalSnapshots

open CIL.Safety

/-- A skipped slot does not acquire a byte home from numeric kind metadata alone. -/
theorem skipped_home_is_incomplete (memory : Memory) :
    WritableHomes memory 0 [.word64] [.root none] ∧
      ¬ CompleteWritableHomes memory 0 [.word64] [.root none] := by
  constructor
  · exact .skip (by intros; simp) (.nil _)
  · intro homes
    obtain ⟨reference, slot⟩ := homes.complete 0 .word64 rfl
    simp at slot

/-- A frame requesting unknown scalar and vector storage. -/
private def unknownMixedBody : CIL.Method :=
  { locals := [.unmodeled, .unmodeled], localKinds := [.word64, .vector256],
    code := [.ret], returnsValue := false }

/-- Actual uninitialized scalar and vector allocation supplies typed private homes. -/
theorem unknown_scalar_vector_homes (memory : Memory) (formed : memory.WellFormed) :
    ∃ frame entered scalar vector,
      enterFrame unknownMixedBody [] memory = .ok (frame, entered) ∧
      frame.locals[0]? = some (.bytes .word64 scalar) ∧
      frame.locals[1]? = some (.bytes .vector256 vector) ∧
      access entered scalar 8 1 true = .ok () ∧
      access entered vector 32 1 true = .ok () := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ := unknown_frame_setup unknownMixedBody rfl
    (by simp [unknownMixedBody]) (by simp [unknownMixedBody]) (by simp [unknownMixedBody])
    (by simp [unknownMixedBody]) (by simp [unknownMixedBody]) (by simp [unknownMixedBody])
    rfl rfl memory [] formed
  obtain ⟨scalar, scalarSlot, _, scalarAccess⟩ := homes.home_at 0 .word64 rfl
  obtain ⟨vector, vectorSlot, _, vectorAccess⟩ := homes.home_at 1 .vector256 rfl
  exact ⟨frame, entered, scalar, vector, setup, scalarSlot, vectorSlot,
    scalarAccess, vectorAccess⟩

/-- Initialized numeric storage exposes the same complete-home interface. -/
theorem initialized_homes_are_complete {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) :
    CompleteWritableHomes memory lower (numericKinds specs) slots := homes.complete

#print axioms skipped_home_is_incomplete
#print axioms unknown_scalar_vector_homes
#print axioms initialized_homes_are_complete

/-- A `.vector128` local followed by a `.word32` local. -/
abbrev vectorAndInt : List CIL.LocalKind := [.vector128, .word32]

/-- An int32 store, a write below the frame and a vector store keep both values, so each
    load pushes exactly what was stored. Without `after_write_apart` the int32 fact would be
    lost at the unrelated write. -/
theorem vector_and_int_survive {body : CIL.Method} {pc : Nat} {args stack : List Value}
    {frame : Frame} {entered start afterInt afterOther final : Memory} {boundary : Nat}
    {vectorHome intHome target : Reference} {bytes : List (BitVec 8)}
    (homes : WritableHomes entered boundary vectorAndInt frame.locals)
    (vectorSlot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[1]? = some (.bytes .word32 intHome))
    (vector : BitVec 128) (count : BitVec 32)
    (storeInt : write start intHome (numberBytes count.toNat 4) 1 = .ok afterInt)
    (callerWrite : write afterInt target bytes 1 = .ok afterOther)
    (belowFrame : target.allocation < boundary)
    (storeVector : write afterOther vectorHome (numberBytes vector.toNat 16) 1 = .ok final) :
    step body (.ldloc 0) pc args frame stack final =
        .ok (.next (pc + 1) (.scalar (.v128 vector) :: stack) frame final) ∧
      step body (.ldloc 1) pc args frame stack final =
        .ok (.next (pc + 1) (.scalar (.i32 count) :: stack) frame final) := by
  have intKnown := (LocalSnapshots.empty start frame.locals).after_write homes 1 .word32 intHome
    (.i32 count) count.toNat rfl intSlot storeInt
  have kept := intKnown.after_write_apart callerWrite fun index _ kind home _ slot => by
    have bound := homes.home_bound index kind home slot
    exact Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le belowFrame bound))
  have bothKnown := kept.after_write homes 0 .vector128 vectorHome (.v128 vector) vector.toNat
    rfl vectorSlot storeVector
  exact ⟨bothKnown.load (.v128 vector) rfl, bothKnown.load (.i32 count) rfl⟩

#print axioms vector_and_int_survive

/-- A zero vector local followed by a zero int32 local. -/
def zeroSpecs : List NumericLocalSpec :=
  [⟨.vector128, .v128 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩]

/-- A fresh numeric frame knows its initial vector; a checked int32 store steps, keeps that
    vector and remembers the stored int32. -/
theorem numeric_frame_store {body : CIL.Method} {pc : Nat} {args stack : List Value}
    {frame : Frame} {entered : Memory} {lower : Nat}
    (homes : NumericHomes entered lower zeroSpecs frame.locals) (formed : entered.WellFormed)
    (count : BitVec 32) :
    ∃ after,
      step body (.stloc 1) pc args frame (.scalar (.i32 count) :: stack) entered =
        .ok (.next (pc + 1) stack frame after) ∧
      step body (.ldloc 0) pc args frame stack after =
        .ok (.next (pc + 1) (.scalar (.v128 0) :: stack) frame after) ∧
      step body (.ldloc 1) pc args frame stack after =
        .ok (.next (pc + 1) (.scalar (.i32 count) :: stack) frame after) := by
  obtain ⟨intHome, intSlot, _, _, intReady⟩ := homes.home_at 1 ⟨.word32, .i32 0, 0, rfl⟩ rfl
  obtain ⟨after, stepped, known, _⟩ := homes.snapshots.store (body := body) (pc := pc)
    (args := args) (stack := stack) homes.writable formed .word32 intHome (.i32 count)
    count.toNat rfl intSlot intReady
  exact ⟨after, stepped, known.load (.v128 0) rfl, known.load (.i32 count) rfl⟩

#print axioms numeric_frame_store

/-- A narrow store remembers the extended value the CLI loads back, not the stored operand:
    the int32 `bits` comes back truncated to a byte and sign-extended. -/
theorem narrow_store_loads_extended {body : CIL.Method} {pc : Nat} {args stack : List Value}
    {frame : Frame} {entered start final : Memory} {boundary : Nat} {home : Reference}
    (homes : WritableHomes entered boundary [.narrow .signed8] frame.locals)
    (slot : frame.locals[0]? = some (.bytes (.narrow .signed8) home)) (bits : BitVec 32)
    (stored : write start home (numberBytes bits.toNat 1) 1 = .ok final) :
    step body (.ldloc 0) pc args frame stack final =
      .ok (.next (pc + 1) (.scalar (.i32 ((bits.setWidth 8).signExtend 32)) :: stack)
        frame final) :=
  ((LocalSnapshots.empty start frame.locals).after_write homes 0 (.narrow .signed8) home
    (.i32 bits) bits.toNat rfl slot stored).load _ rfl

#print axioms narrow_store_loads_extended

/-- A word stored through `WordSnapshots` loads as that `.i64` once viewed as locals: the
    view commutes with remembering the word. -/
theorem word_store_loads_as_local {body : CIL.Method} {pc index : Nat}
    {args stack : List Value} {frame : Frame} {entered before after : Memory}
    {boundary : Nat} {kinds} {known : Nat → Option (BitVec 64)} {home : Reference}
    (snapshots : WordSnapshots before frame.locals known)
    (homes : WritableHomes entered boundary kinds frame.locals) (formed : before.WellFormed)
    (word : BitVec 64) (slot : frame.locals[index]? = some (.bytes .word64 home))
    (written : write before home (numberBytes word.toNat 8) 1 = .ok after) :
    step body (.ldloc index) pc args frame stack after =
      .ok (.next (pc + 1) (.scalar (.i64 word) :: stack) frame after) := by
  have locals := (snapshots.after_write homes formed index home word slot written).toLocalSnapshots
  rw [wordLocals_rememberWord] at locals
  exact locals.load (.i64 word) (by simp [rememberLocal])

#print axioms word_store_loads_as_local

/-- A word store made through `LocalSnapshots` comes back as the same word store: both
    bridges commute with remembering. -/
theorem word_store_through_locals {entered before after : Memory} {boundary : Nat}
    {kinds slots} {known : Nat → Option (BitVec 64)} {home : Reference}
    (snapshots : WordSnapshots before slots known)
    (homes : WritableHomes entered boundary kinds slots) (index : Nat) (word : BitVec 64)
    (slot : slots[index]? = some (.bytes .word64 home))
    (written : write before home (numberBytes word.toNat 8) 1 = .ok after) :
    WordSnapshots after slots (rememberWord known index word) := by
  have stored := snapshots.toLocalSnapshots.after_write homes index .word64 home (.i64 word)
    word.toNat rfl slot written
  have words := stored.toWordSnapshots
  rwa [show localResult .word64 (.i64 word) = .i64 word from rfl, localWords_rememberLocal,
    localWords_wordLocals] at words

#print axioms word_store_through_locals

/-- A vector and an int32 local, each apart from every footprint entry, keep their values
    across a call confined to a carry and an output word. -/
theorem locals_survive_call {before after : Memory} {carry output vectorHome intHome : Reference}
    {known : Nat → Option CIL.Value}
    (snapshots :
      LocalSnapshots before [.bytes .vector128 vectorHome, .bytes .word32 intHome] known)
    (framed : Confined [(carry, 8), (output, 8)] before after) (formed : before.WellFormed)
    (vectorApart : ∀ entry ∈ [(carry, 8), (output, 8)], Apart vectorHome 16 entry)
    (intApart : ∀ entry ∈ [(carry, 8), (output, 8)], Apart intHome 4 entry) :
    LocalSnapshots after [.bytes .vector128 vectorHome, .bytes .word32 intHome] known :=
  snapshots.after_confined framed formed fun index _ _ _ _ slot => by
    rcases index with _ | _ | _ <;> simp at slot <;> obtain ⟨rfl, rfl⟩ := slot <;> assumption

#print axioms locals_survive_call

/-- One remembered vector local. -/
abbrev vectorKnown (vector : BitVec 128) : Nat → Option CIL.Value :=
  rememberLocal (fun _ => none) 0 (.v128 vector)

/-- Storing again to a remembered byte local replaces its value: the load pushes the second
    value, not the first. -/
theorem byte_overwrite_loads_latest {body : CIL.Method} {pc : Nat} {args stack : List Value}
    {frame : Frame} {entered start middle final : Memory} {boundary : Nat} {home : Reference}
    (homes : WritableHomes entered boundary [.byte] frame.locals)
    (slot : frame.locals[0]? = some (.bytes .byte home))
    (first : write start home (numberBytes 7 1) 1 = .ok middle)
    (second : write middle home (numberBytes 200 1) 1 = .ok final) :
    step body (.ldloc 0) pc args frame stack final =
      .ok (.next (pc + 1) (.scalar (.i32 200) :: stack) frame final) := by
  have once := (LocalSnapshots.empty start frame.locals).after_write homes 0 .byte home
    (.i32 7) 7 rfl slot first
  have twice := once.after_write homes 0 .byte home (.i32 200) 200 rfl slot second
  exact twice.load (.i32 200) rfl

#print axioms byte_overwrite_loads_latest

/-- Writes into the vector's own allocation, ending at its first byte or starting just past
    its last, keep it: apartness is by byte interval, not by allocation. -/
theorem vector_survives_neighbour_writes {start middle final : Memory} {home : Reference}
    {vector : BitVec 128} {first second : BitVec 8}
    (snapshots : LocalSnapshots start [.bytes .vector128 home] (vectorKnown vector))
    (room : 1 ≤ home.offset)
    (below : write start ⟨home.allocation, home.offset - 1⟩ [first] 1 = .ok middle)
    (above : write middle ⟨home.allocation, home.offset + 16⟩ [second] 1 = .ok final) :
    LocalSnapshots final [.bytes .vector128 home] (vectorKnown vector) := by
  have ends := snapshots.after_write_apart below fun index _ _ _ _ slot => by
    rcases index with _ | _ <;> simp at slot
    obtain ⟨rfl, rfl⟩ := slot
    exact Or.inr (Or.inr (by simp; omega))
  exact ends.after_write_apart above fun index _ _ _ _ slot => by
    rcases index with _ | _ <;> simp at slot
    obtain ⟨rfl, rfl⟩ := slot
    exact Or.inr (Or.inl (by simp [localWidth]))

#print axioms vector_survives_neighbour_writes

/-- A remembered local survives a callee's frame entry and exit, which keep every older
    allocation, and loads its value afterwards. -/
theorem vector_survives_callee_frame {body : CIL.Method} {pc : Nat} {args stack : List Value}
    {frame : Frame} {caller returned : Memory} {vector : BitVec 128}
    (snapshots : LocalSnapshots caller frame.locals (vectorKnown vector))
    (roundTrip : MemoryBelow caller.nextIdentity caller returned) (formed : caller.WellFormed) :
    step body (.ldloc 0) pc args frame stack returned =
      .ok (.next (pc + 1) (.scalar (.v128 vector) :: stack) frame returned) :=
  (snapshots.after_below roundTrip formed).load (.v128 vector) rfl

#print axioms vector_survives_callee_frame

/-- A write to another allocation keeps the vector through `after_unchanged`, which needs
    only retained authority and the home's unchanged bytes. -/
theorem vector_survives_unchanged_bytes {before after : Memory} {home target : Reference}
    {vector : BitVec 128} {bytes : List (BitVec 8)}
    (snapshots : LocalSnapshots before [.bytes .vector128 home] (vectorKnown vector))
    (formed : before.WellFormed) (written : write before target bytes 1 = .ok after)
    (separate : home.allocation ≠ target.allocation) :
    LocalSnapshots after [.bytes .vector128 home] (vectorKnown vector) :=
  snapshots.after_unchanged formed (write_preserves_access_below written _)
    fun index _ _ _ _ slot offset _ => by
      rcases index with _ | _ <;> simp at slot
      obtain ⟨_, rfl⟩ := slot
      exact write_outside _ _ _ _ _ _ _ written (Or.inl separate)

#print axioms vector_survives_unchanged_bytes

/-- A write onto the first byte of a remembered vector home is not apart from it, so
    `after_write_apart` cannot keep that snapshot. -/
theorem overlapping_write_not_apart (home : Reference) (byte : BitVec 8) :
    ¬ Apart home (localWidth .vector128) (home, [byte].length) := by
  simp [Apart, localWidth]

#print axioms overlapping_write_not_apart

/-- Loads a vector local and returns it. -/
@[cil_code] def loadVectorBody : CIL.Method := {
  code := [.ldloc 0, .ret], locals := [.v128 0], localKinds := [.vector128],
  returnsValue := true }

/-- The stepping tactics take a snapshot load as a supplied step fact, with no change to the
    tactics: the `.ldloc` step pushes the remembered vector. -/
theorem load_fact_steps (program : CIL.Program) (found : program[0]? = some loadVectorBody)
    (args : List Value) (frame : Frame) (memory : Memory) (vector : BitVec 128)
    (known : Nat → Option CIL.Value) (snapshots : LocalSnapshots memory frame.locals known)
    (specified : known 0 = some (.v128 vector)) (fuel : Nat) :
    run program (fuel + 1) 0 0 args frame [] memory =
      run program fuel 0 1 args frame [.scalar (.v128 vector)] memory := by
  cil_checked_steps [snapshots.load (.v128 vector) specified]

#print axioms load_fact_steps

-- Over symbolic memory the local has no known bytes, so the step needs the snapshot fact;
-- the lookup is the same one `load_fact_steps` closes.
set_option linter.unusedVariables false in
example (program : CIL.Program) (found : program[0]? = some loadVectorBody)
    (args : List Value) (frame : Frame) (memory : Memory) (vector : BitVec 128) (fuel : Nat)
    (stop : False) :
    run program (fuel + 1) 0 0 args frame [] memory =
      run program fuel 0 1 args frame [.scalar (.v128 vector)] memory := by
  fail_if_success cil_checked_steps
  exact stop.elim

end Tests.LocalSnapshots
