import CIL.Safety.LocalSnapshots
import CIL.Safety.ConfinedSnapshots
import CIL.Safety.SymbolicExecution

/-! Remembered locals of every numeric kind, checked without an extraction: vector and int32
    locals stay known across stores, writes elsewhere and confined calls, so their loads step
    to the stored values. -/
namespace Tests.LocalSnapshots

open CIL.Safety

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
    step body (.local 0) pc args frame stack final =
        .ok (.next (pc + 1) (.scalar (.v128 vector) :: stack) frame final) ∧
      step body (.local 1) pc args frame stack final =
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
      step body (.setLocal 1) pc args frame (.scalar (.i32 count) :: stack) entered =
        .ok (.next (pc + 1) stack frame after) ∧
      step body (.local 0) pc args frame stack after =
        .ok (.next (pc + 1) (.scalar (.v128 0) :: stack) frame after) ∧
      step body (.local 1) pc args frame stack after =
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
    step body (.local 0) pc args frame stack final =
      .ok (.next (pc + 1) (.scalar (.i32 ((bits.setWidth 8).signExtend 32)) :: stack)
        frame final) :=
  ((LocalSnapshots.empty start frame.locals).after_write homes 0 (.narrow .signed8) home
    (.i32 bits) bits.toNat rfl slot stored).load _ rfl

#print axioms narrow_store_loads_extended

/-- Words convert to locals and back without losing an entry, and a word store commutes with
    the conversion. -/
theorem word_round_trip {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option (BitVec 64)} (snapshots : WordSnapshots memory slots known)
    (index : Nat) (word : BitVec 64) :
    WordSnapshots memory slots known ∧
      wordLocals (rememberWord known index word) =
        rememberLocal (wordLocals known) index (.i64 word) := by
  have back := snapshots.toLocalSnapshots.toWordSnapshots
  have same : localWords (wordLocals known) = known := by
    funext other
    cases present : known other <;> simp [localWords, wordLocals, present]
  exact ⟨same ▸ back, wordLocals_rememberWord known index word⟩

#print axioms word_round_trip

/-- A vector local in its own allocation keeps its value across a call confined to a
    carry word elsewhere. -/
theorem vector_survives_call {before after : Memory} {carry home : Reference}
    {vector : BitVec 128}
    (snapshots : LocalSnapshots before [.bytes .vector128 home]
      (rememberLocal (fun _ => none) 0 (.v128 vector)))
    (framed : Confined [(carry, 8)] before after) (formed : before.WellFormed)
    (separate : home.allocation ≠ carry.allocation) :
    LocalSnapshots after [.bytes .vector128 home]
      (rememberLocal (fun _ => none) 0 (.v128 vector)) :=
  snapshots.after_confined framed formed fun index _ _ _ _ slot entry member => by
    rcases index with _ | _ <;> simp at slot member
    obtain ⟨_, rfl⟩ := slot
    subst member
    exact Or.inl separate

#print axioms vector_survives_call

/-- A write onto the first byte of a remembered vector home is not apart from it, so
    `after_write_apart` cannot keep that snapshot. -/
theorem overlapping_write_not_apart (home : Reference) (byte : BitVec 8) :
    ¬ (home.allocation ≠ home.allocation ∨ home.offset + localWidth .vector128 ≤ home.offset ∨
      home.offset + [byte].length ≤ home.offset) := by
  simp [localWidth]

#print axioms overlapping_write_not_apart

/-- Loads a vector local and returns it. -/
@[cil_code] def loadVectorBody : CIL.Method := {
  code := [.local 0, .ret], locals := [], returnsValue := true }

/-- The stepping tactics take a snapshot load as a supplied step fact, with no change to the
    tactics: the `.local` step pushes the remembered vector. -/
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
