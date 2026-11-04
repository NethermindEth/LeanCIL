import CIL.Safety.LoopScaffold
import CIL.Safety.Execution

/-! Loop stepping over a struct local with the facts gathered by default, and the failures that
name the pc, the instruction and what is missing when a loop tactic cannot go on. -/

namespace Tests.LoopDiagnostics
open CIL.Safety
open CIL (W32)

/-- A struct of two 32-bit fields: `count` at offset 0 and `sum` at offset 4. -/
def layout : CIL.AggregateLayout := ⟨8, [⟨0, 4, false⟩, ⟨4, 4, false⟩]⟩

/-- The layout's fields are in bounds and apart. -/
theorem layout_valid : layout.Valid := by decide +kernel

/-- `for (t = default; t.count != value; t.count++) t.sum = addTwo(t.sum); return t.sum;` -/
@[cil_code] def tally : CIL.Method := {
  returnsValue := true, locals := [.aggregate (List.replicate 8 0)], localKinds := [.aggregate 8]
  code := [.localAddr 0, .initAggregate 8, .branch 14, .localAddr 0, .local 0, .fieldAt 4 4,
    .call 1 1, .setFieldAt 4 4, .localAddr 0, .local 0, .fieldAt 0 4, .const32 1, .add,
    .setFieldAt 0 4, .local 0, .fieldAt 0 4, .arg 0, .bne 3, .local 0, .fieldAt 4 4, .ret] }

/-- `return x + 2;` -/
@[cil_code] def addTwo : CIL.Method := {
  returnsValue := true, locals := [], code := [.arg 0, .const32 2, .add, .ret] }

/-- The program, with `tally` calling `addTwo` as method 1. -/
@[cil_code] def program : CIL.Program := [tally, addTwo]

/-- `addTwo` adds two and touches no memory. -/
def addTwoContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x + 2

theorem addTwo_holds : addTwoContract.Holds program 1 := by
  rintro x memory -
  dsimp only [addTwoContract]
  refine ⟨8, memory, _, ?_, Confined.refl _ memory, _, rfl, rfl⟩
  cil_checked_steps
#print axioms addTwo_holds

/-- The entered frame of `tally`. -/
bind_entry entry (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :=
  tally with [.scalar (.i32 value)] from memory allocating wellFormed

/-- The struct local, remembered by its field values `(count, sum)`. -/
abbrev State (memory : Memory) (home : Reference) :=
  FrameState [] memory [.aggregate 8] (W32 × W32) (fun _ => [.bytes (.aggregate 8) home])
    fun state => [some (.aggregate (layout.encode [.i32 state.1, .i32 state.2]))]

/-- The loop test, with the input and `count` on the stack. -/
bind_cutpoint header (memory : Memory) (value : W32) (home : Reference)
    (state : State memory home) :=
  tally matching (fun op => op matches .bne _) with entry.frame memory home,
    [.scalar (.i32 value), .scalar (.i32 state.values.1)], state.memory

/-- The frame lemmas compose by hand: the struct's zeroing and stores are named, the call is
    crossed with `after_confined`, and each path to the loop head is checked by `cil_loop_steps`
    with no facts passed. The loop doubles its input and allocates nothing the caller sees. -/
theorem doubles (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 value)] memory =
      .ok (final, [.scalar (.i32 (2 * value))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  refine invoke_loop_induction (by rfl) rfl setup (header memory value home)
    (fun state => state.values.2 = 2 * state.values.1)
    (fun state => (value - state.values.1).toNat) (fun start => ?_) ?_
  · obtain ⟨zeroed, zeroing, frame, -⟩ :=
      (entryFrame []).zero_aggregate 0 layout [.i32 0, .i32 0]
    exact loop_reaches_terminates (target := header memory value home ⟨(0, 0), zeroed, frame⟩)
      (by cil_loop_steps) (start _ rfl)
  rintro ⟨⟨count, sum⟩, current, frame⟩ doubled recurse
  dsimp only at doubled
  by_cases done : count = value
  · subst done
    rw [← doubled]
    cil_loop_finish
  · cil_loop_advance [done]
    apply loop_terminates_call addTwo_holds sum
    · rfl
    · cil_lookup []
    · cil_checked_step []
    · rfl
    · trivial
    rintro final _ ⟨_, invoked⟩ framed ⟨_, rfl, rfl⟩
    dsimp only [addTwoContract] at framed ⊢
    have called := frame.after_confined framed
      (invoke_preserves_wellFormed _ _ _ _ _ _ _ frame.wellFormed invoked) (by simp) (by simp)
    obtain ⟨summed, summing, summedFrame, -⟩ :=
      called.store_field 0 layout_valid 1 (.i32 (sum + 2))
    obtain ⟨counted, counting, countedFrame, -⟩ :=
      summedFrame.store_field 0 layout_valid 0 (.i32 (count + 1))
    refine loop_reaches_terminates (target := header memory value home
      ⟨(count + 1, sum + 2), counted, countedFrame⟩) (by cil_loop_steps) (recurse _ ?_ ?_)
    · show sum + 2 = 2 * (count + 1)
      rw [doubled]
      bv_omega
    · show (value - (count + 1)).toNat < (value - count).toNat
      bv_omega
#print axioms doubles

/-- By default the loop tactics take the struct's zeroing and stores through its frame, decide
    the branch from `count ≠ value`, and continue the call with the frame after it: the proof
    names no frame lemma, memory or step and supplies only the invariant and the arithmetic. -/
theorem doubles_by_default (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 value)] memory =
      .ok (final, [.scalar (.i32 (2 * value))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  refine invoke_loop_induction (by rfl) rfl setup (header memory value home)
    (fun state => state.values.2 = 2 * state.values.1)
    (fun state => (value - state.values.1).toNat) (fun start => ?_) ?_
  · cil_loop_recurse start (0, 0)
    rfl
  rintro ⟨⟨count, sum⟩, current, frame⟩ doubled recurse
  dsimp only at doubled
  by_cases done : count = value
  · subst done
    rw [← doubled]
    cil_loop_finish
  · cil_loop_advance
    cil_loop_call addTwo_holds sum
    cil_loop_recurse recurse (count + 1, sum + 2)
    · show sum + 2 = 2 * (count + 1)
      rw [doubled]
      bv_omega
    · show (value - (count + 1)).toNat < (value - count).toNat
      bv_omega
#print axioms doubles_by_default

-- Loop values that are not the reached head state's are refused, showing the reached state.
/-- error: cil_loop_recurse: the reached state is not the head of recurse at -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory : Memory) (value count sum : W32) (home : Reference) (current : Memory)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 count, .i32 sum]))]))
    (recurse : ∀ next : State memory home, LoopTerminates program 0 [.scalar (.i32 value)]
      (fun _ _ => True) (header memory value home next)) :
    LoopTerminates program 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨14, entry.frame memory home, [], current⟩ := by
  cil_loop_recurse recurse (count + 1, sum)

-- A store whose home has no frame fact at its memory stops the walk at that store.
/-- error: cil_loop_recurse: cannot step pc 7 (CIL.Op.setFieldAt 4 4) at memory
  final -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory : Memory) (value sum : W32) (home : Reference) (final : Memory)
    (recurse : ∀ next : State memory home, LoopTerminates program 0 [.scalar (.i32 value)]
      (fun _ _ => True) (header memory value home next)) :
    LoopTerminates program 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨7, entry.frame memory home, [.scalar (.i32 (sum + 2)), .reference (.address home)],
        final⟩ := by
  cil_loop_recurse recurse (0, sum + 2)

-- A contract applied before the loop reaches its call names the instruction it is at.
/-- error: cil_loop_call: pc 3 is CIL.Op.localAddr 0, not a call; step to the call first with
`cil_loop_advance` -/
#guard_msgs (whitespace := lax) in
example (memory : Memory) (value count sum : W32) (home : Reference) (current : Memory)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 count, .i32 sum]))])) :
    LoopTerminates program 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨3, entry.frame memory home, [], current⟩ := by
  cil_loop_call addTwo_holds sum

-- A call stops `cil_loop_steps`, which names the pc and the tactic that crosses it.
/-- error: cil_loop_steps: pc 6 is a call (CIL.Op.call 1 1); cross it with `cil_loop_call` -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory : Memory) (value count sum : W32) (home : Reference) (current : Memory)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 count, .i32 sum]))])) :
    LoopReaches program 0 [.scalar (.i32 value)] ⟨3, entry.frame memory home, [], current⟩
      ⟨15, entry.frame memory home, [], current⟩ := by
  cil_loop_steps

-- A store with no frame fact at its memory fails naming the pc, the instruction and the
-- memory, and what to supply.
/-- error: cil_loop_steps: cannot step pc 7 (CIL.Op.setFieldAt 4 4) at memory
  final -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory : Memory) (value sum : W32) (home : Reference) (final : Memory) :
    LoopReaches program 0 [.scalar (.i32 value)]
      ⟨7, entry.frame memory home, [.scalar (.i32 (sum + 2)), .reference (.address home)], final⟩
      ⟨15, entry.frame memory home, [], final⟩ := by
  cil_loop_steps

-- A path that comes back to the target's pc in another state names the differing part.
/-- error: cil_loop_steps: target state not matched at pc 17: -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) : True := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  obtain ⟨zeroed, zeroing, frame, -⟩ := (entryFrame []).zero_aggregate 0 layout [.i32 0, .i32 0]
  have : LoopReaches program 0 [.scalar (.i32 value)] ⟨0, entry.frame memory home, [], entered⟩
      (header memory (value + 1) home ⟨(0, 0), zeroed, frame⟩) := by
    cil_loop_steps
  trivial

-- A store whose field index is outside the layout has no field to write.
/-- error: could not synthesize default value for parameter 'found' using tactics -/
#guard_msgs (substring := true) in
example (memory current : Memory) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 0, .i32 0]))])) : True := by
  obtain ⟨-, -, -, -⟩ := frame.store_field 0 layout_valid 2 (.i32 1)
  trivial

-- A store of a value whose kind is not the field's width cannot encode the struct.
/-- error: Tactic `rfl` failed: The left-hand side
  fieldStoreNumber 4 (CIL.Value.i64 1) -/
#guard_msgs (substring := true) in
example (memory current : Memory) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 0, .i32 0]))])) : True := by
  obtain ⟨-, -, -, -⟩ := frame.store_field 0 layout_valid 0 (.i64 1)
  trivial

-- A by-value read of a field narrower than the value it lists cannot name the value.
/-- error: could not synthesize default value for parameter 'exact' using tactics -/
#guard_msgs (substring := true) in
example := step_fieldAt_encode layout_valid 0 [.i64 0, .i32 0]

/-- A struct of a flag byte at 0, a signed 16-bit count at 2, a 32-bit total at 4 and a nested
    8-byte struct at 8. -/
def mixed : CIL.AggregateLayout :=
  ⟨16, [⟨0, 1, false⟩, ⟨2, 2, false⟩, ⟨4, 4, false⟩, ⟨8, 8, true⟩]⟩

/-- The layout's fields are in bounds and apart. -/
theorem mixed_valid : mixed.Valid := by decide +kernel

-- Each field's zero is the value its kind loads from zeroed bytes: an int for the narrow and
-- 4-byte fields and zero bytes for the nested struct.
example : mixed.zeros = [.i32 0, .i32 0, .i32 0, .aggregate (List.replicate 8 0)] := rfl

/-- `s = default; while (s.flag == 0) s.flag = 1; return s.count;`, reading `flag` by value and
    the signed `count` through the struct's address. -/
@[cil_code] def flagged : CIL.Method := {
  returnsValue := true, locals := [.aggregate (List.replicate 16 0)], localKinds := [.aggregate 16]
  code := [.localAddr 0, .initAggregate 16, .branch 6, .localAddr 0, .const32 1, .setFieldAt 0 1,
    .local 0, .fieldAt 0 1, .brzero 3, .localAddr 0, .fieldAt 2 2 true, .ret] }

/-- The program of `flagged` alone. -/
@[cil_code] def flaggedProgram : CIL.Program := [flagged]

/-- The entered frame of `flagged`. -/
bind_entry flaggedEntry (memory : Memory) (wellFormed : memory.WellFormed) :=
  flagged with [] from memory allocating wellFormed

/-- The struct local, remembered by its `flag` field; the other fields stay zero. -/
abbrev Flagged (memory : Memory) (home : Reference) :=
  FrameState [] memory [.aggregate 16] W32 (fun _ => [.bytes (.aggregate 16) home])
    fun flag => [some (.aggregate (mixed.encode
      [.i32 flag, .i32 0, .i32 0, .aggregate (List.replicate 8 0)]))]

/-- The loop test, with nothing on the stack. -/
bind_cutpoint flaggedHeader (memory : Memory) (home : Reference) (state : Flagged memory home) :=
  flagged matching (fun op => op matches .local _) with flaggedEntry.frame memory home, [],
    state.memory

/-- `cil_loop_recurse` zeroes a struct with 1-, 2- and 4-byte and nested fields through its
    frame, stores the flag byte, and the loop tactics read the flag by value and the signed
    count through the address as narrow loads. -/
theorem flagged_returns_zero (memory : Memory) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke flaggedProgram fuel 0 [] memory = .ok (final, [.scalar (.i32 0)]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := flaggedEntry.checked memory wellFormed
  refine invoke_loop_induction (by rfl) rfl setup (flaggedHeader memory home)
    (fun state => state.values = 0 ∨ state.values = 1)
    (fun state => if state.values = 0 then 1 else 0) (fun start => ?_) ?_
  · cil_loop_recurse start 0
    exact Or.inl rfl
  rintro ⟨flag, current, frame⟩ (rfl | rfl) recurse
  · cil_loop_recurse recurse 1
    · exact Or.inr rfl
    · simp
  · cil_loop_finish
/-- info: 'Tests.LoopDiagnostics.flagged_returns_zero' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flagged_returns_zero

-- A zero claim that is not the layout's zeros is rejected: the nested struct's zero is its zero
-- bytes, not an int.
/-- error: could not synthesize default value for parameter 'zeroed' using tactics -/
#guard_msgs (substring := true) in
example (memory current : Memory) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 16] [.bytes (.aggregate 16) home]
      (knownLocals [none])) : True := by
  obtain ⟨-, -, -, -⟩ := frame.zero_aggregate 0 mixed [.i32 0, .i32 0, .i32 0, .i32 0]
  trivial

-- A zeroed flag byte holds zero, not one.
/-- error: could not synthesize default value for parameter 'zeroed' using tactics -/
#guard_msgs (substring := true) in
example (memory current : Memory) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 16] [.bytes (.aggregate 16) home]
      (knownLocals [none])) : True := by
  obtain ⟨-, -, -, -⟩ :=
    frame.zero_aggregate 0 mixed [.i32 1, .i32 0, .i32 0, .aggregate (List.replicate 8 0)]
  trivial

-- A narrow read of a 4-byte field is refused; that field reads back exactly.
/-- error: could not synthesize default value for parameter 'narrow' using tactics -/
#guard_msgs (substring := true) in
example := step_fieldAt_encode_narrow mixed_valid 2
  [.i32 0, .i32 0, .i32 7, .aggregate (List.replicate 8 0)]

-- A stored byte reads back truncated to its field: 0x1FF in the flag byte loads as 0xFF, and
-- as -1 signed.
example (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)
    (rest : List Value) :
    step body (.fieldAt 0 1 false) pc args frame (.scalar (.aggregate (mixed.encode
      [.i32 0x1FF, .i32 0, .i32 0, .aggregate (List.replicate 8 0)])) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 0xFF) :: rest) frame memory) ∧
    step body (.fieldAt 0 1 true) pc args frame (.scalar (.aggregate (mixed.encode
      [.i32 0x1FF, .i32 0, .i32 0, .aggregate (List.replicate 8 0)])) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (-1)) :: rest) frame memory) := by
  constructor <;> rw [step_fieldAt_encode_narrow mixed_valid 0 _] <;> rfl

/-- `s = default; while (s.total != value) s.total++; s.flag = 1; return s.flag;`, storing the
    flag byte on the exit path. -/
@[cil_code] def marked : CIL.Method := {
  returnsValue := true, locals := [.aggregate (List.replicate 16 0)], localKinds := [.aggregate 16]
  code := [.localAddr 0, .initAggregate 16, .branch 9, .localAddr 0, .local 0, .fieldAt 4 4,
    .const32 1, .add, .setFieldAt 4 4, .local 0, .fieldAt 4 4, .arg 0, .bne 3, .localAddr 0,
    .const32 1, .setFieldAt 0 1, .local 0, .fieldAt 0 1, .ret] }

/-- The program of `marked` alone. -/
@[cil_code] def markedProgram : CIL.Program := [marked]

/-- The entered frame of `marked`. -/
bind_entry markedEntry (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :=
  marked with [.scalar (.i32 value)] from memory allocating wellFormed

/-- The struct local, remembered by its `total` field; the other fields stay zero. -/
abbrev Marked (memory : Memory) (home : Reference) :=
  FrameState [] memory [.aggregate 16] W32 (fun _ => [.bytes (.aggregate 16) home])
    fun total => [some (.aggregate (mixed.encode
      [.i32 0, .i32 0, .i32 total, .aggregate (List.replicate 8 0)]))]

/-- The loop test, with the input and `total` on the stack. -/
bind_cutpoint markedHeader (memory : Memory) (value : W32) (home : Reference)
    (state : Marked memory home) :=
  marked matching (fun op => op matches .bne _) with markedEntry.frame memory home,
    [.scalar (.i32 value), .scalar (.i32 state.values)], state.memory

/-- `cil_loop_finish` takes a store on the exit path through the frame and returns the stored
    flag, leaving the frame of the stored memory. -/
theorem marked_returns_one (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke markedProgram fuel 0 [.scalar (.i32 value)] memory =
      .ok (final, [.scalar (.i32 1)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := markedEntry.checked memory value wellFormed
  refine invoke_loop_induction (by rfl) rfl setup (markedHeader memory value home)
    (fun _ => True) (fun state => (value - state.values).toNat) (fun start => ?_) ?_
  · cil_loop_recurse start 0
    trivial
  rintro ⟨total, current, frame⟩ - recurse
  by_cases done : total = value
  · subst done
    cil_loop_finish
  · cil_loop_recurse recurse (total + 1)
    · trivial
    · show (value - (total + 1)).toNat < (value - total).toNat
      bv_omega
/-- info: 'Tests.LoopDiagnostics.marked_returns_one' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms marked_returns_one

-- A remembered nested struct, spelled as `List.replicate`, still lets a 4-byte field read
-- by value step.
example (memory current : Memory) (value total : W32) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 16] [.bytes (.aggregate 16) home]
      (knownLocals [some (.aggregate (mixed.encode
        [.i32 0, .i32 0, .i32 total, .aggregate (List.replicate 8 0)]))])) :
    LoopReaches markedProgram 0 [.scalar (.i32 value)]
      ⟨9, markedEntry.frame memory home, [], current⟩
      ⟨11, markedEntry.frame memory home, [.scalar (.i32 total)], current⟩ := by
  cil_loop_steps

-- A docstring before `bind_entry` documents its checked entry, and before `bind_cutpoint` its
-- state.
/-- info: [some "The entered frame of `tally`. ",
  some "The loop test, with the input and `count` on the stack. "] -/
#guard_msgs (whitespace := lax) in
open Lean in
#eval show MetaM _ from do
  let env ← getEnv
  [``entry.checked, ``header].mapM fun name => liftM (findDocString? env name : IO _)

end Tests.LoopDiagnostics
