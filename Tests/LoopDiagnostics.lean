import CIL.Safety.LoopScaffold
import CIL.Safety.Execution
import CIL.Observe

/-! Loop stepping over a struct local, and over an int local and a call through a contract with
a footprint in a caller buffer, with the facts gathered by default, and the failures that name
the pc, the instruction and what is missing when a loop tactic cannot go on, and what the
observer of `CIL.Observe` reports of them. -/

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
    names no frame lemma, memory or step and supplies only the invariant and the arithmetic,
    each selected by the tag `cil_loop_recurse` gives it. -/
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
    case measure =>
      show (value - (count + 1)).toNat < (value - count).toNat
      bv_omega
    case invariant =>
      show sum + 2 = 2 * (count + 1)
      rw [doubled]
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

/-- `cil_loop_advance` takes the same exit-path store and stops at the return, which
    `cil_loop_finish` then proves. -/
theorem marked_advances_to_return (memory : Memory) (value : W32)
    (wellFormed : memory.WellFormed) :
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
    cil_loop_advance
    -- The store is taken: the walk is at the return, with the stored flag on the stack.
    show LoopTerminates markedProgram 0 [.scalar (.i32 total)] _
      ⟨18, _, [.scalar (.i32 1#32)], _⟩
    cil_loop_finish
  · cil_loop_recurse recurse (total + 1)
    · trivial
    · show (value - (total + 1)).toNat < (value - total).toNat
      bv_omega
/-- info: 'Tests.LoopDiagnostics.marked_advances_to_return' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms marked_advances_to_return

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

/-- `for (i = 0; i != n; i++) stamp(Unsafe.Add(ref p, i), i); return i;`, with `i` an int local. -/
@[cil_code] def stamps : CIL.Method := {
  returnsValue := true, locals := [.i32 0], localKinds := [.word32]
  code := [.const32 0, .setLocal 0, .branch 12, .arg 1, .local 0, .memory (.add 4 true),
    .local 0, .call 1 2, .local 0, .const32 1, .add, .setLocal 0, .local 0, .arg 0, .bne 3,
    .local 0, .ret] }

/-- `*slot = value;` -/
@[cil_code] def stamp : CIL.Method := {
  returnsValue := false, locals := [], code := [.arg 0, .arg 1, .storeScalar 4, .ret] }

/-- The program, with `stamps` calling `stamp` as method 1. -/
@[cil_code] def stampsProgram : CIL.Program := [stamps, stamp]

/-- `stamp` writes the word at `slot`, given write authority over it, and nothing else. -/
def stampContract : MethodContract (Reference × W32) Unit where
  args input := [.reference (.address input.1), .scalar (.i32 input.2)]
  results _ := []
  pre input memory := Writable memory input.1 4 0 1
  footprint input := [(input.1, 4)]
  post input _ final _ := Contents final input.1 4 [input.2]

/-- `stamp` meets its contract, through the width-generic store and write lemmas. -/
theorem stamp_holds : stampContract.Holds stampsProgram 1 := by
  rintro ⟨slot, value⟩ memory writable
  dsimp only [stampContract] at writable ⊢
  obtain ⟨after, wrote, formed, confined, filled⟩ := writable.write_one value
  refine ⟨8, after, [], ?_, confined, (), rfl, filled⟩
  cil_checked_steps [step_storeScalar_of_write wrote, formed]
/-- info: 'Tests.LoopDiagnostics.stamp_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stamp_holds

/-- The entered frame of `stamps`. -/
bind_entry stampsEntry (memory : Memory) (count : W32) (buffer : Reference)
    (wellFormed : memory.WellFormed) :=
  stamps with [.scalar (.i32 count), .reference (.address buffer)] from memory
    allocating wellFormed

/-- The index local, over the caller's buffer of `count` words. -/
abbrev Stamping (memory : Memory) (buffer : Reference) (count : Nat) (home : Reference) :=
  FrameState [(buffer, 4 * count)] memory [.word32] W32 (fun _ => [.bytes .word32 home])
    fun index => [some (.i32 index)]

/-- The loop test, with the count and the index on the stack. -/
bind_cutpoint stampsHeader (memory : Memory) (count : W32) (buffer : Reference)
    (home : Reference) (state : Stamping memory buffer count.toNat home) :=
  stamps matching (fun op => op matches .bne _) with stampsEntry.frame memory home,
    [.scalar (.i32 count), .scalar (.i32 state.values)], state.memory

/-- The index stays within the count, and the rest of the buffer stays writable. -/
def StampingInvariant (count : W32) (buffer : Reference) {memory : Memory} {home : Reference}
    (state : Stamping memory buffer count.toNat home) : Prop :=
  state.values.toNat ≤ count.toNat ∧
    Writable state.memory buffer 4 state.values.toNat (count.toNat - state.values.toNat)

/-- The loop tactics take the int local's stores through its frame, carry the `Unsafe.Add`
    result and the formed buffer from the caller's memory to each frame memory, cross the call
    with the frame after it from the index bound, and carry the buffer's write authority along:
    the proof states only the invariant, the arithmetic and the caller's facts. -/
theorem stamps_returns_count (memory : Memory) (count : W32) (buffer : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (small : count.toNat < 2 ^ 31) (writable : Writable memory buffer 4 0 count.toNat) :
    ∃ fuel final, invoke stampsProgram fuel 0
        [.scalar (.i32 count), .reference (.address buffer)] memory =
      .ok (final, [.scalar (.i32 count)]) ∧
      Confined [(buffer, 4 * count.toNat)] memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ :=
    stampsEntry.checked memory count buffer wellFormed
  refine invoke_loop_induction (by rfl) ?_ setup (stampsHeader memory count buffer home)
    (StampingInvariant count buffer) (fun state => count.toNat - state.values.toNat)
    (fun start => ?_) ?_
  · simp [cil_checked, formed]
  · cil_loop_recurse start 0
    exact ⟨by simp, by simpa using writable⟩
  rintro ⟨index, current, frame⟩ ⟨bounded, rest⟩ recurse
  dsimp only at bounded rest
  by_cases done : index = count
  · subst done
    cil_loop_finish
  · have lower : index.toNat < count.toNat := by
      have := BitVec.toNat_ne.mp done
      omega
    have offset := writable.add_int wellFormed formed (index := index) (by omega) (by omega)
      (by omega)
    have slot := rest.sub (index := index.toNat) (length := 1) (by omega) (by omega)
    cil_loop_advance
    cil_loop_call stamp_holds (buffer.element 4 index.toNat, index)
    have next : (index + 1).toNat = index.toNat + 1 := by bv_omega
    cil_loop_recurse recurse (index + 1)
    case invariant =>
      refine ⟨show (index + 1).toNat ≤ count.toNat by omega, ?_⟩
      have later := (Writable.append (left := 1)).mp
        (show Writable _ buffer 4 index.toNat (1 + (count.toNat - (index.toNat + 1))) by
          rwa [show 1 + (count.toNat - (index.toNat + 1)) = count.toNat - index.toNat by omega])
      rw [next]
      simpa [Nat.add_comm] using later.2
    case measure =>
      dsimp only
      omega
/-- info: 'Tests.LoopDiagnostics.stamps_returns_count' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stamps_returns_count

-- Without the `Unsafe.Add` result the advance stops at the add, naming that fact.
/-- error: cil_loop_advance: cannot step pc 5 (CIL.Op.memory (CIL.MemoryOp.add 4 true)) -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (count index : W32) (buffer home : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)])) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance

-- The stuck step shows its pc as a literal, as the message's first line does.
/-- (CIL.Op.memory (CIL.MemoryOp.add 4 true)) 5 -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (count index : W32) (buffer home : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)])) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance

-- The hint for a stuck step names the fact its residual is missing.
/-- info: the `Unsafe.Add` result: `add memory base width offset = .ok reference` at this memory or
the caller's, such as `Writable.add_int` -/
#guard_msgs (whitespace := lax) in
open Lean Meta in
#eval show MetaM Unit from do logInfo (← loopMissingHint #[mkConst ``CIL.Safety.add])

-- A residual that mentions no checked fact gets the general hint.
/-- info: a `LoopFrame` at this memory for a local, or the step equation of a store with this
stack -/
#guard_msgs (whitespace := lax) in
open Lean Meta in
#eval show MetaM Unit from do logInfo (← loopMissingHint #[mkConst ``True])

/-- `i = (byte) 0x1FF; return i;`, storing the int local through a byte narrowing. -/
@[cil_code] def narrowed : CIL.Method := {
  returnsValue := true, locals := [.i32 0], localKinds := [.word32]
  code := [.const32 0x1FF, .setLocal 0 (some .unsigned8), .local 0, .ret] }

/-- The program of `narrowed` alone. -/
@[cil_code] def narrowedProgram : CIL.Program := [narrowed]

/-- The entered frame of `narrowed`. -/
bind_entry narrowedEntry (memory : Memory) (wellFormed : memory.WellFormed) :=
  narrowed with [] from memory allocating wellFormed

-- A narrowing local store is not one `LoopFrame.store` models, so the walk stops at it.
/-- error: cil_loop_finish: cannot step pc 1 (CIL.Op.setLocal 0 (some CIL.NarrowKind.unsigned8)) -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (home : Reference)
    (frame : LoopFrame [] memory current [.word32] [.bytes .word32 home]
      (knownLocals [some (.i32 0)])) :
    LoopTerminates narrowedProgram 0 [] (fun _ _ => True)
      ⟨0, narrowedEntry.frame memory home, [], current⟩ := by
  cil_loop_finish

-- Without the index bound the callee's slot is not shown inside the frame's footprint, and
-- the call fails naming that side condition.
/-- error: cil_loop_call: the frame after the call needs each callee footprint entry inside the
frame's footprint, which the facts do not prove: -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (count index : W32) (buffer home slotted : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)]))
    (offset : add memory buffer 4 (BitVec.ofInt 64 index.toInt) =
      .ok (buffer.element 4 index.toNat))
    (slot : Writable current (buffer.element 4 index.toNat) 4 0 1) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance
  cil_loop_call stamp_holds (buffer.element 4 index.toNat, index)

-- A call whose address argument has no `form` fact does not step, and the failure names the
-- check and the fact it needs.
/-- error: cil_loop_call: the call at pc 7 (CIL.Op.call 1 2) does not step: its argument checks
reduce to -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (count index : W32) (home slotted : Reference)
    (frame : LoopFrame [] memory current [.word32] [.bytes .word32 home]
      (knownLocals [some (.i32 index)])) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address slotted)]
      (fun _ _ => True)
      ⟨7, stampsEntry.frame memory home, [.scalar (.i32 index), .reference (.address slotted)],
        current⟩ := by
  cil_loop_call stamp_holds (slotted, index)

-- At the return, `cil_loop_finish` closes the conjuncts the exit facts prove, here the results
-- and the caller's confinement, and hands back the rest, each tagged by its place among all the
-- conjuncts, which stays put whichever others close.
example (memory : Memory) (count : W32) (buffer home : Reference) (current : Memory)
    (stored : ∀ final, Contents final buffer 4 [count])
    (setup : enterFrame stamps [.scalar (.i32 count), .reference (.address buffer)] memory =
      .ok (stampsEntry.frame memory home, current))
    (frame : LoopFrame [(buffer, 4)] memory current [.word32] [.bytes .word32 home]
      (knownLocals [some (.i32 count)])) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun final results => (results = [.scalar (.i32 count)] ∧
        Confined [(buffer, 4)] memory final) ∧ Contents final buffer 4 [count])
      ⟨15, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_finish
  case postcondition.part3 => exact stored _

-- A call whose stacked argument is not the contract's names both.
/-- error: cil_loop_call: the call at pc 7 (CIL.Op.call 1 2) does not take the contract's
arguments for this input, or is not the named site. -/
#guard_msgs (whitespace := lax, substring := true) in
example (memory current : Memory) (count index : W32) (buffer home : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)]))
    (offset : add memory buffer 4 (BitVec.ofInt 64 index.toInt) =
      .ok (buffer.element 4 index.toNat)) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance
  cil_loop_call stamp_holds (buffer, index)

/-- `stamp`'s method index, named as `bind_callee` names a callee. -/
def stampMethod : Nat := 1

/-- `stamp_holds` at the named callee, whose precondition goals take its name. -/
theorem stampMethod_holds : stampContract.Holds stampsProgram stampMethod := stamp_holds
/-- info: 'Tests.LoopDiagnostics.stampMethod_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stampMethod_holds

/-- The callee's precondition that no hypothesis states is left tagged with the callee, ahead of
    the continuing loop goal, which keeps its own tag. -/
example (memory current : Memory) (count index : W32) (buffer home : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (bound : index.toNat < count.toNat)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)]))
    (offset : add memory buffer 4 (BitVec.ofInt 64 index.toInt) =
      .ok (buffer.element 4 index.toNat))
    (slot : 0 < 1 → Writable current (buffer.element 4 index.toNat) 4 0 1)
    (later : ∀ state, LoopTerminates stampsProgram 0
      [.scalar (.i32 count), .reference (.address buffer)] (fun _ _ => True) state) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance
  cil_loop_call stampMethod_holds (buffer.element 4 index.toNat, index)
  case precondition.stampMethod => exact slot Nat.one_pos
  exact later _

-- A loop tactic handed a tagged obligation instead of a loop path names that obligation.
/-- error: cil_loop_advance: expected a `LoopReaches` or `LoopTerminates` goal
The main goal is the `precondition.stampMethod` obligation; close it first, as
`case precondition.stampMethod => ...`. -/
#guard_msgs (whitespace := lax) in
example (memory current : Memory) (count index : W32) (buffer home : Reference)
    (wellFormed : memory.WellFormed) (formed : form memory buffer = .ok buffer)
    (bound : index.toNat < count.toNat)
    (frame : LoopFrame [(buffer, 4 * count.toNat)] memory current [.word32]
      [.bytes .word32 home] (knownLocals [some (.i32 index)]))
    (offset : add memory buffer 4 (BitVec.ofInt 64 index.toInt) =
      .ok (buffer.element 4 index.toNat)) :
    LoopTerminates stampsProgram 0 [.scalar (.i32 count), .reference (.address buffer)]
      (fun _ _ => True) ⟨3, stampsEntry.frame memory home, [], current⟩ := by
  cil_loop_advance
  cil_loop_call stampMethod_holds (buffer.element 4 index.toNat, index)
  cil_loop_advance

open Lean Elab Command in
/-- Elaborate `command`, which must fail, and fail unless its errors list each of `tags` in
    backticks: the tags Lean's unknown-case hint offers, whatever wording surrounds them. -/
elab "#guard_offered_tags " tags:ident* " in " command:command : command => do
  let before := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand (← `(command| set_option Elab.async false in $command))
  let errors := (← get).messages.toList.filter (·.severity == .error)
  modify fun state => { state with messages := before }
  let texts ← errors.mapM fun error => error.data.toString
  if texts.isEmpty then throwError "#guard_offered_tags: the command did not fail"
  for tag in tags do
    let shown := s!"`{tag.getId}`"
    unless texts.any (·.contains shown) do
      throwError "#guard_offered_tags: no error offers {shown}:\n{String.intercalate "\n" texts}"

-- A mistyped obligation is Lean's unknown case, which offers the tags the recursion left.
#guard_offered_tags invariant measure in
example (memory current : Memory) (value total : W32) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 16] [.bytes (.aggregate 16) home]
      (knownLocals [some (.aggregate (mixed.encode
        [.i32 0, .i32 0, .i32 total, .aggregate (List.replicate 8 0)]))]))
    (recurse : ∀ next : Marked memory home, True →
      (value - next.values).toNat < (value - total).toNat →
      LoopTerminates markedProgram 0 [.scalar (.i32 value)] (fun _ _ => True)
        (markedHeader memory value home next)) :
    LoopTerminates markedProgram 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨3, markedEntry.frame memory home, [], current⟩ := by
  cil_loop_recurse recurse (total + 1)
  case invariants => trivial

/-- A head hypothesis of three conditions leaves the invariant's two parts numbered and the
    measure's decrease last, each selected by its tag, the first also by the bare prefix. -/
example (memory current : Memory) (value total : W32) (home : Reference)
    (frame : LoopFrame [] memory current [.aggregate 16] [.bytes (.aggregate 16) home]
      (knownLocals [some (.aggregate (mixed.encode
        [.i32 0, .i32 0, .i32 total, .aggregate (List.replicate 8 0)]))]))
    (recurse : ∀ next : Marked memory home, next.values = total + 1 → True →
      next.values ≠ total →
      LoopTerminates markedProgram 0 [.scalar (.i32 value)] (fun _ _ => True)
        (markedHeader memory value home next)) :
    LoopTerminates markedProgram 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨3, markedEntry.frame memory home, [], current⟩ := by
  cil_loop_recurse recurse (total + 1)
  case measure => exact fun same => by bv_omega
  case invariant.part2 => trivial
  case invariant => rfl

/-! ## Observing the loop tactics

The observer of `CIL.Observe`, silent without its options, traces each step under
`trace.CIL.step` from the proof term and records each failure under `cil.diagnostics`. -/

set_option hygiene false in
/-- The walk from the entry to the loop head, through the struct's zeroing and the branch. -/
macro "walk_to_head" : tactic => `(tactic| (
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  obtain ⟨zeroed, zeroing, frame, -⟩ :=
    (entryFrame []).zero_aggregate 0 layout [.i32 0, .i32 0]
  have : LoopReaches program 0 [.scalar (.i32 value)] ⟨0, entry.frame memory home, [], entered⟩
      (header memory value home ⟨(0, 0), zeroed, frame⟩) := by
    cil_loop_steps
  trivial))

-- Imported but with neither option set, the observer prints nothing.
#guard_msgs in
example (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) : True := by
  walk_to_head

-- A step names each hypothesis its step proof used: the zeroing fact steps `initAggregate`.
/-- [CIL.step] pc 1: CIL.Op.initAggregate (8 % 2 ^ 64)
  source: unknown, since the proof does not import ExtractedSymbols
  by loop_reaches_next
  used zeroing : -/
#guard_msgs (whitespace := lax, substring := true) in
set_option trace.CIL.step true in
example (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) : True := by
  walk_to_head

-- A branch uses no hypothesis, so no fact is named although `setup` and `wellFormed` are in
-- context; the tactic's summary names the goals it left by obligation tag.
/-- [CIL.step] pc 2: CIL.Op.branch 14
  source: unknown, since the proof does not import ExtractedSymbols
  by loop_reaches_next
  changes pc: 1 + 1 ⟶ 14 -/
#guard_msgs (whitespace := lax, substring := true) in
set_option trace.CIL.step true in
example (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) : True := by
  walk_to_head

-- `cil_checked_steps` is traced the same way, through `run_next` and `run_return`.
/-- [CIL.step] cil_checked_steps took 4 steps; goals left: none -/
#guard_msgs (whitespace := lax, substring := true) in
set_option trace.CIL.step true in
example : addTwoContract.Holds program 1 := by
  rintro x memory -
  dsimp only [addTwoContract]
  refine ⟨8, memory, _, ?_, Confined.refl _ memory, _, rfl, rfl⟩
  cil_checked_steps

-- A step taken by hand, outside any LeanCIL tactic, is traced at its tactic block.
/-- taken outside a LeanCIL tactic -/
#guard_msgs (whitespace := lax, substring := true) in
set_option trace.CIL.step true in
example (memory : Memory) (value : W32) (frame : Frame) :
    run program 100 1 0 [.scalar (.i32 value)] frame [] memory =
      run program 99 1 1 [.scalar (.i32 value)] frame [.scalar (.i32 value)] memory := by
  exact run_next (by cil_lookup []) (by cil_lookup []) (by cil_checked_step [])

-- A call tactic applied before the walk reaches a call records the instruction it is at and
-- that the call site is missing.
/-- "instruction":"CIL.Op.localAddr 0","method":0,"missing":"callSite","obligation":null,"pc":3 -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : Memory) (value count sum : W32) (home : Reference) (current : Memory)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 count, .i32 sum]))])) :
    LoopTerminates program 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨3, entry.frame memory home, [], current⟩ := by
  cil_loop_call addTwo_holds sum

-- The record names the obligation the tactic was handed, read from its goal's tag.
/-- "obligation":"invariant","pc":3 -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : Memory) (value count sum : W32) (home : Reference) (current : Memory)
    (frame : LoopFrame [] memory current [.aggregate 8] [.bytes (.aggregate 8) home]
      (knownLocals [some (.aggregate (layout.encode [.i32 count, .i32 sum]))])) :
    LoopTerminates program 0 [.scalar (.i32 value)] (fun _ _ => True)
      ⟨3, entry.frame memory home, [], current⟩ := by
  refine ?invariant
  cil_loop_call addTwo_holds sum

-- A tactic that stops without an error, leaving a step for the proof, is recorded as stopped
-- there, with the instruction it did not take.
/-- "instruction":"CIL.Op.const32 2","method":1,"missing" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : Memory) (value : W32) (frame : Frame)
    (result : Except LocatedFault (Memory × List Value)) :
    run program 100 1 0 [.scalar (.i32 value)] frame [] memory = result := by
  cil_checked_steps 1

-- Each name the observer reads a fact or a missing fact by is a declaration of the framework.
#guard_msgs in
run_meta do
  for (name, _) in factMeanings do
    unless (← Lean.getEnv).contains name do throwError "{name} is not declared"
  for (_, names) in missingFactMentions do
    for name in names do
      unless (← Lean.getEnv).contains name do throwError "{name} is not declared"


end Tests.LoopDiagnostics
