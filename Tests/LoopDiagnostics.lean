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

bind_entry entry (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :=
  tally with [.scalar (.i32 value)] from memory allocating wellFormed

/-- The struct local, remembered by its field values `(count, sum)`. -/
abbrev State (memory : Memory) (home : Reference) :=
  FrameState [] memory [.aggregate 8] (W32 × W32) (fun _ => [.bytes (.aggregate 8) home])
    fun state => [some (.aggregate (layout.encode [.i32 state.1, .i32 state.2]))]

bind_cutpoint header (memory : Memory) (value : W32) (home : Reference)
    (state : State memory home) :=
  tally matching (fun op => op matches .bne _) with entry.frame memory home,
    [.scalar (.i32 value), .scalar (.i32 state.values.1)], state.memory

/-- With no facts passed, the gathered frame facts step the struct's zeroing, its by-value field
    reads, the call through `addTwo`'s contract, both field stores and the return: the loop
    doubles its input and allocates nothing the caller sees. -/
theorem doubles (memory : Memory) (value : W32) (wellFormed : memory.WellFormed) :
    ∃ fuel final, invoke program fuel 0 [.scalar (.i32 value)] memory =
      .ok (final, [.scalar (.i32 (2 * value))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked memory value wellFormed
  obtain ⟨zeroed, zeroing, frame, -⟩ := (entryFrame []).zero_aggregate 0 layout [.i32 0, .i32 0]
  refine invoke_loop_induction (by rfl) rfl setup (header memory value home)
    (fun state => state.values.2 = 2 * state.values.1)
    (fun state => (value - state.values.1).toNat) ⟨(0, 0), zeroed, frame⟩ (by cil_loop_steps)
    (by simp) ?_
  rintro ⟨⟨count, sum⟩, current, frame⟩ doubled recurse
  dsimp only at doubled
  by_cases done : count = value
  · subst done
    rw [← doubled]
    cil_loop_finish
  · cil_loop_advance [done]
    cil_loop_call addTwo_holds sum
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

end Tests.LoopDiagnostics
