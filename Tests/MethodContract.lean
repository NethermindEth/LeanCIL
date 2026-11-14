import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.MethodContract
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint
import CIL.Safety.ReturnMemory
import CIL.Safety.Segment

/-! A synthetic extraction with the bodies the C# fixture compiles to:
    `Root(ref r, in b) { AddTo(in r, in b, out r); r = Mix(r, b); }`. -/
namespace Extracted

open CIL

def method0Signature : String := "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)"
def method1Signature : String := "System.UInt64 Contracts.Calls::Mix(System.UInt64,System.UInt64)"
def method2Signature : String := "System.Void Contracts.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)"
@[cil_code] def method0 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .arg 0, .call 2 3, .arg 0, .arg 0, .load64, .arg 1, .load64, .call 1 2, .store64, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .ldc_i4 3, .conv_i8, .mul, .arg 1, .add, .ret] }
@[cil_code] def method2 : Method := { returnsValue := false, locals := [], code :=
  [.arg 2, .arg 0, .load64, .arg 1, .load64, .add, .store64, .ret] }
@[cil_code] def program : Program := [method0, method1, method2]
def signatures : List String := [method0Signature, method1Signature, method2Signature]

end Extracted

namespace Tests.MethodContract

open CIL.Safety

bind_method root rootBody := "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)"
bind_callee mix mixBody := "System.UInt64 Contracts.Calls::Mix(System.UInt64,System.UInt64)" from rootBody
bind_callee addTo addBody := "System.Void Contracts.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" from rootBody
bind_call addSite := addTo from rootBody
bind_call mixSite := mix from rootBody

def mixContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ m := m.WellFormed
  footprint _ := []
  post input _ _ v := v = input.1 * 3 + input.2

structure AddInput where
  a : Reference
  b : Reference
  res : Reference
  x : CIL.W64
  y : CIL.W64

/-- `res` may overlap either input arbitrarily. -/
def addContract : MethodContract AddInput where
  args input := [.reference (.address input.a), .reference (.address input.b), .reference (.address input.res)]
  pre input m := read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()
  footprint input := [(input.res, 8)]
  post input _ final values := values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)

structure RootInput where
  r : Reference
  b : Reference
  x : CIL.W64
  y : CIL.W64

def rootContract : MethodContract RootInput where
  args input := [.reference (.address input.r), .reference (.address input.b)]
  pre input m := m.WellFormed ∧ read m input.r 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.r 8 1 true = .ok () ∧
    WordsDisjoint input.r input.b
  footprint input := [(input.r, 8)]
  post input _ final values := values = [] ∧
    read final input.r 8 1 = .ok (numberBytes ((input.x + input.y) * 3 + input.y).toNat 8)

@[cil_code] def boundedBody : CIL.Method :=
  { returnsValue := false, locals := [], code := [.nop, .nop, .nop, .ret] }

@[cil_code] def boundedProgram : CIL.Program := [boundedBody]

def boundedRun (pc : Nat) (frame : Frame) (memory : Memory) : Prop :=
  ∃ fuel result returned,
    run boundedProgram fuel 0 pc [] frame [] memory = .ok (result, returned) ∧ True

theorem bounded_steps_stop_at_continuation (frame : Frame) (memory : Memory)
    (continuation : boundedRun 2 frame memory) : boundedRun 0 frame memory := by
  unfold boundedRun at *
  cil_contract_steps 2 []
  exact continuation

theorem bounded_steps_zero_preserves_goal (frame : Frame) (memory : Memory)
    (continuation : boundedRun 0 frame memory) : boundedRun 0 frame memory := by
  unfold boundedRun at *
  cil_contract_steps 0 []
  exact continuation

theorem bounded_steps_stop_at_return (frame : Frame) (memory : Memory) : boundedRun 0 frame memory := by
  unfold boundedRun
  cil_contract_steps 1000000 []
  trivial

theorem contract_steps_until_continuation (frame : Frame) (memory : Memory)
    (continuation : boundedRun 2 frame memory) : boundedRun 0 frame memory := by
  unfold boundedRun at *
  cil_contract_steps [] until continuation

theorem contract_steps_until_checks_initial_goal (frame : Frame) (memory : Memory)
    (continuation : boundedRun 0 frame memory) : boundedRun 0 frame memory := by
  unfold boundedRun at *
  cil_contract_steps [] until continuation

theorem contract_steps_until_postcondition (frame : Frame) (memory : Memory)
    (finished : True) : boundedRun 0 frame memory := by
  unfold boundedRun
  cil_contract_steps [] until finished

theorem mix_holds : mixContract.Holds Extracted.program mix := by
  rintro ⟨x, y⟩ m -
  refine MethodContract.Holds.intro m _ ?_ (Confined.refl _ m) rfl
  cil_checked_steps

theorem add_holds : addContract.Holds Extracted.program addTo := by
  rintro ⟨a, b, res, x, y⟩ m ⟨readA, readB, writable⟩
  dsimp only [addContract] at readA readB writable
  obtain ⟨stored, wrote, store, readback⟩ := store_word64 (x + y) writable
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine MethodContract.Holds.intro stored _
    ?_ (Confined.write wrote (by simp [addContract, numberBytes])) ⟨rfl, readback⟩
  cil_checked_steps [fa, fb, fr, la, lb, store]

set_option maxHeartbeats 400000 in
/-- Uses only the callees' contracts at their call sites; neither callee body is unfolded. -/
theorem root_holds (mixHolds : mixContract.Holds Extracted.program mix)
    (addHolds : addContract.Holds Extracted.program addTo) : rootContract.Holds Extracted.program root := by
  rintro ⟨r, b, x, y⟩ m ⟨formed, readR, readB, writable, disjoint⟩
  dsimp only [rootContract, MethodContract.Returns] at *
  have rOld := formed.access_bound writable
  have bOld := formed.access_bound (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  cil_contract_steps [fr, fb]
  cil_formed_call addHolds ⟨r, b, r, x, y⟩ at addSite [fr, fb]
  case precondition => exact ⟨readR, readB, writable⟩
  case wellFormed => exact formed
  -- The call supplies `m1.WellFormed`, which `mixContract.pre` needs; `addContract.post` does not state it.
  intro m1 sum added kept
  obtain ⟨rfl, readR1⟩ := added.post
  have formed1 := kept.formed
  have framed1 := added.framed
  have readB1 : read m1 b 8 1 = .ok (numberBytes y.toNat 8) :=
    (framed1.read_eq b bOld 8 1 disjoint.outside).trans readB
  have writable1 : access m1 r 8 1 true = .ok () := (framed1.access_write r rOld 8 1).trans writable
  have fr1 := access_reference_valid _ _ _ _ _ writable1
  have fb1 := access_reference_valid _ _ _ _ _ (read_access readB1)
  have lr1 := load_word64_of_read readR1
  have lb1 := load_word64_of_read readB1
  cil_contract_steps [fr1, fb1, lr1, lb1]
  cil_contract_call mixHolds (x + y, y) at mixSite []
  case precondition => exact formed1
  intro m2 mixed call
  obtain rfl := call.post
  have framed2 := call.framed
  dsimp only [mixContract]
  have writable2 : access m2 r 8 1 true = .ok () :=
    (framed2.access_write r (Nat.lt_of_lt_of_le rOld framed1.grows) 8 1).trans writable1
  obtain ⟨m3, wrote, store, readback⟩ := store_word64 ((x + y) * 3 + y) writable2
  have fr2 := access_reference_valid _ _ _ _ _ writable2
  cil_contract_steps [fr2, store]
  case postcondition =>
    exact ⟨framed1.trans ((framed2.widen (by simp [mixContract])).trans
        (Confined.write wrote (by simp [addContract, numberBytes]))),
      _, rfl, rfl, readback⟩

theorem root_correct : rootContract.Holds Extracted.program root := root_holds mix_holds add_holds

-- A callee's writes to its own frame and the frame's teardown leave only its footprint changed.
theorem frame_confined (m entered home stored final : Memory) (frame : Frame) (slot out : Reference)
    (slotBytes outBytes : List (BitVec 8))
    (enter : MemoryBelow m.nextIdentity m entered) (grows : m.nextIdentity ≤ entered.nextIdentity)
    (fresh : m.nextIdentity ≤ slot.allocation) (owned : ∀ id ∈ frame.owned, m.nextIdentity ≤ id)
    (wroteSlot : write entered slot slotBytes 1 = .ok home) (wroteOut : write home out outBytes 1 = .ok stored)
    (left : leaveFrame frame stored = final) :
    Confined [(out, outBytes.length)] m final := by
  have body : Confined ([(slot, slotBytes.length)] ++ [(out, outBytes.length)]) m stored :=
    ((Confined.refl _ m).then_below enter grows).trans
      ((Confined.write wroteSlot (by simp)).trans (Confined.write wroteOut (by simp)))
  subst left
  exact (body.forget_fresh (by simpa using fresh)).after_leaveFrame owned

-- A callee that writes only its own frame cannot change what the caller reads after the call.
theorem call_keeps_caller_read (body : CIL.Method) (args : List Value) (m entered home : Memory) (frame : Frame)
    (slot r : Reference) (bytes : List (BitVec 8)) (width alignment : Nat)
    (enter : enterFrame body args m = .ok (frame, entered)) (fresh : m.nextIdentity ≤ slot.allocation)
    (wrote : write entered slot bytes 1 = .ok home) (old : r.allocation < m.nextIdentity) :
    read (leaveFrame frame home) r width alignment = read m r width alignment :=
  (MemoryBelow.frame_round_trip enter (write_preserves_memory_below _ _ _ _ _ _ fresh wrote)).read r old width alignment

#print axioms call_keeps_caller_read
#print axioms root_holds
#print axioms root_correct
#print axioms frame_confined

example (program : CIL.Program) (before after : Memory)
    (kept : FrameInvariants program before after) :
    after.WellFormed ∧ (StaticWorldValid (programStaticDescriptors program) before →
      StaticWorldValid (programStaticDescriptors program) after) ∧
      ∀ catalog, ObjectSitesConsistent catalog program →
        before.ClassesConsistent catalog → after.ClassesConsistent catalog :=
  ⟨kept.formed, kept.staticWorld, kept.classes⟩

example (program : CIL.Program) (memory : Memory) (formed : memory.WellFormed) :
    FrameInvariants program memory memory :=
  FrameInvariants.refl program formed

example (program : CIL.Program) (before after : Memory) (formed : after.WellFormed)
    (preserved : StaticWorldPreserved program before after)
    (classes : ClassesPreserved program before after) : FrameInvariants program before after where
  formed := formed
  staticWorld world := preserved world
  classes catalog sites consistent := classes catalog sites consistent

example {program : CIL.Program} {first middle last : Memory}
    (left : StaticWorldPreserved program first middle) (right : StaticWorldPreserved program middle last) :
    StaticWorldPreserved program first last :=
  left.trans right

example {program : CIL.Program} {first middle last : Memory}
    (left : FrameInvariants program first middle) (right : FrameInvariants program middle last) :
    FrameInvariants program first last :=
  left.trans right

example {program : CIL.Program} {before after : Memory} (kept : FrameInvariants program before after)
    (world : StaticWorldValid (programStaticDescriptors program) before) :
    after.WellFormed ∧ StaticWorldValid (programStaticDescriptors program) after :=
  ⟨kept.formed, kept.staticWorld world⟩

-- A loaded local reaches the stack as `localResult kind value` and its consumer must step by its
-- equation; unfolding `CIL.step`, or re-elaborating a tactic per step, exceeds the budget.
def loadedGuardBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := false, locals := [], code :=
    [.ldloc 0, .ldc_i4 4, .blt_un 7, .ldloc 0, .ldc_i4 0, .bge 7, .nop, .ret,
      .ldloc 1, .ldloc 2, .blt_un 7, .ret] }

set_option maxHeartbeats 2000 in
theorem loaded_unsigned_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (word : CIL.W32) (home : Reference) (slot : frame.locals[0]? = some (.bytes .word32 home))
    (load : loadLocal memory (.bytes .word32 home) =
      .ok (.scalar (localResult .word32 (.i32 word)))) :
    Segment program index 0 (if word < 4#32 then 7 else 3)
      (SegmentState.exact [] ⟨frame, [], memory⟩)
      (SegmentState.exact [] ⟨frame, [], memory⟩) := by
  cil_segment 3 [found, slot, load]

set_option maxHeartbeats 2000 in
theorem loaded_signed_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (word : CIL.W32) (home : Reference) (slot : frame.locals[0]? = some (.bytes .word32 home))
    (load : loadLocal memory (.bytes .word32 home) =
      .ok (.scalar (localResult .word32 (.i32 word)))) :
    Segment program index 3 (if 0 ≤ word.toInt then 7 else 6)
      (SegmentState.exact [] ⟨frame, [], memory⟩)
      (SegmentState.exact [] ⟨frame, [], memory⟩) := by
  cil_segment 3 [found, slot, load]

set_option maxHeartbeats 2000 in
theorem loaded_limb_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (low high : CIL.W64) (lowHome highHome : Reference)
    (lowSlot : frame.locals[1]? = some (.bytes .word64 lowHome))
    (highSlot : frame.locals[2]? = some (.bytes .word64 highHome))
    (lowLoad : loadLocal memory (.bytes .word64 lowHome) =
      .ok (.scalar (localResult .word64 (.i64 low))))
    (highLoad : loadLocal memory (.bytes .word64 highHome) =
      .ok (.scalar (localResult .word64 (.i64 high)))) :
    Segment program index 8 (if low < high then 7 else 11)
      (SegmentState.exact [] ⟨frame, [], memory⟩)
      (SegmentState.exact [] ⟨frame, [], memory⟩) := by
  cil_segment 3 [found, lowSlot, highSlot, lowLoad, highLoad]

-- A parameter-selected widening is fetched as `if true = true then ..` and must step by its
-- equation; re-elaborating a tactic at every contract step exceeds the budget.
def widenBody (signed : Bool) : CIL.Method :=
  { returnsValue := true, locals := [], code :=
      [.arg 0, if signed then .conv_i8 else .conv_u8, .arg 1, .pop, .pop, .ldc_i4 0, .ret] }

def widenArgs (scalarFirst : Bool) (input : Reference) (value : CIL.Value) : List Value :=
  if scalarFirst then [.scalar value, .reference (.address input)] else [.reference (.address input), .scalar value]

set_option maxHeartbeats 3500 in
theorem selected_widening (signed : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (widenBody signed)) (frame : Frame) (memory : Memory)
    (input : Reference) (word : CIL.W32) (formed : form memory input = .ok input) :
    Segment program index 0 3
      (SegmentState.exact (widenArgs (true && true) input (.i32 word)) ⟨frame, [], memory⟩)
      (SegmentState.exact (widenArgs (true && true) input (.i32 word))
        ⟨frame, [.reference (.address input),
          .scalar (.i64 (if signed then word.signExtend 64 else word.zeroExtend 64))],
          memory⟩) := by
  cases signed
  all_goals
    simp only [Bool.false_eq_true, ite_true, ite_false]
    cil_segment 3 [found, formed, widenArgs]

/-- info: 'Tests.MethodContract.loaded_unsigned_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms loaded_unsigned_branch
/-- info: 'Tests.MethodContract.loaded_signed_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms loaded_signed_branch
/-- info: 'Tests.MethodContract.loaded_limb_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms loaded_limb_branch
/-- info: 'Tests.MethodContract.selected_widening' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selected_widening

/-- A feature test and a vector load step by their own equations inside a contract proof. -/
def featureLoadBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.feature .avx2, .pop, .arg 0, .memory .load128, .ret] }

theorem feature_load_contract (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.avx2 = true) (found : program[index]? = some (featureLoadBody profile))
    (memory : Memory) (source : Reference) (value : BitVec 128)
    (formed : form memory source = .ok source)
    (loaded : loadValue memory (.address source) 16 = .ok (.v128 value)) :
    ∃ fuel result returned, invoke program fuel index [.reference (.address source)] memory =
      .ok (result, returned) ∧ returned = [.scalar (.v128 value)] := by
  cil_contract_steps [wide, formed, loaded]
  rfl

/-- info: 'Tests.MethodContract.feature_load_contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_load_contract

/-- A body whose first instruction depends on a feature, stepped as a contract proof steps it. -/
def featureOpBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [],
    code := [if profile.avx2 then .arg 1 else .arg 0, .fieldAt 0 8, .ret] }

open CIL.Safety in
theorem feature_op_contract_steps (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (scalar : profile.avx2 = false) (found : program[index]? = some (featureOpBody profile))
    (frame : Frame) (memory : Memory) (left right : Reference) (limb : BitVec 64)
    (formed : form memory left = .ok left)
    (field : ∀ rest, instruction (.fieldAt 0 8) (.reference (.address left) :: rest) memory =
      .ok (memory, .scalar (.i64 limb) :: rest)) :
    ∃ fuel final values,
      run program fuel index 0 [.reference (.address left), .reference (.address right)] frame [] memory =
        .ok (final, values) ∧ final = leaveFrame frame memory ∧ values = [.scalar (.i64 limb)] := by
  cil_contract_steps [scalar, formed, field]
  exact ⟨rfl, rfl⟩

#print axioms feature_op_contract_steps

/-- A wrapper can load either argument first and widen either the first or second stack value. -/
def orderedWidenBody (signed scalarFirst reversed : Bool) : CIL.Method :=
  let first := if reversed then 1 else 0
  let second := if reversed then 0 else 1
  let convert := if signed then CIL.Instruction.conv_i8 else CIL.Instruction.conv_u8
  { returnsValue := true, locals := [], code :=
      (if scalarFirst then [.arg first, convert, .arg second]
       else [.arg first, .arg second, convert]) ++ [.pop, .pop, .ldc_i4 0, .ret] }

set_option maxHeartbeats 12000 in
/-- All eight wrapper cases use one three-step proof without unfolding the evaluator. -/
theorem ordered_widening (signed scalarFirst reversed : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (orderedWidenBody signed scalarFirst reversed))
    (frame : Frame) (memory : Memory) (input : Reference) (word : CIL.W32)
    (formed : form memory input = .ok input) :
    Segment program index 0 3
      (SegmentState.exact (widenArgs (scalarFirst != reversed) input (.i32 word))
        ⟨frame, [], memory⟩)
      (SegmentState.exact (widenArgs (scalarFirst != reversed) input (.i32 word))
        ⟨frame, (widenArgs scalarFirst input
          (.i64 (if signed then word.signExtend 64 else word.zeroExtend 64))).reverse,
          memory⟩) := by
  cases signed <;> cases scalarFirst <;> cases reversed
  all_goals
    simp only [widenArgs, Bool.false_eq_true, ite_true, ite_false,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    cil_segment 3 [found, formed, widenArgs]

#print axioms ordered_widening

/-- The wrapper has a successful continuation for every ordering and every input word. -/
theorem ordered_widening_returns (signed scalarFirst reversed : Bool)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (orderedWidenBody signed scalarFirst reversed))
    (frame : Frame) (memory : Memory) (input : Reference) (word : CIL.W32)
    (formed : form memory input = .ok input) :
    ∃ fuel final returned, run program fuel index 0
      (widenArgs (scalarFirst != reversed) input (.i32 word)) frame [] memory =
        .ok (final, returned) ∧ final = leaveFrame frame memory ∧
        returned = [.scalar (.i32 0)] := by
  apply WP.exists_execution
  apply (ordered_widening signed scalarFirst reversed program index found frame memory input word
    formed).run_exists _ _ ⟨rfl, rfl⟩
  rintro after ⟨_, rfl⟩
  cases scalarFirst <;> cases signed <;> cases reversed
  all_goals
    cil_contract_steps [found, formed, widenArgs, orderedWidenBody]
    exact ⟨rfl, rfl⟩

#print axioms ordered_widening_returns

/-- An opaque helper's result-only contract still supplies checked lifetime and frame facts.
    No cell footprint or confinement assertion is needed or inferred. -/
theorem framed_opaque_call {program : CIL.Program} {memory : Memory} (value : CIL.W32)
    (formed : memory.WellFormed)
    (found : program[0]? = some
      { locals := [], returnsValue := true, code := [.call 1 0, .ret] })
    (helper : WP (Execution (fun fuel => invoke program fuel 1 [] memory))
      (fun result => result.2 = [.scalar (.i32 value)])) :
    WP (Execution (fun fuel => run program fuel 0 0 [] ⟨0, [], [], 0⟩ [] memory))
      (fun result => FrameInvariants program memory result.1 ∧
        AllocationExtension memory result.1 ∧ result.2 = [.scalar (.i32 value)]) := by
  apply WP.call_framed found rfl (by cil_checked_step []) formed helper
  intro final values result preserved allocations
  change values = [.scalar (.i32 value)] at result
  subst values
  cil_contract_steps [found]
  exact ⟨preserved, allocations, rfl⟩

#print axioms framed_opaque_call

/-- A feature test and a literal each feed a branch, which then continues at a numeral. -/
@[cil_code] def literalBranchBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code :=
    [.feature .avx2, .brfalse 5, .ldc_i8 1, .brtrue 6, .ret, .ldc_i4 9, .ldc_i4 7, .ret] }

/-- A branch on a literal operand is decided where it is taken: the lookups after it meet a
    numeral, and so does a continuation stated at the numeral. A conditional left in the
    program counter would be carried through every later step. -/
theorem literal_branch_pc (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.avx2 = true) (found : program[index]? = some (literalBranchBody profile))
    (frame : Frame) (memory : Memory) :
    ∃ fuel result returned, run program fuel index 0 [] frame [] memory =
      .ok (result, returned) ∧ returned = [.scalar (.i32 7)] := by
  cil_contract_steps 4 [found, wide]
  -- The pinned goal is the check: both branches were decided to the numeral 6.
  guard_target = ∃ fuel result returned, run program fuel index 6 [] frame [] memory =
    .ok (result, returned) ∧ returned = [.scalar (.i32 7)]
  cil_contract_steps [found, wide]
  rfl

#print axioms literal_branch_pc

/-- Step facts match a fetched opcode whose index they state as closed arithmetic, here through
    a `Fin` literal, and a loaded `localResult` of a typed value is the value the next fact
    takes. The facts would otherwise match only an index spelled as the numeral. -/
theorem coerced_index_facts (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (found : program[index]? = some body) (load : body.code[0]? = some (.ldloc 7))
    (store : body.code[1]? = some (.stloc 8)) (frame : Frame) (memory after : Memory)
    (bits : BitVec 128)
    (loaded : ∀ pc args stack,
      step body (.ldloc (↑(6 : Fin 10) + 1)) pc args frame stack memory =
        .ok (.next (pc + 1) (.scalar (localResult .vector128 (.v128 bits)) :: stack) frame
          memory))
    (stored : ∀ pc args stack,
      step body (.stloc (↑(7 : Fin 10) + 1)) pc args frame (.scalar (.v128 bits) :: stack)
        memory = .ok (.next (pc + 1) stack frame after))
    (continuation : WP (Execution (fun fuel => run program fuel index 2 [] frame [] after))
      (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel index 0 [] frame [] memory)) (fun _ => True) := by
  cil_contract_steps [found, load, store, loaded, stored] until continuation

#print axioms coerced_index_facts

/-- Two symbolic words are combined and branched on. -/
@[cil_code] def symbolicBranchBody : CIL.Method :=
  { returnsValue := true, locals := [], code :=
    [.arg 0, .arg 1, .or, .brtrue 6, .ldc_i4 7, .ret, .ldc_i4 9, .ret] }

/-- A branch no fact decides ends the walk with its condition in the program counter, where
    `split` gives both successors; stepping resumes in each. -/
theorem symbolic_branch_splits (program : CIL.Program) (index : Nat)
    (found : program[index]? = some symbolicBranchBody) (frame : Frame) (memory : Memory)
    (left right : CIL.W64) :
    ∃ fuel result returned, run program fuel index 0
      [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory = .ok (result, returned) ∧
        (returned = [.scalar (.i32 7)] ∨ returned = [.scalar (.i32 9)]) := by
  cil_contract_steps [found]
  guard_target = ∃ fuel result returned, run program fuel index
    (if ¬left ||| right = 0#64 then 6 else 4) [.scalar (.i64 left), .scalar (.i64 right)]
      frame [] memory = .ok (result, returned) ∧
        (returned = [.scalar (.i32 7)] ∨ returned = [.scalar (.i32 9)])
  split
  · cil_contract_steps [found]
    exact Or.inr rfl
  · cil_contract_steps [found]
    exact Or.inl rfl

#print axioms symbolic_branch_splits

-- An instruction lookup at an undecided branch reports the branch without evaluating it.
/--
error: cil_lookup: undecided branch if ¬left = 0#64 then 6 else 4; split on its condition
-/
#guard_msgs in
example (left : CIL.W64) (operation : CIL.Instruction) :
    symbolicBranchBody.code[if ¬left = 0#64 then 6 else 4]? = some operation := by
  cil_lookup []

end Tests.MethodContract
