import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.MethodContract
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint
import CIL.Safety.ReturnMemory

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
  [.arg 0, .const32 3, .convI8, .mul, .arg 1, .add, .ret] }
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
  dsimp only [mixContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps

theorem add_holds : addContract.Holds Extracted.program addTo := by
  rintro ⟨a, b, res, x, y⟩ m ⟨readA, readB, writable⟩
  dsimp only [addContract] at *
  have length : (numberBytes (x + y).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, wrote⟩ := write_succeeds (bytes := numberBytes (x + y).toNat 8) (by simpa only [length] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m (.address res) (.i64 (x + y)) = .ok stored := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine ⟨9, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    observerCount, unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
    fa, fb, fr, la, lb, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

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
  cil_contract_steps [checkedValue, formValue, checkedAt, fr, fb,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_formed_call addHolds ⟨r, b, r, x, y⟩ at addSite [checkedValue, formValue, checkedAt, fr, fb,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact ⟨readR, readB, writable⟩
  · exact formed
  -- The call supplies `m1.WellFormed`, which `mixContract.pre` needs; `addContract.post` does not state it.
  rintro m1 _ - formed1 - framed1 ⟨_, rfl, rfl, readR1⟩
  have readB1 : read m1 b 8 1 = .ok (numberBytes y.toNat 8) :=
    (framed1.read_eq b bOld 8 1 disjoint.outside).trans readB
  have writable1 : access m1 r 8 1 true = .ok () := (framed1.access_write r rOld 8 1).trans writable
  have fr1 := access_reference_valid _ _ _ _ _ writable1
  have fb1 := access_reference_valid _ _ _ _ _ (read_access readB1)
  have lr1 := load_word64_of_read readR1
  have lb1 := load_word64_of_read readB1
  cil_contract_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    fr1, fb1, lr1, lb1, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_call mixHolds (x + y, y) at mixSite [checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  · exact formed1
  rintro m2 _ - framed2 ⟨_, rfl, rfl⟩
  dsimp only [mixContract]
  have writable2 : access m2 r 8 1 true = .ok () :=
    (framed2.access_write r (Nat.lt_of_lt_of_le rOld framed1.grows) 8 1).trans writable1
  have length : (numberBytes ((x + y) * 3 + y).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m3, wrote⟩ := write_succeeds (bytes := numberBytes ((x + y) * 3 + y).toNat 8)
    (by simpa only [length] using writable2)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m2 (.address r) (.i64 ((x + y) * 3 + y)) = .ok m3 := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fr2 := access_reference_valid _ _ _ _ _ writable2
  cil_contract_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    observerCount, unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
    staticInstruction, fr2, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [leaveFrame, List.foldl_nil]
  exact ⟨framed1.trans ((framed2.widen (by simp [mixContract])).trans (Confined.write wrote (by simp [addContract, numberBytes]))),
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
  exact (body.forget_fresh (by simpa using fresh)).then_below
    (leaveFrame_preserves_memory_below frame stored _ owned) (Nat.le_of_eq (leaveFrame_nextIdentity frame stored).symm)

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

example (program : CIL.Program) (before after : Memory) :
    FrameInvariants program before after =
      (after.WellFormed ∧ (StaticWorldValid (programStaticDescriptors program) before →
        StaticWorldValid (programStaticDescriptors program) after)) := rfl

example (program : CIL.Program) (memory : Memory) (formed : memory.WellFormed) :
    FrameInvariants program memory memory :=
  FrameInvariants.refl program formed

example (program : CIL.Program) (before after : Memory) (formed : after.WellFormed)
    (preserved : StaticWorldPreserved program before after) : FrameInvariants program before after := by
  constructor
  · exact formed
  · intro world
    exact preserved world

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

-- A loaded local reaches the stack as `localResult kind value`; its consumer must still rewrite by its
-- step equation. The fallback unfolds `CIL.step`, whose match equations alone exceed this budget,
-- and so did re-elaborating an inline tactic block at every contract step.
def loadedGuardBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := false, locals := [], code :=
    [.local 0, .const32 4, .bltu 7, .local 0, .const32 0, .bge 7, .nop, .ret,
      .local 1, .local 2, .bltu 7, .ret] }

set_option maxHeartbeats 2000 in
theorem loaded_unsigned_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (word : CIL.W32) (home : Reference) (slot : frame.locals[0]? = some (.bytes .word32 home))
    (load : loadLocal memory (.bytes .word32 home) = .ok (.scalar (localResult .word32 (.i32 word))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned, run program fuel index (if word < 4#32 then 7 else 3) [] frame []
      memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 0 [] frame [] memory = .ok (final, returned) ∧
      post final returned := by
  cil_contract_steps [slot, load] until continuation

set_option maxHeartbeats 2000 in
theorem loaded_signed_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (word : CIL.W32) (home : Reference) (slot : frame.locals[0]? = some (.bytes .word32 home))
    (load : loadLocal memory (.bytes .word32 home) = .ok (.scalar (localResult .word32 (.i32 word))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned, run program fuel index (if 0 ≤ word.toInt then 7 else 6) [] frame []
      memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 3 [] frame [] memory = .ok (final, returned) ∧
      post final returned := by
  cil_contract_steps [slot, load] until continuation

set_option maxHeartbeats 2000 in
theorem loaded_limb_branch (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (loadedGuardBody profile)) (frame : Frame) (memory : Memory)
    (low high : CIL.W64) (lowHome highHome : Reference)
    (lowSlot : frame.locals[1]? = some (.bytes .word64 lowHome))
    (highSlot : frame.locals[2]? = some (.bytes .word64 highHome))
    (lowLoad : loadLocal memory (.bytes .word64 lowHome) = .ok (.scalar (localResult .word64 (.i64 low))))
    (highLoad : loadLocal memory (.bytes .word64 highHome) = .ok (.scalar (localResult .word64 (.i64 high))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned, run program fuel index (if low < high then 7 else 11) [] frame []
      memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 8 [] frame [] memory = .ok (final, returned) ∧
      post final returned := by
  cil_contract_steps [lowSlot, highSlot, lowLoad, highLoad] until continuation

-- A body that selects its widening by a parameter yields `if true = true then ..` from the lookup;
-- the step must reduce it to the opcode so the widening equation applies, within a budget that
-- re-elaborating an inline tactic block at every contract step exceeded.
def widenBody (signed : Bool) : CIL.Method :=
  { returnsValue := true, locals := [], code := [.arg 0, if signed then .convI8 else .convU8, .arg 1, .ret] }

def widenArgs (scalarFirst : Bool) (input : Reference) (value : CIL.Value) : List Value :=
  if scalarFirst then [.scalar value, .reference (.address input)] else [.reference (.address input), .scalar value]

set_option maxHeartbeats 3500 in
theorem selected_widening (signed : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (widenBody signed)) (frame : Frame) (memory : Memory)
    (input : Reference) (word : CIL.W32) (formed : form memory input = .ok input)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index 3 (widenArgs (true && true) input (.i32 word)) frame
        [.reference (.address input), .scalar (.i64 (if signed then word.signExtend 64 else word.zeroExtend 64))]
        memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 0 (widenArgs (true && true) input (.i32 word)) frame [] memory =
      .ok (final, returned) ∧ post final returned := by
  cases signed
  all_goals
    cil_contract_steps 3 [found, formed, widenArgs]
    simpa only [ite_true, Bool.false_eq_true, ite_false] using continuation

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
  cil_contract_steps [wide, formed, loaded, checkedValue, formValue, checkedAt]
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

end Tests.MethodContract
