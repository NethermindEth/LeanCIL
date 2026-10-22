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
    simp only [storeValue, referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine ⟨9, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
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
    simp only [storeValue, referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fr2 := access_reference_valid _ _ _ _ _ writable2
  cil_contract_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
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

#print axioms root_holds
#print axioms root_correct
#print axioms frame_confined

end Tests.MethodContract
