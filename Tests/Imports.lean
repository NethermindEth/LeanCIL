import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.Imports
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint
import CIL.Safety.ReturnMemory

/-! `Root(ref r, in b) { AddTo(in r, in b, out r); r = Mix(r, b); }` with `AddTo` imported at slot 0. -/
namespace Tests.Imports.Calls.Extracted

open CIL

def method0Signature : String := "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)"
def method1Signature : String := "System.UInt64 Contracts.Calls::Mix(System.UInt64,System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .arg 0, .call 2 3, .arg 0, .arg 0, .load64, .arg 1, .load64, .call 1 2, .store64, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 3, .convI8, .mul, .arg 1, .add, .ret] }
@[cil_code] def program : Program := [method0, method1]
def signatures : List String := [method0Signature, method1Signature]

end Tests.Imports.Calls.Extracted

namespace Tests.Imports.Calls

open CIL.Safety

bind_method root rootBody := "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)"
bind_callee mix mixBody := "System.UInt64 Contracts.Calls::Mix(System.UInt64,System.UInt64)" from rootBody
@[cil_code] def addTo : Nat := importIndex Extracted.program 0
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

/-- Proved once on the unlinked program; every linked program reuses it through `extend`. -/
theorem mix_holds : mixContract.Holds Extracted.program mix := by
  rintro ⟨x, y⟩ m -
  dsimp only [mixContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps

/-- The import's contract is the only assumption about `AddTo`; no body is fixed at its slot. -/
def importsAdd (linked : CIL.Program) : Prop := addContract.Holds linked addTo

set_option maxHeartbeats 400000 in
/-- `Root` holds in every program that links it and provides `AddTo` meeting its contract. -/
theorem root_given : HoldsGiven Extracted.program importsAdd (fun linked => rootContract.Holds linked root) := by
  rintro linked ⟨rest, rfl⟩ addHolds
  have mixHolds := mix_holds.extend ⟨rest, rfl⟩
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
  generalize (x + y) * 3 + y = v
  have writable2 : access m2 r 8 1 true = .ok () :=
    (framed2.access_write r (Nat.lt_of_lt_of_le rOld framed1.grows) 8 1).trans writable1
  have length : (numberBytes v.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m3, wrote⟩ := write_succeeds (bytes := numberBytes v.toNat 8)
    (by simpa only [length] using writable2)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m2 (.address r) (.i64 v) = .ok m3 := by
    simp only [storeValue, referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fr2 := access_reference_valid _ _ _ _ _ writable2
  cil_contract_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    staticInstruction, fr2, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [leaveFrame, List.foldl_nil]
  exact ⟨framed1.trans ((framed2.widen (by simp [mixContract])).trans (Confined.write wrote (by simp [addContract, numberBytes]))),
    _, rfl, rfl, readback⟩

/-- The claim as the plain implication over linked programs. -/
example : ∀ linked, Links Extracted.program linked → addContract.Holds linked (importIndex Extracted.program 0) →
    rootContract.Holds linked root :=
  root_given

/-! One concrete implementation of the import, appended at its slot. -/

@[cil_code] def addBody : CIL.Method := { returnsValue := false, locals := [], code :=
  [.arg 2, .arg 0, .load64, .arg 1, .load64, .add, .store64, .ret] }
@[cil_code] def linkedProgram : CIL.Program := Extracted.program ++ [addBody]

theorem add_linked : importsAdd linkedProgram := by
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

theorem root_linked : rootContract.Holds linkedProgram root :=
  root_given.discharge ⟨[addBody], rfl⟩ add_linked

/-! Unlinked, the import slot is empty and `Root` faults at the call instead of returning. -/

/-- `invoke_of_run` for any outcome, faults included. -/
theorem invoke_eq_of_run {program : CIL.Program} {fuel method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory} {outcome : Except LocatedFault (Memory × List Value)}
    (found : program[method]? = some body) (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : run program fuel method 0 args frame [] entered = outcome) :
    invoke program fuel method args memory = outcome := by
  simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact executed

theorem root_unlinked (input : RootInput) (m : Memory) (permitted : rootContract.pre input m) (fuel : Nat) :
    invoke Extracted.program (fuel + 4) root (rootContract.args input) m = .error ⟨root, addSite, .invalidState⟩ := by
  obtain ⟨r, b, x, y⟩ := input
  obtain ⟨_, _, readB, writable, _⟩ := permitted
  have fr := access_reference_valid _ _ _ _ _ writable
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  dsimp only [rootContract]
  refine invoke_eq_of_run (by simp only [cil_code]; rfl)
    (by simp [checkedValue, formValue, checkedAt, fr, fb, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
    (by rfl) ?_
  cil_checked_steps [checkedValue, formValue, checkedAt, fr, fb,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact run_call_unlinked (by simp only [cil_code]; rfl) addSite.call
    (by cil_checked_step [checkedValue, formValue, checkedAt, fr, fb, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure])
    (importIndex_unlinked _ 0)

/-- Unlinked, `Root` returns at no fuel. -/
theorem root_unlinked_never_returns (input : RootInput) (m : Memory) (permitted : rootContract.pre input m)
    (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel root (rootContract.args input) m ≠ .ok result := fun returned =>
  nomatch invoke_unique (first := .ok result) trivial (by simp [Settled]) returned (root_unlinked input m permitted 0)

/-- So the unlinked contract holds only vacuously: no input meets its precondition. -/
theorem root_unlinked_vacuous (holds : rootContract.Holds Extracted.program root) (input : RootInput) (m : Memory) :
    ¬ rootContract.pre input m := fun permitted =>
  let ⟨fuel, final, values, invoked, _⟩ := holds input m permitted
  root_unlinked_never_returns input m permitted fuel (final, values) invoked

#print axioms root_given
#print axioms root_linked
#print axioms root_unlinked
#print axioms root_unlinked_vacuous

end Tests.Imports.Calls

/-! `Root(v) => Strict(v) + 1`, `Strict(v) => Percent(v) == 0 ? throw ... : v`, `Percent` imported at slot 0. -/
namespace Tests.Imports.Outcomes.Extracted

open CIL

def method0Signature : String := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Outcomes.Calls::Strict(System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .const32 1, .convI8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 2 1, .brzero 5, .arg 0, .ret, .nop, .nop, .throw "System.ArgumentException"] }
@[cil_code] def program : Program := [method0, method1]
def signatures : List String := [method0Signature, method1Signature]

end Tests.Imports.Outcomes.Extracted

namespace Tests.Imports.Outcomes

open CIL.Safety

bind_method root rootBody := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
bind_callee strict strictBody := "System.UInt64 Outcomes.Calls::Strict(System.UInt64)" from rootBody
@[cil_code] def percent : Nat := importIndex Extracted.program 0
bind_call strictSite := strict from rootBody
bind_call percentSite := percent from strictBody

def percentContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"

def strictRaises (v : CIL.W64) : Option String :=
  if v ≤ 100 then if v = 0 then some "System.ArgumentException" else none
  else some "System.ArgumentOutOfRangeException"

def strictContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := strictRaises v

def rootContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v + 1
  raises v _ := strictRaises v

def importsPercent (linked : CIL.Program) : Prop := percentContract.Holds linked percent

/-- The imported raise propagates, a zero return then raises here, and other values return. -/
theorem strict_given :
    HoldsGiven Extracted.program importsPercent (fun linked => strictContract.Holds linked strict) := by
  rintro linked ⟨rest, rfl⟩ percentHolds
  rintro v m -
  by_cases within : v ≤ 100
  · by_cases zero : v = 0
    · subst zero
      simp only [strictContract, strictRaises, within, ↓reduceIte]
      cil_raise_steps []
      cil_outcome_call percentHolds 0 at percentSite []
      · trivial
      · simp only [percentContract, within, ite_true]
      rintro m1 _ - - ⟨_, rfl, rfl⟩
      dsimp only [percentContract]
      cil_raise_steps [CIL.truth]
    · simp only [strictContract, strictRaises, within, zero, ite_true, ite_false]
      cil_contract_steps []
      cil_outcome_call percentHolds v at percentSite []
      · trivial
      · simp only [percentContract, within, ite_true]
      rintro m1 _ - confined ⟨out, rfl, same⟩
      subst out
      dsimp only [percentContract]
      have truth : CIL.truth (.i64 v) = some true := by simp [CIL.truth]; exact zero
      cil_contract_steps [truth]
      exact ⟨confined, _, rfl, rfl⟩
  · simp only [strictContract, strictRaises, within, ite_false]
    cil_raise_steps []
    cil_outcome_raise percentHolds v at percentSite []
    · trivial
    · simp only [percentContract, within, ite_false]

/-- `Root` composes the conditional `Strict` contract in each linked program. -/
theorem root_given :
    HoldsGiven Extracted.program importsPercent (fun linked => rootContract.Holds linked root) := by
  rintro linked ⟨rest, rfl⟩ percentHolds
  have strictHolds := strict_given.discharge ⟨rest, rfl⟩ percentHolds
  rintro v m -
  dsimp only [rootContract]
  cases raised : strictRaises v with
  | some exception =>
    cil_raise_steps []
    cil_outcome_raise strictHolds v at strictSite []
    · trivial
    · exact raised
  | none =>
    cil_contract_steps []
    cil_outcome_call strictHolds v at strictSite []
    · trivial
    · exact raised
    rintro m1 _ - confined ⟨out, rfl, same⟩
    subst out
    dsimp only [strictContract]
    cil_contract_steps []
    exact ⟨confined, _, rfl, rfl⟩

@[cil_code] def percentBody : CIL.Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 (BitVec.ofInt 32 100), .convI8, .bleu 7, .nop, .nop,
    .throw "System.ArgumentOutOfRangeException", .arg 0, .ret] }
@[cil_code] def linkedProgram : CIL.Program := Extracted.program ++ [percentBody]

theorem percent_linked : importsPercent linkedProgram := by
  rintro v m -
  by_cases within : v ≤ 100
  · have bound : v ≤ 100#64 := within
    simp only [percentContract, within, ite_true]
    refine ⟨10, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
    cil_checked_steps [bound]
  · have bound : ¬ v ≤ 100#64 := within
    simp only [percentContract, within, ite_false]
    cil_raise_steps [bound]

theorem root_linked : rootContract.Holds linkedProgram root :=
  root_given.discharge ⟨[percentBody], rfl⟩ percent_linked

/-- The imported exception reaches `Root` in the linked program. -/
example (m : Memory) : Raises linkedProgram root [.scalar (.i64 101)] m "System.ArgumentOutOfRangeException" :=
  root_linked.raising (input := 101) trivial (by simp only [rootContract, strictRaises]; decide)

/-- Linking further keeps both outcomes. -/
example (more : CIL.Program) : rootContract.Holds (linkedProgram ++ more) root :=
  root_linked.extend ⟨more, rfl⟩

#print axioms strict_given
#print axioms root_given
#print axioms root_linked

end Tests.Imports.Outcomes
