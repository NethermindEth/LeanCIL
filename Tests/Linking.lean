import CIL.Safety.Linking
import Tests.Imports

/-! `AddTo(in a, in b, out res) { res = Sum(a, b); }` extracted alone, with its helper `Sum` at local index 1. -/
namespace Tests.Linking.Calls

open CIL CIL.Safety
open Tests.Imports.Calls (addContract AddInput rootContract root root_given)

@[cil_code] def addEntry : Method := { returnsValue := false, locals := [], code :=
  [.arg 2, .arg 0, .arg 1, .call 1 2, .store64, .ret] }
@[cil_code] def sumHelper : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .load64, .arg 1, .load64, .add, .ret] }
def addLib : Library := { entry := addEntry, helpers := [sumHelper] }
@[cil_code] def addProgram : CIL.Program := [addEntry, sumHelper]

theorem addLib_closed : Closed addLib.program := Closed.of_check (by decide)

/-- Proved on the library alone: the entry steps into its own helper at index 1. -/
theorem add_holds : addContract.Holds addProgram 0 := by
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
  refine ⟨10, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    fa, fb, fr, la, lb, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

@[cil_code] def linked : CIL.Program := link Tests.Imports.Calls.Extracted.program [addLib]

/-- The entry fills import slot 0 at index 2 and its call to the helper is renamed from 1 to 3. -/
example : linked.map (fun body => body.code.flatMap Op.callees) = [[2, 1], [], [3], []] := by decide

/-- `Root`'s conditional proof, discharged by the library proved alone and relocated. -/
theorem root_composed : rootContract.Holds linked root :=
  composed (specs := [addContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    (fun j bound => by cases j with | zero => exact addLib_closed | succ => simp at bound)
    (fun j bound _ => by cases j with | zero => exact add_holds | succ => simp at bound)

def relocatedCompletion : CIL.Program :=
  { code := [.ret], locals := [], returnsValue := false } ::
    linked.map (CIL.Method.relocate (fun index => index + 1))

theorem root_prefix_relocated : rootContract.Holds relocatedCompletion (root + 1) := by
  have imported : Tests.Imports.Calls.importsAdd linked :=
    add_holds.relocate addLib_closed (link_relocates _ _ (j := 0) (by decide))
  apply MethodContract.relocateGiven (f := fun index => index + 1)
    root_given (link_links _ _) imported (Closed.of_check (by decide))
  intro index bound
  simp [relocatedCompletion, List.getElem?_eq_getElem bound]

#print axioms add_holds
#print axioms root_composed
#print axioms root_prefix_relocated

end Tests.Linking.Calls

/-! `Percent(v) => Check(v)` extracted alone, with the raising `Check` at local index 1. -/
namespace Tests.Linking.Outcomes

open CIL CIL.Safety
open Tests.Imports.Outcomes (percentContract rootContract strictRaises root root_given percentBody)

@[cil_code] def percentEntry : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .ret] }
def percentLib : Library := { entry := percentEntry, helpers := [percentBody] }
@[cil_code] def percentProgram : CIL.Program := [percentEntry, percentBody]

theorem percentLib_closed : Closed percentLib.program := Closed.of_check (by decide)

theorem checkSite.call : percentEntry.code[1]? = some (.call 1 1) := rfl

theorem check_holds : percentContract.Holds percentProgram 1 := by
  rintro v m -
  by_cases within : v ≤ 100
  · have bound : v ≤ 100#64 := within
    simp only [percentContract, within, ite_true]
    refine ⟨10, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
    cil_checked_steps [bound]
  · have bound : ¬ v ≤ 100#64 := within
    simp only [percentContract, within, ite_false]
    cil_raise_steps [bound]

/-- The helper's raise propagates through the entry's local call. -/
theorem percent_holds : percentContract.Holds percentProgram 0 := by
  rintro v m -
  by_cases within : v ≤ 100
  · simp only [percentContract, within, ite_true]
    cil_contract_steps []
    cil_outcome_call check_holds v at checkSite []
    · trivial
    · simp only [percentContract, within, ite_true]
    rintro m1 _ - confined ⟨out, rfl, same⟩
    subst out
    cil_contract_steps []
    exact ⟨confined, _, rfl, rfl⟩
  · simp only [percentContract, within, ite_false]
    cil_raise_steps []
    cil_outcome_raise check_holds v at checkSite []
    · trivial
    · simp only [percentContract, within, ite_false]

@[cil_code] def linked : CIL.Program := link Tests.Imports.Outcomes.Extracted.program [percentLib]

example : linked.map (fun body => body.code.flatMap Op.callees) = [[1], [2], [3], []] := by decide

theorem root_composed : rootContract.Holds linked root :=
  composed (specs := [percentContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    (fun j bound => by cases j with | zero => exact percentLib_closed | succ => simp at bound)
    (fun j bound _ => by cases j with | zero => exact percent_holds | succ => simp at bound)

def relocatedCompletion : CIL.Program :=
  { code := [.ret], locals := [], returnsValue := false } ::
    linked.map (CIL.Method.relocate (fun index => index + 1))

theorem root_prefix_relocated : rootContract.Holds relocatedCompletion (root + 1) := by
  have imported : Tests.Imports.Outcomes.importsPercent linked :=
    percent_holds.relocate percentLib_closed (link_relocates _ _ (j := 0) (by decide))
  apply OutcomeContract.relocateGiven (f := fun index => index + 1)
    root_given (link_links _ _) imported (Closed.of_check (by decide))
  intro index bound
  simp [relocatedCompletion, List.getElem?_eq_getElem bound]

/-- The relocated helper's exception reaches `Root` through two relocated calls. -/
example (m : CIL.Safety.Memory) : Raises linked root [.scalar (.i64 101)] m "System.ArgumentOutOfRangeException" :=
  root_composed.raising (input := 101) trivial (by simp only [rootContract, strictRaises]; decide)

/-- Two libraries: entries fill slots 0 and 1, then each library's helpers follow in order. -/
example : (link [] [Tests.Linking.Calls.addLib, percentLib]).map (fun body => body.code.flatMap Op.callees) =
    [[2], [3], [], []] := by decide

#print axioms check_holds
#print axioms percent_holds
#print axioms root_composed
#print axioms root_prefix_relocated

end Tests.Linking.Outcomes
