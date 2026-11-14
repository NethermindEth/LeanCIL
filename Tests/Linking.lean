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

@[cil_code] def linked : CIL.Program := link Tests.Imports.Calls.Extracted.program [addLib]

/-- The entry fills import slot 0 at index 2 and its call to the helper is renamed from 1 to 3. -/
example : linked.map (fun body => body.code.flatMap Instruction.callees) =
    [[2, 1], [], [3], []] := by decide

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
    add_holds.relocate (f := linkSlot Tests.Imports.Calls.Extracted.program [addLib] 0)
      addLib_closed (link_relocates Tests.Imports.Calls.Extracted.program [addLib] (j := 0) (by decide))
  apply MethodContract.relocateGiven (f := fun index => index + 1)
    root_given (link_links _ _) imported (Closed.of_check (by decide))
  intro index bound
  have found : linked[index]? = some (linked[index]'bound) := List.getElem?_eq_getElem bound
  change (linked.map (CIL.Method.relocate (fun index => index + 1)))[index]? =
    some ((linked[index]'bound).relocate (fun index => index + 1))
  rw [List.getElem?_map, found]
  rfl

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
    cil_contract_steps [bound]
    exact ⟨Confined.refl _ m, _, rfl, rfl⟩
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
    intro m1 out call
    have same := call.post
    subst out
    cil_contract_steps []
    exact MethodContract.Holds.returns call.framed rfl
  · simp only [percentContract, within, ite_false]
    cil_raise_steps []
    cil_outcome_raise check_holds v at checkSite []
    · trivial
    · simp only [percentContract, within, ite_false]

@[cil_code] def linked : CIL.Program := link Tests.Imports.Outcomes.Extracted.program [percentLib]

example : linked.map (fun body => body.code.flatMap Instruction.callees) =
    [[1], [2], [3], []] := by decide

theorem root_composed : rootContract.Holds linked root :=
  composed (specs := [percentContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    (fun j bound => by cases j with | zero => exact percentLib_closed | succ => simp at bound)
    (fun j bound _ => by cases j with | zero => exact percent_holds | succ => simp at bound)

def relocatedCompletion : CIL.Program :=
  { code := [.ret], locals := [], returnsValue := false } ::
    linked.map (CIL.Method.relocate (fun index => index + 1))

theorem root_prefix_relocated : rootContract.Holds relocatedCompletion (root + 1) := by
  have imported : Tests.Imports.Outcomes.importsPercent linked :=
    percent_holds.relocate (f := linkSlot Tests.Imports.Outcomes.Extracted.program [percentLib] 0)
      percentLib_closed (link_relocates Tests.Imports.Outcomes.Extracted.program [percentLib] (j := 0) (by decide))
  apply OutcomeContract.relocateGiven (f := fun index => index + 1)
    root_given (link_links _ _) imported (Closed.of_check (by decide))
  intro index bound
  have found : linked[index]? = some (linked[index]'bound) := List.getElem?_eq_getElem bound
  change (linked.map (CIL.Method.relocate (fun index => index + 1)))[index]? =
    some ((linked[index]'bound).relocate (fun index => index + 1))
  rw [List.getElem?_map, found]
  rfl

/-- The relocated helper's exception reaches `Root` through two relocated calls. -/
example (m : CIL.Safety.Memory) : Raises linked root [.scalar (.i64 101)] m "System.ArgumentOutOfRangeException" :=
  root_composed.raising (input := 101) trivial (by simp only [rootContract, strictRaises]; decide)

/-- Two libraries: entries fill slots 0 and 1, then each library's helpers follow in order. -/
example : (link [] [Tests.Linking.Calls.addLib, percentLib]).map
    (fun body => body.code.flatMap Instruction.callees) =
    [[2], [3], [], []] := by decide

#print axioms check_holds
#print axioms percent_holds
#print axioms root_composed
#print axioms root_prefix_relocated

end Tests.Linking.Outcomes

/-! A relocated body's link table is renamed with its code. -/
namespace Tests.Linking.Links

open CIL

def body : Method := {
  code := [.arg 0, .call 1 1, .pop, .callVirtual [(.void, 2)] 1, .newAggregate 3 0 8, .ret]
  locals := [], returnsValue := false }

/-- Direct, virtual and aggregate entries all move by the renaming. -/
example : (body.relocate (· + 10)).links =
    [(1, .direct 11), (3, .virtual [(.void, 12)]), (4, .aggregate 13 8)] := rfl

/-- The pcs of the entries stay. -/
example : (body.relocate (· + 10)).links.map Prod.fst = body.links.map Prod.fst := rfl

example : (body.relocate (· + 10)).linkAt 1 = some (.direct 11) := rfl

/-- A relocated catalog keeps its identities and renames only the body indices. -/
example (identity : ManagedIdentity) :
    (Link.indirect [⟨identity, 2⟩]).relocate (· + 5) = .indirect [⟨identity, 7⟩] := rfl

/-- A body made with `withCode` has implied links, and so does its relocation. -/
example (f : Nat → Nat) (method : Method) (code : List Instruction) :
    let relocated := (method.withCode code).relocate f
    relocated.links = linksOfCode relocated.code :=
  Method.relocate_links_implied f _ rfl

end Tests.Linking.Links

/-! How a proof reads `linkAt` for an extracted method, a template and a literal body. -/
namespace Tests.Linking.Resolution

open CIL

/-- The link of the call at pc 1, named and tagged as an extraction names it. -/
@[cil_code] def callLink : Link := .direct 3

/-- An extraction's method: its table and call-site fact are generated, with the table explicit. -/
def extracted : Method := {
  code := [.arg 0, .call 3 1, .pop, .ret], locals := [], returnsValue := false
  links := [(1, callLink)] }

/-- The generated fact of the table. -/
@[cil_code] theorem extracted_links : extracted.links = [(1, callLink)] := rfl

/-- The generated fact of the call site at pc 1. -/
@[cil_code] theorem extracted_link1 : extracted.linkAt 1 = some callLink := rfl

/-- A call site: the generated fact and the tagged link definition reach the constructor, so the
    match of a stepping-style read reduces under `simp only [cil_code]`. -/
example : (match extracted.linkAt 1 with | some (.direct callee) => callee | _ => 0) = 3 := by
  simp only [cil_code]

/-- A pc that is not a call site: no fact exists, and the table is read by the listed keys. -/
example : extracted.linkAt 0 = none :=
  Method.linkAt_of_unlisted (by simp [extracted_links])

/-- The same read through a scan of the table, which is bounded by the number of calls. -/
example : extracted.linkAt 2 = none := by
  simp [Method.linkAt, linkLookup, extracted_links]

/-- A literal body with its default table: one step from an instruction fact. -/
def literal : Method :=
  { code := [.arg 0, .call 3 1, .pop, .ret], locals := [], returnsValue := false }

/-- The instruction fact of the call, as `cil_instruction_equations` states it. -/
theorem literal_at1 : literal.code[1]? = some (.call 3 1) := rfl

/-- The instruction fact of a pc without a call. -/
theorem literal_at0 : literal.code[0]? = some (.arg 0) := rfl

example : literal.linkAt 1 = some (.direct 3) := by
  rw [Method.linkAt_of_instruction rfl literal_at1]; rfl

example : literal.linkAt 0 = none := by
  rw [Method.linkAt_of_instruction rfl literal_at0]; rfl

/-- Evaluation also reads it, at the cost of rebuilding the implied table. -/
example : literal.linkAt 1 = some (.direct 3) := rfl

/-- A template body takes its callee as a parameter, so its read stays symbolic. -/
def template (profile : FeatureProfile) (callee : Nat) : Method :=
  { profile, code := [.arg 0, .call callee 1, .pop, .ret], locals := [], returnsValue := false }

example (profile : FeatureProfile) (callee : Nat) :
    (template profile callee).linkAt 1 = some (.direct callee) :=
  (Method.linkAt_of_instruction rfl (pc := 1) (op := .call callee 1) rfl).trans rfl

example (profile : FeatureProfile) (callee : Nat) : (template profile callee).linkAt 2 = none :=
  (Method.linkAt_of_instruction rfl (pc := 2) (op := .pop) rfl).trans rfl

/-- A body built with `withCode` reads the links of its new code. -/
example : (literal.withCode [.call 5 0, .ret]).linkAt 0 = some (.direct 5) := rfl

end Tests.Linking.Resolution
