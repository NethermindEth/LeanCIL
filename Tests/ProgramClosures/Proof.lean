import Extracted
import Lean
import CIL
import CIL.MethodIdentity

/-!
# A summary proved once over its closure and applied in other programs

`Closure::AddTwo` returns its argument plus two by calling `Bump` and `Nudge`, which have the
same body. Its contract is stepped once in the extraction, carried to the closure of `AddTwo`,
bound there to the closure's records, and carried from the closure back to the extraction, to a
program that holds the closure at other indices. The executable contract also holds when
`Bump` and `Nudge` share an index, but their distinct tokens prevent decoding that binding.
Relocations into a program with other bytes at an index
`AddTwo` links to, and into one holding `AddTwo` and `Bump`, whose bodies differ, at one index,
are refuted.
-/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

bind_method addTwo addTwoBody := "System.UInt64 Closure::AddTwo(System.UInt64)"

/-- `AddTwo` returns its argument plus two and changes no memory. -/
def addTwoContract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x + 2 ∧ final = initial

/-- `AddTwo` meets its contract in the extraction, stepping both calls. -/
theorem addTwo_holds : addTwoContract.Holds Extracted.program addTwo := by
  rintro x memory -
  refine MethodContract.Holds.intro memory (x + 1 + 1) ?_ (Confined.refl _ _) ⟨by bv_omega, rfl⟩
  cil_checked_steps
#print axioms addTwo_holds

/-- Every record's pinned bytes decode to the method at its index of the extraction. -/
theorem bodies_decode :
    decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
  decodedProgram?_eq_some Extracted.translation_valid.programBindingsValid
    (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded)
      (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
          Extracted.method1_decoded)
        (.cons ((Method.ofBody?_of_decodes Extracted.method2_body_validated).trans
            Extracted.method2_decoded)
          (.cons ((Method.ofBody?_of_decodes Extracted.method3_body_validated).trans
              Extracted.method3_decoded) .nil))))
#print axioms bodies_decode

/-- The methods `AddTwo` reaches, renumbered from `AddTwo` at 0, with their indices here. -/
def closure : Program × List Nat :=
  (closureWith Extracted.programIndex.get? Extracted.programLength addTwo).getD ([], [])

/-- The closure of `AddTwo` is found. -/
theorem closure_found : Extracted.program.closure addTwo = some closure := by
  rw [Program.closure_eq_closureWith Extracted.programIndex_get? Extracted.programLength_eq]
  cil_kernel_rfl
#print axioms closure_found

/-- The closure holds `AddTwo`, then its callees in the order its link table enters them. -/
theorem closure_indices : closure.2 = [1, 3, 2] := by decide +kernel
#print axioms closure_indices

/-- The index in the extraction of each method of the closure. -/
def here (slot : Nat) : Nat := closure.2.getD slot 0

/-- The closure's first method is `AddTwo`. -/
theorem here_first : here 0 = addTwo := by
  unfold here
  rw [closure_indices]
  rfl
#print axioms here_first

/-- The closure's records, read from the extraction's in closure order. -/
def records : List MethodEvidence :=
  (Extracted.program.closureEvidence Extracted.methodEvidence addTwo).getD []

/-- The closure's records are found. -/
theorem records_found :
    Extracted.program.closureEvidence Extracted.methodEvidence addTwo = some records := by
  cil_kernel_rfl
#print axioms records_found

/-- The closure has one record per method. -/
theorem records_length : records.length = 3 := by decide +kernel
#print axioms records_length

/-- The closure's records decode to the closure. -/
theorem closure_decodes :
    decodedProgram? Extracted.profile Extracted.environment records = some closure.1 :=
  Program.closureEvidence_decodes bodies_decode closure_found records_found
#print axioms closure_decodes

/-- The contract of `AddTwo` holds in its closure alone. -/
theorem closure_holds : addTwoContract.Holds closure.1 0 :=
  MethodContract.Holds.restrict (f := here) (here_first ▸ addTwo_holds)
    (Program.closure_closed closure_found) (Program.closure_relocates closure_found).1
    (by decide +kernel)
#print axioms closure_holds

/-- The record of `AddTwo` in the closure: the extraction's, with its links renumbered. -/
def addTwoRecord : MethodEvidence :=
  (Extracted.methodEvidence[addTwo]'(by decide)).relocateLinks
    (Extracted.program.closureSearch addTwo).position

/-- The closure's first record is `AddTwo`'s. -/
theorem first_record : records[0]? = some addTwoRecord := by cil_kernel_rfl
#print axioms first_record

/-- The summary of `AddTwo`, proved once over its closure. -/
theorem closure_summary :
    DecodedSummary closure.1 records Extracted.profile Extracted.environment 0
      addTwoRecord.assembly addTwoRecord.original.token addTwoRecord.arguments addTwoContract :=
  .of_decoded closure_decodes first_record ⟨_, Extracted.method1_body_validated⟩
    Extracted.method1_specialization_validated.1
    closure_holds
#print axioms closure_summary

/-- The summary of the closure is a summary of `AddTwo` in the extraction. -/
theorem summary_here :
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment (here 0) addTwoRecord.assembly addTwoRecord.original.token
      addTwoRecord.arguments addTwoContract :=
  closure_summary.relocate (Program.closure_closed closure_found)
    (Program.closure_relocates closure_found).1 bodies_decode fun item found => by
      obtain rfl := Option.some.inj (first_record.symm.trans found)
      refine ⟨Extracted.methodEvidence[addTwo]'(by decide), ?_, rfl, rfl, rfl, rfl, ⟨_, Extracted.method1_body_validated⟩⟩
      rw [here_first]
      exact List.getElem?_eq_getElem _
#print axioms summary_here

/-- `Entry` returns its argument plus two and leaves memory as it was, through the summary of
    `AddTwo` carried from its closure. -/
theorem correctness (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 (x + 2))]) := by
  have held : addTwoContract.Holds Extracted.program addTwo := here_first ▸ summary_here.holds
  refine (WP.exact_iff (execution := Execution fun fuel =>
    invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory)).mp ?_
  cil_contract_steps [held, addTwoContract] with final value added
  obtain ⟨rfl, rfl⟩ := added.post
  rfl
#print axioms correctness

/-- The record at `slot` of the closure. -/
def record (slot : Nat) (bound : slot < 3) : MethodEvidence :=
  records[slot]'(records_length ▸ bound)

/-- The index of each closure method in a second program: `AddTwo` at 3 and its callees at 0
    and 2, with `Entry` at 1. -/
def elsewhere (slot : Nat) : Nat := [3, 0, 2].getD slot 0

/-- The records of the second program, each with its links renamed into it. -/
def elsewhereEvidence : List MethodEvidence :=
  [(record 1 (by decide)).relocateLinks elsewhere,
    (Extracted.methodEvidence[0]'(by decide)).relocateLinks fun index => [1, 3, 2, 0].getD index 0,
    (record 2 (by decide)).relocateLinks elsewhere,
    addTwoRecord.relocateLinks elsewhere]

/-- The second program: `Bump`, `Entry` calling index 3, `Nudge`, and `AddTwo` calling indices
    0 and 2. -/
def elsewhereProgram : Program :=
  [Extracted.method3, { Extracted.method0 with links := [(1, .direct 3)] }, Extracted.method2,
    { Extracted.method1 with links := [(1, .direct 0), (2, .direct 2)] }]

/-- The second program's records decode to it. -/
theorem elsewhere_decodes :
    decodedProgram? Extracted.profile Extracted.environment elsewhereEvidence =
      some elsewhereProgram := by
  cil_kernel_rfl
#print axioms elsewhere_decodes

/-- The second program holds each closure method at the index `elsewhere` gives it. -/
theorem elsewhere_relocates : RelocatesInto closure.1 elsewhereProgram elsewhere :=
  RelocatesInto.of_decoded closure_decodes elsewhere_decodes fun slot bound => by
    rw [records_length] at bound
    match slot, bound with
    | 0, _ => exact ⟨addTwoRecord, addTwoRecord.relocateLinks elsewhere, first_record, rfl,
        MethodEvidence.ofBody?_relocateLinks _ _ _ _⟩
    | 1, bound | 2, bound => exact ⟨record _ bound, (record _ bound).relocateLinks elsewhere,
        List.getElem?_eq_getElem _, rfl, MethodEvidence.ofBody?_relocateLinks _ _ _ _⟩
#print axioms elsewhere_relocates

/-- The summary of the closure is a summary of `AddTwo` at index 3 of the second program. -/
theorem summary_elsewhere :
    DecodedSummary elsewhereProgram elsewhereEvidence Extracted.profile Extracted.environment
      (elsewhere 0) addTwoRecord.assembly addTwoRecord.original.token addTwoRecord.arguments
      addTwoContract :=
  closure_summary.relocate (Program.closure_closed closure_found) elsewhere_relocates
    elsewhere_decodes fun item found => by
      obtain rfl := Option.some.inj (first_record.symm.trans found)
      exact ⟨addTwoRecord.relocateLinks elsewhere, rfl, rfl, rfl, rfl, rfl,
        ⟨_, Extracted.method1_body_validated⟩⟩
#print axioms summary_elsewhere

/-- In the second program, `Entry` returns its argument plus two and leaves memory as it was,
    through the contract of `AddTwo` carried there from its closure. -/
theorem correctness_elsewhere (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke elsewhereProgram fuel 1 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 (x + 2))]) := by
  have held : addTwoContract.Holds elsewhereProgram 3 := summary_elsewhere.holds
  refine (WP.exact_iff (execution := Execution fun fuel =>
    invoke elsewhereProgram fuel 1 [.scalar (.i64 x)] memory)).mp ?_
  cil_contract_steps [held, addTwoContract] with final value added
  obtain ⟨rfl, rfl⟩ := added.post
  rfl
#print axioms correctness_elsewhere

/-- The two callees of `AddTwo` decode to the same method. -/
theorem callees_agree : closure.1[1]? = closure.1[2]? := by cil_kernel_rfl
#print axioms callees_agree

/-- The index of each closure method in a third program: `AddTwo` at 2 and both its callees at
    0, with `Entry` at 1. -/
def collapse (slot : Nat) : Nat := [2, 0, 0].getD slot 0

/-- The records of the third program, each with its links renamed into it. -/
def collapsedEvidence : List MethodEvidence :=
  [(record 1 (by decide)).relocateLinks collapse,
    (Extracted.methodEvidence[0]'(by decide)).relocateLinks fun index => [1, 2, 0, 0].getD index 0,
    addTwoRecord.relocateLinks collapse]

/-- The third program: `Bump`, `Entry` calling index 2, and `AddTwo` calling index 0 twice. -/
def collapsedProgram : Program :=
  [Extracted.method3, { Extracted.method0 with links := [(1, .direct 2)] },
    { Extracted.method1 with links := [(1, .direct 0), (2, .direct 0)] }]

/-- Collapsing distinct metadata tokens onto one slot fails the decoded call check. -/
theorem collapsed_bindings_refused :
    decodedProgram? Extracted.profile Extracted.environment collapsedEvidence = none := by
  cil_kernel_rfl
#print axioms collapsed_bindings_refused

/-- The two callees still have identical executable bodies after renumbering. -/
theorem collapsed_relocates : RelocatesInto closure.1 collapsedProgram collapse := by
  intro slot bound
  have size : closure.1.length = 3 := by decide +kernel
  rw [size] at bound
  match slot, bound with
  | 0, _ | 1, _ | 2, _ => rfl
#print axioms collapsed_relocates

/-- In the third program, `Entry` returns its argument plus two and leaves memory as it was,
    through the contract of `AddTwo` carried there from its closure. -/
theorem correctness_collapsed (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke collapsedProgram fuel 1 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 (x + 2))]) := by
  have held : addTwoContract.Holds collapsedProgram 2 :=
    closure_holds.relocate (Program.closure_closed closure_found) collapsed_relocates
  refine (WP.exact_iff (execution := Execution fun fuel =>
    invoke collapsedProgram fuel 1 [.scalar (.i64 x)] memory)).mp ?_
  cil_contract_steps [held, addTwoContract] with final value added
  obtain ⟨rfl, rfl⟩ := added.post
  rfl
#print axioms correctness_collapsed

/-- A fourth program that holds the closure where the second does, except that `Entry`'s
    record stands at index 0, where `elsewhere` sends `Bump`. -/
def otherBytesEvidence : List MethodEvidence :=
  [(Extracted.methodEvidence[0]'(by decide)).relocateLinks fun index => [1, 3, 2, 0].getD index 0,
    (Extracted.methodEvidence[0]'(by decide)).relocateLinks fun index => [1, 3, 2, 0].getD index 0,
    (record 2 (by decide)).relocateLinks elsewhere,
    addTwoRecord.relocateLinks elsewhere]

/-- The fourth program with Entry's executable body in Bump's slot. -/
def otherBytesProgram : Program :=
  elsewhereProgram.set 0 { Extracted.method0 with links := [(1, .direct 3)] }

/-- The call to Bump cannot bind to Entry's record. -/
theorem other_bytes_bindings_refused :
    decodedProgram? Extracted.profile Extracted.environment otherBytesEvidence = none := by
  cil_kernel_rfl
#print axioms other_bytes_bindings_refused

/-- No relocation into the fourth program sends `Bump` to index 0, whose bytes are `Entry`'s. -/
theorem other_bytes_refused : ¬ RelocatesInto closure.1 otherBytesProgram elsewhere := by
  intro relocates
  have bump := congrArg (Option.map fun method => method.code.length) (relocates 1 (by decide))
  revert bump
  decide +kernel
#print axioms other_bytes_refused

/-- The index of each closure method in a fifth program: `AddTwo` and `Bump`, whose bodies
    differ, at 2, and `Nudge` at 0. -/
def merge (slot : Nat) : Nat := [2, 2, 0].getD slot 0

/-- The records of the fifth program, each with its links renamed into it. -/
def mergedEvidence : List MethodEvidence :=
  [(record 2 (by decide)).relocateLinks merge,
    (Extracted.methodEvidence[0]'(by decide)).relocateLinks fun index => [1, 2, 2, 0].getD index 0,
    addTwoRecord.relocateLinks merge]

/-- The fifth program, with AddTwo occupying the slot of its first callee. -/
def mergedProgram : Program :=
  [Extracted.method2, { Extracted.method0 with links := [(1, .direct 2)] },
    { Extracted.method1 with links := [(1, .direct 2), (2, .direct 0)] }]

/-- The call to Bump cannot bind to AddTwo's record. -/
theorem merged_bindings_refused :
    decodedProgram? Extracted.profile Extracted.environment mergedEvidence = none := by
  cil_kernel_rfl
#print axioms merged_bindings_refused

/-- No relocation sends `AddTwo` and `Bump` to one index, since their bodies differ. -/
theorem differing_merge_refused : ¬ RelocatesInto closure.1 mergedProgram merge := by
  intro relocates
  have bump := congrArg (Option.map fun method => method.code.length) (relocates 1 (by decide))
  revert bump
  decide +kernel
#print axioms differing_merge_refused

-- A theorem left unproved would still print its axioms; this check fails instead.
open Lean in
run_cmd do
  for name in [``addTwo_holds, ``bodies_decode, ``closure_found, ``closure_indices, ``here_first,
      ``records_found, ``records_length, ``closure_decodes, ``closure_holds, ``first_record,
      ``closure_summary, ``summary_here, ``correctness, ``elsewhere_decodes,
      ``elsewhere_relocates, ``summary_elsewhere, ``correctness_elsewhere, ``callees_agree,
      ``collapsed_bindings_refused, ``collapsed_relocates, ``correctness_collapsed,
      ``other_bytes_bindings_refused, ``other_bytes_refused, ``merged_bindings_refused,
      ``differing_merge_refused] do
    if (← collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on sorryAx"

end ExampleProof
