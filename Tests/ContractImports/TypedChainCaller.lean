import ExtractedImports
import CIL.Safety.Forwarders

/-! `Chain(in source, out destination)` copies through a local of the imported Pair:
`Library.Copy(in source, out var middle); Library.Copy(in middle, out destination)`. The proof
uses only the imported `copy` contract at both call sites, never the library's body. -/

namespace TypedChainCaller
open CIL.Safety

/-- The chain meets the imported copy contract: the local is fresh frame storage, so only
    `destination` changes in the caller's memory. -/
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => TypedImportInterface.copy.Holds linked 0) := by
  rintro linked links imported ⟨source, destination, value⟩ memory ⟨formed, readable, writable⟩
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : TypedImportInterface.copy.Holds linked 1 := imported
  obtain ⟨middle, entered, made, middleWritable, -⟩ :=
    make_fitting_local memory memory.nextIdentity (.aggregate 8) (.aggregate (List.replicate 8 0))
      formed nofun (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun) (fun _ => nofun)
      nofun (Or.inr rfl)
  let frame : Frame := ⟨memory.nextIdentity, [.bytes (.aggregate 8) middle], [middle.allocation],
    0⟩
  have setup : enterFrame Extracted.method0
      [.reference (.address source), .reference (.address destination)] memory =
        .ok (frame, entered) := by
    simp only [enterFrame, Extracted.method0_opaqueVectorLocals, makeSelectedLocals,
      List.isEmpty_nil, ite_true, Extracted.method0_localKinds, Extracted.method0_locals,
      makeLocals, made,
      Extracted.method0_parameterHomes, makeParameterHomes, List.map_nil, Bind.bind,
      Except.bind, Pure.pure, Except.pure, List.append_nil, frame]
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have entryBelow : MemoryBelow memory.nextIdentity memory entered :=
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ made
  have middleFresh : memory.nextIdentity ≤ middle.allocation := (owned.2 _ (by simp [frame])).1
  have enteredFormed := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ formed made
  have sourceOld := formed.access_bound (read_access readable)
  have destinationOld := formed.access_bound writable
  have sourceEntered : read entered source 8 1 = .ok (numberBytes value.toNat 8) :=
    (entryBelow.read _ sourceOld 8 1).trans readable
  have destinationEntered : access entered destination 8 1 true = .ok () :=
    (entryBelow.access _ destinationOld 8 1 true).trans writable
  have sourceForm := access_reference_valid _ _ _ _ _ (read_access readable)
  have destinationForm := access_reference_valid _ _ _ _ _ writable
  have sourceEnteredForm := access_reference_valid _ _ _ _ _ (read_access sourceEntered)
  have middleForm := access_reference_valid _ _ _ _ _ middleWritable
  obtain ⟨called, output, call⟩ := holds.result (source, middle, value)
    ⟨enteredFormed, sourceEntered, middleWritable⟩
  have firstFormed : called.WellFormed :=
    call.invoked.elim fun _ invoked =>
      invoke_preserves_wellFormed _ _ _ _ _ _ _ enteredFormed invoked
  have firstFramed := call.framed
  have copiedFirst := call.post
  have destinationFirst : access called destination 8 1 true = .ok () :=
    (firstFramed.access_write destination (Nat.lt_of_lt_of_le destinationOld owned.1.next)
      8 1).trans destinationEntered
  have middleFirstForm := access_reference_valid _ _ _ _ _ (read_access copiedFirst)
  have destinationFirstForm := access_reference_valid _ _ _ _ _ destinationFirst
  obtain ⟨called_1, output_1, call_1⟩ := holds.result (middle, destination, value)
    ⟨firstFormed, copiedFirst, destinationFirst⟩
  have lastFramed := call_1.framed
  have copiedLast := call_1.post
  have exitFresh : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => (owned.2 id member).1
  have exitBelow := leaveFrame_preserves_memory_below frame called_1 _ exitFresh
  -- The local's write is fresh frame storage; the destination's is the caller's footprint.
  have framed : Confined [(middle, 8), (destination, 8)] entered called_1 :=
    (firstFramed.widen (by simp [TypedImportInterface.copy])).trans
      (lastFramed.widen (by simp [TypedImportInterface.copy]))
  have confined := Confined.across_frame (footprint := [(destination, 8)]) entryBelow
    owned.1.next framed exitBelow (Nat.le_of_eq (leaveFrame_nextIdentity frame called_1).symm)
    (by
      intro entry member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst same
      · exact .inl middleFresh
      · exact .inr ⟨_, List.mem_singleton_self _, Within.refl _⟩)
  refine MethodContract.Holds.intro (c := TypedImportInterface.copy)
    (input := (source, destination, value)) (leaveFrame frame called_1) () ?_ confined
    ((exitBelow.read _ destinationOld 8 1).trans copiedLast)
  apply (WP.exact_iff (execution := Execution _)).mp
  apply WP.enter found
    (by simp [checkedValue, formValue, checkedAt, sourceForm, destinationForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) setup
  apply WP.step found (by rfl) (by cil_checked_step [sourceEnteredForm])
  apply WP.step found (by rfl) (by cil_checked_step [frame, middleForm])
  apply WP.call found (by rfl)
    (by cil_checked_step [frame, sourceEnteredForm, middleForm, TypedImportInterface.copy])
    ((WP.exact_iff (execution := Execution _)).mpr call.invoked)
  intro final values same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  apply WP.step found (by rfl) (by cil_checked_step [frame, middleFirstForm])
  apply WP.step found (by rfl) (by cil_checked_step [destinationFirstForm])
  apply WP.call found (by rfl)
    (by cil_checked_step [frame, middleFirstForm, destinationFirstForm, TypedImportInterface.copy])
    ((WP.exact_iff (execution := Execution _)).mpr call_1.invoked)
  intro final values same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  apply WP.returned found (by rfl) (by cil_checked_step []) (by rfl)
  rfl
#print axioms correctness
end TypedChainCaller
