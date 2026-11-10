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
    [], 0⟩
  have setup : enterFrame Extracted.method0
      [.reference (.address source), .reference (.address destination)] memory =
        .ok (frame, entered) := by
    simp only [enterFrame, Extracted.method0_opaqueVectorLocals, makeSelectedLocals,
      List.isEmpty_nil, ite_true, Extracted.method0_localKinds, Extracted.method0_locals,
      makeLocals, made, Extracted.method0_vectorArgs, makeArgumentHomes,
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
  have destinationEnteredForm := access_reference_valid _ _ _ _ _ destinationEntered
  have middleForm := access_reference_valid _ _ _ _ _ middleWritable
  dsimp only [TypedImportInterface.copy, MethodContract.Returns]
  apply WP.adequate.mpr
  refine invoke_exists_of_run found
    (by simp [checkedValue, formValue, checkedAt, sourceForm, destinationForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) setup ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[0]? = some (.arg 0))
    (by cil_checked_step [checkedValue, formValue, checkedAt, sourceEnteredForm,
      Except.mapError]) ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[1]? = some (.localAddr 0))
    (by simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, frame, List.getElem?_cons_zero,
      localAddress, formValue, checkedAt, middleForm, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]; rfl) ?_
  refine run_call_of_contract_formed holds (source, middle, value) found
    (by rfl : Extracted.method0.code[2]? = some (.call 1 2))
    (by cil_checked_step [formValue, sourceEnteredForm, middleForm,
      TypedImportInterface.copy, Except.mapError]) rfl
    ⟨enteredFormed, sourceEntered, middleWritable⟩ enteredFormed ?_
  intro first _ firstCall firstKept
  have firstFormed := firstKept.formed
  have firstFramed := firstCall.framed
  have copiedFirst := firstCall.post
  have destinationFirst : access first destination 8 1 true = .ok () :=
    (firstFramed.access_write destination (Nat.lt_of_lt_of_le destinationOld owned.1.next)
      8 1).trans destinationEntered
  have middleFirstForm := access_reference_valid _ _ _ _ _ (read_access copiedFirst)
  have destinationFirstForm := access_reference_valid _ _ _ _ _ destinationFirst
  refine run_next_exists _ found (by rfl : Extracted.method0.code[3]? = some (.localAddr 0))
    (by simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero,
      localAddress, formValue, checkedAt, middleFirstForm, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]; rfl) ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[4]? = some (.arg 1))
    (by cil_checked_step [checkedValue, formValue, checkedAt, destinationFirstForm,
      Except.mapError]) ?_
  refine run_call_of_contract_formed holds (middle, destination, value) found
    (by rfl : Extracted.method0.code[5]? = some (.call 1 2))
    (by cil_checked_step [formValue, middleFirstForm, destinationFirstForm,
      TypedImportInterface.copy, Except.mapError]) rfl
    ⟨firstFormed, copiedFirst, destinationFirst⟩ firstFormed ?_
  intro last _ lastCall _
  have lastFramed := lastCall.framed
  have copiedLast := lastCall.post
  have exitFresh : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => (owned.2 id member).1
  have exitBelow := leaveFrame_preserves_memory_below frame last _ exitFresh
  -- The local's write is fresh frame storage; the destination's is the caller's footprint.
  have framed : Confined [(middle, 8), (destination, 8)] entered last :=
    (firstFramed.widen (by simp [TypedImportInterface.copy])).trans
      (lastFramed.widen (by simp [TypedImportInterface.copy]))
  have confined := Confined.across_frame (footprint := [(destination, 8)]) entryBelow
    owned.1.next framed exitBelow (Nat.le_of_eq (leaveFrame_nextIdentity frame last).symm)
    (by
      intro entry member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst same
      · exact .inl middleFresh
      · exact .inr ⟨_, List.mem_singleton_self _, Within.refl _⟩)
  refine run_return_exists found (by rfl : Extracted.method0.code[6]? = some (.ret none))
    (by cil_checked_step []) (by rfl) ?_
  exact ⟨confined, (), rfl, (exitBelow.read _ destinationOld 8 1).trans copiedLast⟩

#print axioms correctness
end TypedChainCaller
