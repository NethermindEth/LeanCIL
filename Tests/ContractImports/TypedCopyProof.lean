import Extracted
import TypedImportInterface
import CIL.Safety.WordMemory

namespace TypedCopyProof
open CIL.Safety

def caller : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1
}

/-- `caller` holds one well-formed allocation, its one view, and no object references. -/
theorem caller_formed : caller.WellFormed where
  allocations id allocation found := by
    simp only [caller] at found
    split at found
    · rename_i same
      subst id
      cases found
      exact ⟨by decide, by simp [Allocation.WellFormed, nativeLimit]⟩
    · cases found
  slots _ _ _ held := nomatch held
  views view member := by
    simp only [caller, List.mem_singleton] at member
    subst view
    exact ⟨_, rfl, by decide⟩

#print axioms caller_formed

theorem permitted_alias : TypedImportInterface.copy.pre (⟨0, 0⟩, ⟨0, 0⟩, 0) caller :=
  ⟨caller_formed, by rfl, by rfl⟩

#print axioms permitted_alias

theorem correctness : TypedImportInterface.copy.Holds Extracted.program 0 := by
  rintro ⟨source, destination, value⟩ memory ⟨formed, readable, writable⟩
  dsimp only [TypedImportInterface.copy, MethodContract.Returns] at *
  have width : (numberBytes value.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, wrote⟩ := write_succeeds (bytes := numberBytes value.toNat 8)
    (by simpa only [width] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [width] at readback
  have sourceForm := access_reference_valid _ _ _ _ _ (read_access readable)
  have destinationForm := access_reference_valid _ _ _ _ _ writable
  obtain ⟨_, sourceReady⟩ := access_requirements (read_access readable)
  obtain ⟨_, destinationReady⟩ := access_requirements writable
  have sourceAddress : add memory source 1 (BitVec.ofNat 64 0) = .ok source := by
    simpa using sourceReady.add_slice formed 1 0 8 (by decide) (by decide)
  have destinationAddress : add memory destination 1 (BitVec.ofNat 64 0) = .ok destination := by
    simpa using destinationReady.add_slice formed 1 0 8 (by decide) (by decide)
  have loaded := load_word64_of_read readable
  refine MethodContract.Holds.intro (c := TypedImportInterface.copy)
    (input := (source, destination, value)) result () ?_
    (Confined.write wrote (by simp [TypedImportInterface.copy, width])) readback
  cil_checked_steps [checkedValue, numericValue, instruction, formValue, checkedAt,
    sourceForm, destinationForm, sourceAddress, destinationAddress, loaded, wrote,
    referenceAt, ordinaryAccessAlignment, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

#print axioms correctness
end TypedCopyProof
