import Extracted
import TypedImportInterface
import CIL.Safety.WordMemory
import Examples.Support

namespace TypedCopyProof
open CIL.Safety

theorem permitted_alias : TypedImportInterface.copy.pre (⟨0, 0⟩, ⟨0, 0⟩, 0) Examples.caller := by
  refine ⟨?_, by rfl, by rfl⟩
  constructor
  · intro id allocation found
    simp only [Examples.caller] at found
    split at found
    · rename_i same
      subst id
      cases found
      exact ⟨by decide, by simp [Allocation.WellFormed, nativeLimit]⟩
    · cases found
  · intro view member
    simp only [Examples.caller, List.mem_singleton] at member
    subst view
    exact ⟨_, rfl, by decide⟩

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
  refine ⟨CIL.executionBound Extracted.program 0, result, [], ?_,
    Confined.write wrote (by simp only [width, List.mem_singleton]), (), rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, instruction, formValue, checkedAt,
    sourceForm, destinationForm, sourceAddress, destinationAddress, loaded, wrote,
    referenceAt, ordinaryAccessAlignment, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

#print axioms correctness
end TypedCopyProof
