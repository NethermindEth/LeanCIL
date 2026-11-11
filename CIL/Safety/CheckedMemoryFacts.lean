import CIL.Safety.WordMemory
import CIL.Safety.MemorySteps
import CIL.Safety.InstructionSteps

/-!
# Memory instructions from checked byte operations

These bridges connect successful reads and writes to the existing opcode equations. They
retain all checks of the byte operation, including alignment, initialization and authority.
The `cil_checked` rules also accept these facts during ordinary checked stepping.
-/

namespace CIL.Safety

attribute [cil_checked] storeValue_word64_of_write storeValue_vector128_of_write
  storeValue_vector256_of_write storeValue_vector512_of_write

/-- A 128-bit load reads the complete initialized vector from its checked byte encoding. -/
theorem load_vector128_of_read {memory : Memory} {reference : Reference} {bits : BitVec 128}
    (loaded : read memory reference 16 1 = .ok (numberBytes bits.toNat 16)) :
    loadValue memory (.address reference) 16 = .ok (.v128 bits) := by
  simpa only [numericOfWidth, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    load_scalar_of_read (by decide : ScalarWidth 16) loaded
#print axioms load_vector128_of_read

/-- A 256-bit load reads the complete initialized vector from its checked byte encoding. -/
theorem load_vector256_of_read {memory : Memory} {reference : Reference} {bits : BitVec 256}
    (loaded : read memory reference 32 1 = .ok (numberBytes bits.toNat 32)) :
    loadValue memory (.address reference) 32 = .ok (.v256 bits) := by
  simpa only [numericOfWidth, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    load_scalar_of_read (by decide : ScalarWidth 32) loaded
#print axioms load_vector256_of_read

/-- A 512-bit load reads the complete initialized vector from its checked byte encoding. -/
theorem load_vector512_of_read {memory : Memory} {reference : Reference} {bits : BitVec 512}
    (loaded : read memory reference 64 1 = .ok (numberBytes bits.toNat 64)) :
    loadValue memory (.address reference) 64 = .ok (.v512 bits) := by
  simpa only [numericOfWidth, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    load_scalar_of_read (by decide : ScalarWidth 64) loaded
#print axioms load_vector512_of_read

attribute [cil_checked] load_word64_of_read load_vector128_of_read load_vector256_of_read
  load_vector512_of_read

/-- A checked byte write advances a 128-bit store without assuming initialized destination
    contents. -/
theorem step_store128_of_write {memory after : Memory} {target : Reference} {bits : BitVec 128}
    (written : write memory target (numberBytes bits.toNat 16) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body (.memory .store128) pc args frame
        (.scalar (.v128 bits) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_memory_store128_eq, storeValue_vector128_of_write written]
  rfl
#print axioms step_store128_of_write

/-- A checked byte write advances a 256-bit store without assuming initialized destination
    contents. -/
theorem step_store256_of_write {memory after : Memory} {target : Reference} {bits : BitVec 256}
    (written : write memory target (numberBytes bits.toNat 32) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body (.memory .store256) pc args frame
        (.scalar (.v256 bits) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_memory_store256_eq, storeValue_vector256_of_write written]
  rfl
#print axioms step_store256_of_write

/-- A checked byte write advances a 512-bit store without assuming initialized destination
    contents. -/
theorem step_store512_of_write {memory after : Memory} {target : Reference} {bits : BitVec 512}
    (written : write memory target (numberBytes bits.toNat 64) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body (.memory .store512) pc args frame
        (.scalar (.v512 bits) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_memory_store512_eq, storeValue_vector512_of_write written]
  rfl
#print axioms step_store512_of_write

/-- `store64` through an address whose eight-byte write succeeds steps to that write. The step
    holds in any method and frame. -/
theorem step_store64_of_write {memory after : Memory} {target : Reference} {word : CIL.W64}
    (written : write memory target (numberBytes word.toNat 8) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body .store64 pc args frame
        (.scalar (.i64 word) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_store64_reference_eq, storeValue_word64_of_write written]
  rfl

/-- A 1-, 2- or 4-byte scalar store of an int through an address whose write succeeds steps to
    that write. The step holds in any method and frame. -/
theorem step_storeScalar_of_write {memory after : Memory} {target : Reference} {width : Nat}
    {bits : CIL.W32} (written : write memory target (numberBytes bits.toNat width) 1 = .ok after)
    (narrow : width = 1 ∨ width = 2 ∨ width = 4 := by decide) :
    ∀ body pc args frame rest,
      step body (.storeScalar width) pc args frame
        (.scalar (.i32 bits) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_storeScalar_i32_eq body pc args frame memory width narrow]
  simp [referenceAt, checkedAt, ordinaryAccessAlignment, written, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure]

/-- An eight-byte scalar store of a long through an address whose write succeeds steps to that
    write. The step holds in any method and frame. -/
theorem step_storeScalar_i64_of_write {memory after : Memory} {target : Reference}
    {bits : CIL.W64} (written : write memory target (numberBytes bits.toNat 8) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body (.storeScalar 8) pc args frame
        (.scalar (.i64 bits) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_storeScalar_i64_eq]
  simp [referenceAt, checkedAt, ordinaryAccessAlignment, written, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure]

#print axioms step_store64_of_write
#print axioms step_storeScalar_of_write
#print axioms step_storeScalar_i64_of_write
end CIL.Safety
