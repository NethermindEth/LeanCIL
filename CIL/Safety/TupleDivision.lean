import CIL.Safety.ByteEncoding
import CIL.Safety.Execution

namespace CIL.Safety

theorem wordBytes_eq (word : CIL.W64) : CIL.X86.wordBytes word = numberBytes word.toNat 8 := rfl

theorem wordBytes_length (word : CIL.W64) : (CIL.X86.wordBytes word).length = 8 := by
  simp [CIL.X86.wordBytes]

theorem byteNumber_wordBytes (word : CIL.W64) : byteNumber (CIL.X86.wordBytes word) = word.toNat := by
  rw [wordBytes_eq, byteNumber_numberBytes]
  exact Nat.mod_eq_of_lt word.isLt

/-- `ldfld Item1` on a returned `(ulong, ulong)` reads the first word. -/
theorem item1_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 0 8) (.scalar (.aggregate (CIL.X86.wordBytes first ++ CIL.X86.wordBytes second)) :: rest) m =
      .ok (m, .scalar (.i64 first) :: rest) := by
  have taken : ((CIL.X86.wordBytes first ++ CIL.X86.wordBytes second).drop 0).take 8 = CIL.X86.wordBytes first := by
    simp [wordBytes_length]
  simp only [instruction, List.length_append, wordBytes_length, taken, byteNumber_wordBytes,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `ldfld Item2` on a returned `(ulong, ulong)` reads the second word. -/
theorem item2_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 8 8) (.scalar (.aggregate (CIL.X86.wordBytes first ++ CIL.X86.wordBytes second)) :: rest) m =
      .ok (m, .scalar (.i64 second) :: rest) := by
  have taken : ((CIL.X86.wordBytes first ++ CIL.X86.wordBytes second).drop 8).take 8 = CIL.X86.wordBytes second := by
    simp [wordBytes_length, List.take_of_length_le]
  simp only [instruction, List.length_append, wordBytes_length, taken, byteNumber_wordBytes,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- Under `upper < divisor`, DivRem returns the exact `Nat` quotient and remainder in Item1 and Item2. -/
theorem divRem_fields {lower upper divisor : CIL.W64} (fits : upper.toNat < divisor.toNat)
    (rest : List Value) (m : Memory) :
    ∃ quotient remainder : CIL.W64,
      checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor] =
        .ok (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) ∧
      instruction (.fieldAt 0 8) (.scalar (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) :: rest) m =
        .ok (m, .scalar (.i64 quotient) :: rest) ∧
      instruction (.fieldAt 8 8) (.scalar (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) :: rest) m =
        .ok (m, .scalar (.i64 remainder) :: rest) ∧
      quotient.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) / divisor.toNat ∧
      remainder.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) % divisor.toNat := by
  obtain ⟨quotient, remainder⟩ := CIL.X86.divRem64_fields (lower := lower) fits
  refine ⟨_, _, ?_, item1_of_tuple _ _ rest m, item2_of_tuple _ _ rest m, quotient, remainder⟩
  simp [checkedIntrinsic, CIL.Value.hasUnspecified, CIL.X86.divRemValue, CIL.X86.divRem64_ok fits, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `upper ≥ divisor`, including a zero divisor, is a located arithmetic fault, never a tuple. -/
theorem divRem_fault {lower upper divisor : CIL.W64} (overflows : divisor.toNat ≤ upper.toNat) :
    checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor] =
      .error (.arithmetic (if divisor = 0 then .divideByZero else .overflow)) := by
  simp only [checkedIntrinsic, CIL.X86.divRemValue, CIL.X86.divRem64_fault overflows,
    List.any_cons, List.any_nil, CIL.Value.hasUnspecified, Bool.false_or, Bool.false_eq_true, ite_false,
    Except.mapError, Bind.bind, Except.bind]

#print axioms item1_of_tuple
#print axioms item2_of_tuple
#print axioms divRem_fields
#print axioms divRem_fault
end CIL.Safety
