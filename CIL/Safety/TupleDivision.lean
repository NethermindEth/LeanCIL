import CIL.Safety.ByteEncoding
import CIL.Safety.Execution

/-!
# DivRem tuples

`X86Base.DivRem` on 64-bit words returns a `(ulong, ulong)` aggregate. These lemmas read
its `Item1` and `Item2` fields back as the exact `Nat` quotient and remainder of the
128-bit dividend, and show that an overflowing or zero divisor is an arithmetic fault in
the checked interpreter, never a tuple. `Math.DivRem(int, int)` returns its `(int, int)` pair
through the same aggregate encoding, with `divRemBits` faults reported unchanged.
-/

namespace CIL.Safety

theorem wordBytes_eq (word : CIL.W64) : CIL.X86.wordBytes word = numberBytes word.toNat 8 := rfl

theorem wordBytes_length (word : CIL.W64) : (CIL.X86.wordBytes word).length = 8 := by
  simp [CIL.X86.wordBytes, CIL.littleEndianBytes]

theorem byteNumber_wordBytes (word : CIL.W64) :
    byteNumber (CIL.X86.wordBytes word) = word.toNat := by
  rw [wordBytes_eq, byteNumber_numberBytes]
  exact Nat.mod_eq_of_lt word.isLt

/-- `ldfld Item1` on a returned `(ulong, ulong)` reads the first word. -/
theorem item1_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 0 8)
      (.scalar (.aggregate (CIL.X86.wordBytes first ++ CIL.X86.wordBytes second)) :: rest) m =
      .ok (m, .scalar (.i64 first) :: rest) := by
  have taken : ((CIL.X86.wordBytes first ++ CIL.X86.wordBytes second).drop 0).take 8 =
      CIL.X86.wordBytes first := by
    simp [wordBytes_length]
  simp only [instruction, List.length_append, wordBytes_length, taken, byteNumber_wordBytes,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `ldfld Item2` on a returned `(ulong, ulong)` reads the second word. -/
theorem item2_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 8 8)
      (.scalar (.aggregate (CIL.X86.wordBytes first ++ CIL.X86.wordBytes second)) :: rest) m =
      .ok (m, .scalar (.i64 second) :: rest) := by
  have taken : ((CIL.X86.wordBytes first ++ CIL.X86.wordBytes second).drop 8).take 8 =
      CIL.X86.wordBytes second := by
    simp [wordBytes_length, List.take_of_length_le]
  simp only [instruction, List.length_append, wordBytes_length, taken, byteNumber_wordBytes,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- Under `upper < divisor`, DivRem returns the exact `Nat` quotient and remainder in Item1
    and Item2. -/
theorem divRem_fields {lower upper divisor : CIL.W64} (fits : upper.toNat < divisor.toNat)
    (rest : List Value) (m : Memory) :
    ∃ quotient remainder : CIL.W64,
      checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor] =
        .ok (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) ∧
      instruction (.fieldAt 0 8)
          (.scalar (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) ::
            rest) m =
        .ok (m, .scalar (.i64 quotient) :: rest) ∧
      instruction (.fieldAt 8 8)
          (.scalar (.aggregate (CIL.X86.wordBytes quotient ++ CIL.X86.wordBytes remainder)) ::
            rest) m =
        .ok (m, .scalar (.i64 remainder) :: rest) ∧
      quotient.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) / divisor.toNat ∧
      remainder.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) % divisor.toNat := by
  obtain ⟨quotient, remainder⟩ := CIL.X86.divRem64_fields (lower := lower) fits
  refine ⟨_, _, ?_, item1_of_tuple _ _ rest m, item2_of_tuple _ _ rest m, quotient, remainder⟩
  simp [checkedIntrinsic, CIL.Value.hasUnspecified, CIL.X86.divRemValue,
    CIL.X86.divRem64_ok fits, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `upper ≥ divisor`, including a zero divisor, is a located arithmetic fault, never a tuple. -/
theorem divRem_fault {lower upper divisor : CIL.W64} (overflows : divisor.toNat ≤ upper.toNat) :
    checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor] =
      .error (.arithmetic (if divisor = 0 then .divideByZero else .overflow)) := by
  simp only [checkedIntrinsic, CIL.X86.divRemValue, CIL.X86.divRem64_fault overflows,
    List.any_cons, List.any_nil, CIL.Value.hasUnspecified, Bool.false_or, Bool.false_eq_true,
    ite_false, Except.mapError, Bind.bind, Except.bind]

/-- Checked `Math.DivRem(int, int)` encodes `divRemBits` as Item1 at 0 and Item2 at 4, and
    reports its `div` faults as arithmetic faults. -/
theorem mathDivRem32_eq (signed : Bool) (left right : CIL.W32) :
    checkedIntrinsic (.scalar (.divRem 32 signed)) [.i32 left, .i32 right] =
      ((CIL.divRemBits signed left right).map fun (quotient, remainder) =>
        CIL.Value.aggregate (CIL.littleEndianBytes 4 quotient.toNat ++
          CIL.littleEndianBytes 4 remainder.toNat)).mapError .arithmetic := by
  simp only [checkedIntrinsic, CIL.evalDivRem, CIL.evalDivRem.tuple, BitVec.setWidth_eq,
    List.any_cons, List.any_nil, CIL.Value.hasUnspecified, Bool.false_or, Bool.false_eq_true,
    ite_false, Bool.or_true, ite_true]
  cases CIL.divRemBits signed left right <;> rfl

/-- `ldfld Item1` on a returned `(int, int)` reads the quotient's four bytes back exactly. -/
theorem item1_of_int_tuple (first second : CIL.W32) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 0 4)
      (.scalar (.aggregate (CIL.littleEndianBytes 4 first.toNat ++
        CIL.littleEndianBytes 4 second.toNat)) :: rest) m =
      .ok (m, .scalar (.i32 first) :: rest) := by
  have length (word : CIL.W32) : (CIL.littleEndianBytes 4 word.toNat).length = 4 := by
    simp [CIL.littleEndianBytes]
  have taken : ((CIL.littleEndianBytes 4 first.toNat ++
      CIL.littleEndianBytes 4 second.toNat).drop 0).take 4 =
      CIL.littleEndianBytes 4 first.toNat := by
    simp [length]
  have number : byteNumber (CIL.littleEndianBytes 4 first.toNat) = first.toNat := by
    rw [show CIL.littleEndianBytes 4 first.toNat = numberBytes first.toNat 4 from rfl,
      byteNumber_numberBytes]
    exact Nat.mod_eq_of_lt first.isLt
  simp only [instruction, List.length_append, length, taken, number, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rfl

#print axioms mathDivRem32_eq
#print axioms item1_of_int_tuple
#print axioms item1_of_tuple
#print axioms item2_of_tuple
#print axioms divRem_fields
#print axioms divRem_fault
end CIL.Safety
