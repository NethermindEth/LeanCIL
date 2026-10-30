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

/-- An eight-byte field encoding a 64-bit word decodes back to that word. -/
theorem byteNumber_numberBytes_word (word : CIL.W64) :
    byteNumber (numberBytes word.toNat 8) = word.toNat := by
  rw [byteNumber_numberBytes]
  exact Nat.mod_eq_of_lt word.isLt

/-- `ldfld Item1` on a returned `(ulong, ulong)` reads the first word. -/
theorem item1_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 0 8)
      (.scalar (.aggregate (numberBytes first.toNat 8 ++ numberBytes second.toNat 8)) :: rest) m =
      .ok (m, .scalar (.i64 first) :: rest) := by
  have taken : ((numberBytes first.toNat 8 ++ numberBytes second.toNat 8).drop 0).take 8 =
      numberBytes first.toNat 8 := by
    simp [numberBytes_length]
  simp only [instruction, List.length_append, numberBytes_length, taken,
    byteNumber_numberBytes_word, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `ldfld Item2` on a returned `(ulong, ulong)` reads the second word. -/
theorem item2_of_tuple (first second : CIL.W64) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 8 8)
      (.scalar (.aggregate (numberBytes first.toNat 8 ++ numberBytes second.toNat 8)) :: rest) m =
      .ok (m, .scalar (.i64 second) :: rest) := by
  have taken : ((numberBytes first.toNat 8 ++ numberBytes second.toNat 8).drop 8).take 8 =
      numberBytes second.toNat 8 := by
    simp [numberBytes_length, List.take_of_length_le]
  simp only [instruction, List.length_append, numberBytes_length, taken,
    byteNumber_numberBytes_word, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- Under `upper < divisor`, DivRem returns the exact `Nat` quotient and remainder in Item1
    and Item2. -/
theorem divRem_fields {lower upper divisor : CIL.W64} (fits : upper.toNat < divisor.toNat)
    (rest : List Value) (m : Memory) :
    ∃ quotient remainder : CIL.W64,
      checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor] =
        .ok (.aggregate (numberBytes quotient.toNat 8 ++ numberBytes remainder.toNat 8)) ∧
      instruction (.fieldAt 0 8)
          (.scalar (.aggregate (numberBytes quotient.toNat 8 ++ numberBytes remainder.toNat 8)) ::
            rest) m =
        .ok (m, .scalar (.i64 quotient) :: rest) ∧
      instruction (.fieldAt 8 8)
          (.scalar (.aggregate (numberBytes quotient.toNat 8 ++ numberBytes remainder.toNat 8)) ::
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
        CIL.Value.aggregate (numberBytes quotient.toNat 4 ++
          numberBytes remainder.toNat 4)).mapError .arithmetic := by
  simp only [checkedIntrinsic, CIL.evalDivRem, CIL.evalDivRem.tuple, BitVec.setWidth_eq,
    List.any_cons, List.any_nil, CIL.Value.hasUnspecified, Bool.false_or, Bool.false_eq_true,
    ite_false, Bool.or_true, ite_true]
  cases CIL.divRemBits signed left right <;> rfl

/-- `ldfld Item1` on a returned `(int, int)` reads the quotient's four bytes back exactly. -/
theorem item1_of_int_tuple (first second : CIL.W32) (rest : List Value) (m : Memory) :
    instruction (.fieldAt 0 4)
      (.scalar (.aggregate (numberBytes first.toNat 4 ++
        numberBytes second.toNat 4)) :: rest) m =
      .ok (m, .scalar (.i32 first) :: rest) := by
  have taken : ((numberBytes first.toNat 4 ++ numberBytes second.toNat 4).drop 0).take 4 =
      numberBytes first.toNat 4 := by
    simp [numberBytes_length]
  have number : byteNumber (numberBytes first.toNat 4) = first.toNat := by
    rw [byteNumber_numberBytes]
    exact Nat.mod_eq_of_lt first.isLt
  simp only [instruction, List.length_append, numberBytes_length, taken, number, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rfl

#print axioms byteNumber_numberBytes_word
#print axioms mathDivRem32_eq
#print axioms item1_of_int_tuple
#print axioms item1_of_tuple
#print axioms item2_of_tuple
#print axioms divRem_fields
#print axioms divRem_fault
end CIL.Safety
