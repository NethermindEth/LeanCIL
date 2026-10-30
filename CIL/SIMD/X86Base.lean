import CIL.IntegerArithmetic

/-!
# X86Base.X64.DivRem

The 128-by-64-bit unsigned division intrinsic, and proofs that it either returns the exact
quotient and remainder or faults; it never returns a truncated result.

128-by-64 DIV faults (#DE) unless upper < divisor: DivideByZeroException for 0, else
OverflowException.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/X86Base.cs
https://learn.microsoft.com/dotnet/api/system.runtime.intrinsics.x86.x86base.x64.divrem?view=net-10.0
-/

namespace CIL.X86

/-- The 128-bit dividend `upper:lower`. -/
def dividend (lower upper : W64) : Nat := upper.toNat * 2 ^ 64 + lower.toNat

/-- Quotient and remainder of `upper:lower` by `divisor`, faulting unless `upper < divisor`. -/
def divRem64 (lower upper divisor : W64) : Except ArithmeticFault (W64 × W64) :=
  if divisor = 0 then .error .divideByZero
  else if divisor.toNat ≤ upper.toNat then .error .overflow
  else .ok (BitVec.ofNat 64 (dividend lower upper / divisor.toNat),
    BitVec.ofNat 64 (dividend lower upper % divisor.toNat))

/-- Little-endian bytes of one 64-bit tuple field. -/
def wordBytes (word : W64) : List (BitVec 8) := littleEndianBytes 8 word.toNat

/-- `ValueTuple<ulong, ulong>` stores Item1 at offset 0 and Item2 at offset 8. -/
def divRemValue : List Value → Except ArithmeticFault Value
  | [.i64 lower, .i64 upper, .i64 divisor] => do
    let (quotient, remainder) ← divRem64 lower upper divisor
    return .aggregate (wordBytes quotient ++ wordBytes remainder)
  | _ => .error .invalidOperands

theorem dividend_lt {lower upper divisor : W64} (fits : upper.toNat < divisor.toNat) :
    dividend lower upper < divisor.toNat * 2 ^ 64 := by
  unfold dividend
  have := lower.isLt
  calc upper.toNat * 2 ^ 64 + lower.toNat < (upper.toNat + 1) * 2 ^ 64 := by omega
    _ ≤ divisor.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ fits

theorem divRem64_ok {lower upper divisor : W64} (fits : upper.toNat < divisor.toNat) :
    divRem64 lower upper divisor = .ok (BitVec.ofNat 64 (dividend lower upper / divisor.toNat),
      BitVec.ofNat 64 (dividend lower upper % divisor.toNat)) := by
  have nonzero : divisor ≠ 0 := by
    intro zero
    simp [zero] at fits
  unfold divRem64
  split
  · contradiction
  · split
    · omega
    · rfl

/-- Under the precondition both fields are exact: no 64-bit truncation occurs. -/
theorem divRem64_fields {lower upper divisor : W64} (fits : upper.toNat < divisor.toNat) :
    (BitVec.ofNat 64 (dividend lower upper / divisor.toNat)).toNat =
        (upper.toNat * 2 ^ 64 + lower.toNat) / divisor.toNat ∧
      (BitVec.ofNat 64 (dividend lower upper % divisor.toNat)).toNat =
        (upper.toNat * 2 ^ 64 + lower.toNat) % divisor.toNat := by
  have positive : 0 < divisor.toNat := by omega
  have quotient : dividend lower upper / divisor.toNat < 2 ^ 64 :=
    (Nat.div_lt_iff_lt_mul positive).mpr (by rw [Nat.mul_comm]; exact dividend_lt fits)
  have remainder : dividend lower upper % divisor.toNat < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ positive) divisor.isLt
  exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt quotient]; rfl,
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt remainder]; rfl⟩

/-- Every input violating the precondition is a fault, never a wrapped result. -/
theorem divRem64_fault {lower upper divisor : W64} (overflows : divisor.toNat ≤ upper.toNat) :
    divRem64 lower upper divisor = .error (if divisor = 0 then .divideByZero else .overflow) := by
  unfold divRem64
  split <;> (try split) <;> first | rfl | omega

end CIL.X86
