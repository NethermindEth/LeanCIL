import CIL.Safety.Execution
import CIL.Extraction.Scalars

/-!
# Mixed native arithmetic

Bare decoded arithmetic instructions widen admitted mixed operands. Scalar admission keeps
native integers distinct from fixed-width integers and rejects mixed unsigned branches.
-/

namespace Tests.MixedNativeOpcodes

open CIL CIL.Safety CIL.Extraction

/-- A scalar body with no frame storage. -/
private def body : Method := { returnsValue := true, locals := [], code := [] }

/-- The empty activation used by scalar steps. -/
private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- Mixed addition sign-extends the int32 operand in either stack position. -/
theorem add_mixed :
    step body .add 0 [] frame [.scalar (.i64 5), .scalar (.i32 0xFFFFFFFF)] Memory.empty =
      .ok (.next 1 [.scalar (.i64 4)] frame Memory.empty) ∧
    step body .add 0 [] frame [.scalar (.i32 0xFFFFFFFF), .scalar (.i64 5)] Memory.empty =
      .ok (.next 1 [.scalar (.i64 4)] frame Memory.empty) := by
  constructor <;> rfl
#print axioms add_mixed

/-- Unsigned checked multiplication zero-extends the int32 operand in either position. -/
theorem multiply_unsigned_mixed :
    step body .mul_ovf_un 0 [] frame [.scalar (.i32 0x80000000), .scalar (.i64 2)]
        Memory.empty = .ok (.next 1 [.scalar (.i64 0x100000000)] frame Memory.empty) ∧
    step body .mul_ovf_un 0 [] frame [.scalar (.i64 2), .scalar (.i32 0x80000000)]
        Memory.empty = .ok (.next 1 [.scalar (.i64 0x100000000)] frame Memory.empty) := by
  constructor <;> rfl
#print axioms multiply_unsigned_mixed

/-- Unsigned division sign-extends the mixed int32 numerator before dividing. -/
theorem divide_unsigned_mixed :
    step body .div_un 0 [] frame [.scalar (.i64 2), .scalar (.i32 0xFFFFFFFF)]
        Memory.empty = .ok (.next 1 [.scalar (.i64 0x7FFFFFFFFFFFFFFF)] frame Memory.empty) := by
  rfl
#print axioms divide_unsigned_mixed

/-- A mixed unsigned comparison branch remains unsupported. -/
theorem unsigned_branch_refused :
    step body (.blt_un 4) 0 [] frame [.scalar (.i64 2), .scalar (.i32 1)] Memory.empty =
      .error .invalidState := by
  rfl
#print axioms unsigned_branch_refused

/-- Mixed signed division retains both arithmetic fault conditions. -/
theorem divide_mixed_faults :
    step body .div 0 [] frame [.scalar (.i32 0), .scalar (.i64 7)] Memory.empty =
      .error (.arithmetic .divideByZero) ∧
    step body .div 0 [] frame [.scalar (.i32 0xFFFFFFFF), .scalar (.i64 0x8000000000000000)]
        Memory.empty = .error (.arithmetic .overflow) := by
  constructor <;> rfl
#print axioms divide_mixed_faults

/-- Mixed unsigned remainder sign-extends the int32 numerator. -/
theorem remainder_unsigned_mixed :
    step body .rem_un 0 [] frame [.scalar (.i64 2), .scalar (.i32 0xFFFFFFFF)]
        Memory.empty = .ok (.next 1 [.scalar (.i64 1)] frame Memory.empty) := by
  rfl
#print axioms remainder_unsigned_mixed

/-- Mixed checked addition preserves signed and unsigned overflow faults. -/
theorem addition_mixed_overflow :
    step body .add_ovf 0 [] frame [.scalar (.i32 1), .scalar (.i64 0x7FFFFFFFFFFFFFFF)]
        Memory.empty = .error (.arithmetic .overflow) ∧
    step body .add_ovf_un 0 [] frame [.scalar (.i64 0xFFFFFFFFFFFFFFFF), .scalar (.i32 1)]
        Memory.empty = .error (.arithmetic .overflow) := by
  constructor <;> rfl
#print axioms addition_mixed_overflow

/-- Bare addition admits native/int32 pairs and rejects fixed-width int64/int32 pairs. -/
theorem addition_admission :
    scalarOpMatches ⟨0, 88, .none⟩ [.word32, .native] .add = true ∧
    scalarOpMatches ⟨0, 88, .none⟩ [.native, .word32] .add = true ∧
    scalarOpMatches ⟨0, 88, .none⟩ [.word32, .word64] .add = false ∧
    scalarOpMatches ⟨0, 88, .none⟩ [.word64, .word32] .add = false := by
  decide
#print axioms addition_admission

end Tests.MixedNativeOpcodes
