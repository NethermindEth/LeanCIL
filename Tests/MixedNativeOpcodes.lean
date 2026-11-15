import CIL.Safety.Execution
import CIL.Extraction.Scalars

/-!
# Mixed native arithmetic

Bare decoded arithmetic instructions widen admitted mixed operands. The reference step and the
checked step agree on every instruction `widenMixed` widens, in both operand orders, and on
division and overflow-checked arithmetic. Scalar admission keeps native integers distinct from
fixed-width integers and rejects mixed unsigned branches.
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

/-- The reference step and the checked step both replace `right` over `left` with `result`
    and resume at the next instruction, whatever lies beneath the pair. -/
def Agree (op : Instruction) (left right result : CIL.Value) : Prop :=
  (∀ (pc : Nat) (rest : List CIL.Value) (memory : CIL.Memory),
    CIL.step op false none pc [] (right :: left :: rest) memory =
      some (.next (pc + 1) (result :: rest) memory)) ∧
  ∀ (body : Method) (pc : Nat) (args : List Safety.Value) (frame : Frame)
    (rest : List Safety.Value) (memory : Safety.Memory),
    step body op pc args frame (.scalar right :: .scalar left :: rest) memory =
      .ok (.next (pc + 1) (.scalar result :: rest) frame memory)

/-- The reference step and the checked step of the compare-and-branch `op` both jump to its
    target exactly when `taken` holds for `right` over `left`, consuming the pair. -/
def Branches (op : Nat → Instruction) (left right : CIL.Value) (taken : Prop) [Decidable taken] :
    Prop :=
  (∀ (target pc : Nat) (rest : List CIL.Value) (memory : CIL.Memory),
    CIL.step (op target) false none pc [] (right :: left :: rest) memory =
      some (.next (if taken then target else pc + 1) rest memory)) ∧
  ∀ (body : Method) (target pc : Nat) (args : List Safety.Value) (frame : Frame)
    (rest : List Safety.Value) (memory : Safety.Memory),
    step body (op target) pc args frame (.scalar right :: .scalar left :: rest) memory =
      .ok (.next (if taken then target else pc + 1) rest frame memory)

/-- Wrapping arithmetic and bitwise operations sign-extend the int32 operand of a mixed pair in
    either stack position and compute at native width (ECMA-335 III.1.5). -/
theorem signed_arithmetic (int32 : W32) (native : W64) :
    Agree .add (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 + native)) ∧
    Agree .add (.i64 native) (.i32 int32) (.i64 (native + int32.signExtend 64)) ∧
    Agree .sub (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 - native)) ∧
    Agree .sub (.i64 native) (.i32 int32) (.i64 (native - int32.signExtend 64)) ∧
    Agree .mul (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 * native)) ∧
    Agree .mul (.i64 native) (.i32 int32) (.i64 (native * int32.signExtend 64)) ∧
    Agree .and (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 &&& native)) ∧
    Agree .and (.i64 native) (.i32 int32) (.i64 (native &&& int32.signExtend 64)) ∧
    Agree .or (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 ||| native)) ∧
    Agree .or (.i64 native) (.i32 int32) (.i64 (native ||| int32.signExtend 64)) ∧
    Agree .xor (.i32 int32) (.i64 native) (.i64 (int32.signExtend 64 ^^^ native)) ∧
    Agree .xor (.i64 native) (.i32 int32) (.i64 (native ^^^ int32.signExtend 64)) := by
  unfold Agree
  and_intros <;> intros <;> rfl
#print axioms signed_arithmetic

/-- Signed comparisons compare the sign-extended int32 operand with the native operand. -/
theorem signed_comparisons (int32 : W32) (native : W64) :
    Agree .ceq (.i32 int32) (.i64 native)
      (.i32 (if int32.signExtend 64 = native then 1 else 0)) ∧
    Agree .ceq (.i64 native) (.i32 int32)
      (.i32 (if native = int32.signExtend 64 then 1 else 0)) ∧
    Agree .clt (.i32 int32) (.i64 native)
      (.i32 (if (int32.signExtend 64).toInt < native.toInt then 1 else 0)) ∧
    Agree .clt (.i64 native) (.i32 int32)
      (.i32 (if native.toInt < (int32.signExtend 64).toInt then 1 else 0)) ∧
    Agree .cgt (.i32 int32) (.i64 native)
      (.i32 (if native.toInt < (int32.signExtend 64).toInt then 1 else 0)) ∧
    Agree .cgt (.i64 native) (.i32 int32)
      (.i32 (if (int32.signExtend 64).toInt < native.toInt then 1 else 0)) := by
  unfold Agree
  and_intros <;> intros <;> rfl
#print axioms signed_comparisons

/-- Unsigned comparisons also sign-extend the int32 operand, then compare unsigned. -/
theorem unsigned_comparisons (int32 : W32) (native : W64) :
    Agree .clt_un (.i32 int32) (.i64 native)
      (.i32 (if int32.signExtend 64 < native then 1 else 0)) ∧
    Agree .clt_un (.i64 native) (.i32 int32)
      (.i32 (if native < int32.signExtend 64 then 1 else 0)) ∧
    Agree .cgt_un (.i32 int32) (.i64 native)
      (.i32 (if native < int32.signExtend 64 then 1 else 0)) ∧
    Agree .cgt_un (.i64 native) (.i32 int32)
      (.i32 (if int32.signExtend 64 < native then 1 else 0)) := by
  unfold Agree
  and_intros <;> intros <;> rfl
#print axioms unsigned_comparisons

/-- Signed compare-and-branch instructions compare the sign-extended int32 operand. -/
theorem signed_branches (int32 : W32) (native : W64) :
    Branches .beq (.i32 int32) (.i64 native) (int32.signExtend 64 = native) ∧
    Branches .beq (.i64 native) (.i32 int32) (native = int32.signExtend 64) ∧
    Branches .blt (.i32 int32) (.i64 native) ((int32.signExtend 64).toInt < native.toInt) ∧
    Branches .blt (.i64 native) (.i32 int32) (native.toInt < (int32.signExtend 64).toInt) ∧
    Branches .ble (.i32 int32) (.i64 native) ((int32.signExtend 64).toInt ≤ native.toInt) ∧
    Branches .ble (.i64 native) (.i32 int32) (native.toInt ≤ (int32.signExtend 64).toInt) ∧
    Branches .bgt (.i32 int32) (.i64 native) (native.toInt < (int32.signExtend 64).toInt) ∧
    Branches .bgt (.i64 native) (.i32 int32) ((int32.signExtend 64).toInt < native.toInt) ∧
    Branches .bge (.i32 int32) (.i64 native) (native.toInt ≤ (int32.signExtend 64).toInt) ∧
    Branches .bge (.i64 native) (.i32 int32) ((int32.signExtend 64).toInt ≤ native.toInt) := by
  unfold Branches
  and_intros <;> intros <;> rfl
#print axioms signed_branches

/-- Overflow-checked arithmetic sign-extends the int32 operand of a mixed pair for the signed
    forms and zero-extends it for the unsigned forms; both interpreters agree in either order. -/
theorem checked_arithmetic :
    Agree .add_ovf (.i32 0xFFFFFFFF) (.i64 5) (.i64 4) ∧
    Agree .add_ovf (.i64 5) (.i32 0xFFFFFFFF) (.i64 4) ∧
    Agree .add_ovf_un (.i32 0xFFFFFFFF) (.i64 5) (.i64 0x100000004) ∧
    Agree .add_ovf_un (.i64 5) (.i32 0xFFFFFFFF) (.i64 0x100000004) ∧
    Agree .sub_ovf (.i32 0xFFFFFFFF) (.i64 5) (.i64 0xFFFFFFFFFFFFFFFA) ∧
    Agree .sub_ovf (.i64 5) (.i32 0xFFFFFFFF) (.i64 6) ∧
    Agree .sub_ovf_un (.i32 0xFFFFFFFF) (.i64 5) (.i64 0xFFFFFFFA) ∧
    Agree .sub_ovf_un (.i64 0x100000005) (.i32 0xFFFFFFFF) (.i64 6) ∧
    Agree .mul_ovf (.i32 0xFFFFFFFF) (.i64 5) (.i64 0xFFFFFFFFFFFFFFFB) ∧
    Agree .mul_ovf (.i64 5) (.i32 0xFFFFFFFF) (.i64 0xFFFFFFFFFFFFFFFB) ∧
    Agree .mul_ovf_un (.i32 0xFFFFFFFF) (.i64 5) (.i64 0x4FFFFFFFB) ∧
    Agree .mul_ovf_un (.i64 5) (.i32 0xFFFFFFFF) (.i64 0x4FFFFFFFB) := by
  unfold Agree
  and_intros <;> intros <;> rfl
#print axioms checked_arithmetic

/-- Division and remainder sign-extend the int32 operand of a mixed pair, as numerator or
    divisor, for the signed and the unsigned forms; both interpreters agree in either order. -/
theorem division :
    Agree .div (.i32 0xFFFFFFF9) (.i64 2) (.i64 0xFFFFFFFFFFFFFFFD) ∧
    Agree .div (.i64 7) (.i32 0xFFFFFFFE) (.i64 0xFFFFFFFFFFFFFFFD) ∧
    Agree .div_un (.i32 0xFFFFFFF9) (.i64 2) (.i64 0x7FFFFFFFFFFFFFFC) ∧
    Agree .div_un (.i64 0xFFFFFFFFFFFFFFFF) (.i32 0xFFFFFFFE) (.i64 1) ∧
    Agree .rem (.i32 0xFFFFFFF9) (.i64 2) (.i64 0xFFFFFFFFFFFFFFFF) ∧
    Agree .rem (.i64 7) (.i32 0xFFFFFFFE) (.i64 1) ∧
    Agree .rem_un (.i32 0xFFFFFFF9) (.i64 2) (.i64 1) ∧
    Agree .rem_un (.i64 0xFFFFFFFFFFFFFFFF) (.i32 0xFFFFFFFE) (.i64 1) := by
  unfold Agree
  and_intros <;> intros <;> rfl
#print axioms division

/-- Outside the eleven listed instructions and the five compare-and-branch forms, `widenMixed`
    leaves every stack as it is. -/
theorem widened_instructions (op : Instruction) (stack : List CIL.Value) :
    (op ∈ [.add, .sub, .mul, .and, .or, .xor, .ceq, .clt, .cgt, .clt_un, .cgt_un] ∨
      ∃ target, op ∈ [.beq target, .blt target, .ble target, .bgt target, .bge target]) ∨
    widenMixed op stack = stack := by
  cases op <;> simp [widenMixed, nativePureBinary]
#print axioms widened_instructions

/-- An instruction `widenMixed` widens leaves the stack as it is unless a 64-bit operand lies
    on top of a 32-bit one or the reverse, so equal kinds, and a float, reference or vector on
    top, are unchanged whatever lies beneath. -/
theorem widened_unchanged_unless_mixed (op : Instruction) (widened : nativePureBinary op = true)
    (top below : CIL.Value) (rest : List CIL.Value)
    (nativeOverInt32 : ∀ native int32, ¬(top = .i64 native ∧ below = .i32 int32))
    (int32OverNative : ∀ int32 native, ¬(top = .i32 int32 ∧ below = .i64 native)) :
    widenMixed op (top :: below :: rest) = top :: below :: rest := by
  unfold widenMixed
  rw [widened]
  split
  · next _ _ _ heq =>
    cases heq
    exact absurd ⟨rfl, rfl⟩ (nativeOverInt32 _ _)
  · next _ _ _ heq =>
    cases heq
    exact absurd ⟨rfl, rfl⟩ (int32OverNative _ _)
  · rfl
#print axioms widened_unchanged_unless_mixed

/-- Unsigned branches refuse a mixed pair in both interpreters and both operand orders. -/
theorem unsigned_branches_refused (int32 : W32) (native : W64) :
    ([Instruction.bne_un 9, .blt_un 9, .bgt_un 9, .ble_un 9, .bge_un 9].all fun op =>
      (CIL.step op false none 0 [] [.i32 int32, .i64 native] (fun _ => none)).isNone &&
      (CIL.step op false none 0 [] [.i64 native, .i32 int32] (fun _ => none)).isNone &&
      !(step body op 0 [] frame [.scalar (.i32 int32), .scalar (.i64 native)] Memory.empty).isOk &&
      !(step body op 0 [] frame [.scalar (.i64 native), .scalar (.i32 int32)] Memory.empty).isOk) =
      true := by
  rfl
#print axioms unsigned_branches_refused

end Tests.MixedNativeOpcodes
