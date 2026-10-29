import CIL.Safety.Execution
import CIL.Extraction.Scalars

/-! # Checked pointer subtraction and allocation-relative ordering -/

namespace Tests.PointerOperations
open CIL.Safety

/-- Pointer storage admits characters and integer enums, without admitting other pointee shapes. -/
theorem pointer_storage_kinds :
    let runtime := CIL.Extraction.runtimeScope
    let storage := CIL.Extraction.typeStorage []
    storage (.pointer (.atom runtime "System.Char")) = some .reference ∧
    storage (.pointer (.enum "Example" (.atom runtime "System.Int16"))) = some .reference ∧
    storage (.pointer (.enum "Example" (.atom runtime "System.UInt64"))) = some .reference ∧
    storage (.pointer (.enum "Example" (.atom runtime "System.Boolean"))) = none ∧
    storage (.pointer (.atom "forged" "System.Char")) = none ∧
    storage (.pointer (.atom runtime "System.Double")) = none ∧
    storage (.pointer (.byref (.atom runtime "System.Int32"))) = none ∧
    storage (.pointer (.pointer (.atom runtime "System.Int32"))) = none := by decide +kernel
#print axioms pointer_storage_kinds

private def memory : Memory := {
  allocations := fun identity => if identity < 2 then
    some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 2 }

private def subtract : CIL.Method := {
  code := [.arg 0, .arg 1, .sub, .ret], locals := [], returnsValue := true }

/-- Pointer subtraction checks positions without requiring readable storage. -/
theorem subtract_bytes :
    invoke [subtract] 8 0 [.reference (.address ⟨0, 5⟩), .scalar (.i32 3)] memory =
      .ok (memory, [.reference (.address ⟨0, 2⟩)]) := rfl
#print axioms subtract_bytes

/-- A negative int32 byte displacement moves the reference forward. -/
theorem subtract_negative_bytes :
    invoke [subtract] 8 0 [.reference (.address ⟨0, 2⟩), .scalar (.i32 4294967293)] memory =
      .ok (memory, [.reference (.address ⟨0, 5⟩)]) := rfl
#print axioms subtract_negative_bytes

/-- Native offsets have the same byte-unit semantics. -/
theorem subtract_native_bytes :
    invoke [subtract] 8 0 [.reference (.address ⟨0, 5⟩), .scalar (.i64 3)] memory =
      .ok (memory, [.reference (.address ⟨0, 2⟩)]) := rfl
#print axioms subtract_native_bytes

/-- Subtraction cannot discard a reference's readonly restriction. -/
theorem subtract_preserves_readonly :
    invoke [subtract] 8 0 [.readOnlyReference (.address ⟨0, 5⟩), .scalar (.i32 3)] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 2⟩)]) := rfl
#print axioms subtract_preserves_readonly

/-- Two same-allocation pointers produce a native byte difference. -/
theorem positive_difference :
    invoke [subtract] 8 0 [.reference (.address ⟨0, 5⟩), .reference (.address ⟨0, 2⟩)] memory =
      .ok (memory, [.scalar (.i64 3)]) := rfl
#print axioms positive_difference

/-- Negative differences preserve their two's-complement native representation. -/
theorem negative_difference :
    referenceDifference memory (.address ⟨0, 2⟩) (.address ⟨0, 5⟩) =
      .ok 18446744073709551613 := rfl
#print axioms negative_difference

/-- Declared end positions can participate in a difference without becoming readable. -/
theorem end_difference :
    referenceDifference memory (.address ⟨0, 8⟩) (.address ⟨0, 0⟩) = .ok 8 := rfl
#print axioms end_difference

/-- Distinct allocation identities cannot justify an address difference. -/
theorem cross_allocation_rejected :
    referenceDifference memory (.address ⟨0, 2⟩) (.address ⟨1, 2⟩) =
      .error (.unsupported "Cross-allocation pointer arithmetic") := rfl
#print axioms cross_allocation_rejected

/-- Null does not have an allocation-relative arithmetic position. -/
theorem null_difference_rejected :
    referenceDifference memory .null .null = .error (.memory .nullDereference .null 0) := rfl
#print axioms null_difference_rejected

/-- Wrapping below the allocation cannot fabricate a valid position. -/
theorem underflow_rejected :
    referenceSubtract memory (.address ⟨0, 0⟩) (.i32 1) =
      .error (.memory .invalidReference (.address ⟨0, 0⟩) 0) := rfl
#print axioms underflow_rejected

/-- Even identical invalid pointer representations must be rejected. -/
theorem invalid_difference_rejected :
    referenceDifference memory (.address ⟨0, 9⟩) (.address ⟨0, 9⟩) =
      .error (.memory .invalidReference (.address ⟨0, 9⟩) 0) := rfl
#print axioms invalid_difference_rejected

/-- Unsigned ordering of two live same-allocation pointers follows their byte positions. -/
theorem interior_before_end :
    referenceLess memory (.address ⟨0, 7⟩) (.address ⟨0, 8⟩) = .ok true := rfl
#print axioms interior_before_end

/-- Pointer subtraction cannot be certified as scalar addition. -/
theorem changed_subtraction_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 89, .none⟩ [.native, .reference] .add = false :=
  by decide +kernel
#print axioms changed_subtraction_rejected

/-- A difference must retain the exact raw subtraction operation. -/
theorem difference_encoding :
    CIL.Extraction.scalarOpMatches ⟨0, 89, .none⟩ [.reference, .reference] .sub = true :=
  by decide +kernel
#print axioms difference_encoding

private def comparison (operation : CIL.Op) : CIL.Method := {
  code := [.arg 0, .arg 1, operation, .ret], locals := [], returnsValue := true }

private def branch (operation : CIL.Op) : CIL.Method := {
  code := [.arg 0, .arg 1, operation, .const32 0, .ret, .const32 1, .ret]
  locals := [], returnsValue := true }

/-- Both unsigned comparisons agree with offset ordering and preserve memory. -/
theorem unsigned_comparisons :
    [CIL.Op.ltu, .gtu].map (fun operation =>
      (invoke [comparison operation] 8 0
        [.reference (.address ⟨0, 2⟩), .readOnlyReference (.address ⟨0, 5⟩)] memory).map
        Prod.snd) = [.ok [.scalar (.i32 1)], .ok [.scalar (.i32 0)]] := rfl
#print axioms unsigned_comparisons

/-- All four unsigned branches select the proper successor for the same pair of pointers. -/
theorem unsigned_branches :
    [CIL.Op.bltu 5, .bleu 5, .bgtu 5, .bgeu 5].map (fun operation =>
      (invoke [branch operation] 10 0
        [.reference (.address ⟨0, 2⟩), .reference (.address ⟨0, 5⟩)] memory).map Prod.snd) =
      [.ok [.scalar (.i32 1)], .ok [.scalar (.i32 1)],
        .ok [.scalar (.i32 0)], .ok [.scalar (.i32 0)]] := rfl
#print axioms unsigned_branches

/-- The ordering operations reject cross-allocation comparisons even for equal offsets. -/
theorem cross_allocation_order_rejected :
    referenceLess memory (.address ⟨0, 2⟩) (.address ⟨1, 2⟩) =
      .error (.unsupported "Cross-allocation pointer arithmetic") := rfl
#print axioms cross_allocation_order_rejected

/-- Equal pointers are not strictly ordered. -/
theorem identical_position_not_less :
    referenceLess memory (.address ⟨0, 2⟩) (.address ⟨0, 2⟩) = .ok false := rfl
#print axioms identical_position_not_less

/-- Signed ordering cannot be certified from managed-reference operand kinds. -/
theorem signed_order_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 65028, .none⟩ [.reference, .reference] .lt = false :=
  by decide +kernel
#print axioms signed_order_rejected
/-- Expired storage cannot participate in a pointer difference. -/
theorem expired_difference_rejected :
    referenceDifference { memory with
      allocations := fun _ => some ⟨.callerStack, ⟨8, 1, []⟩, false, [8]⟩ }
      (.address ⟨0, 2⟩) (.address ⟨0, 5⟩) =
      .error (.memory .expiredLifetime (.address ⟨0, 2⟩) 0) := rfl
#print axioms expired_difference_rejected

/-- Integer-minus-pointer is not a pointer operation. -/
theorem reversed_operands_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 89, .none⟩ [.reference, .native] .sub = false :=
  by decide +kernel
#print axioms reversed_operands_rejected

/-- The difference is a native integer, never a reference that can be dereferenced. -/
theorem difference_kind (raw : CIL.Extraction.RawMethod) :
    CIL.Extraction.scalarTransfer raw ⟨0, 89, .none⟩ [.reference, .reference] =
      some [.native] := rfl
#print axioms difference_kind

/-- Subtracting a native displacement retains the raw reference kind. -/
theorem subtraction_kind (raw : CIL.Extraction.RawMethod) :
    CIL.Extraction.scalarTransfer raw ⟨0, 89, .none⟩ [.native, .reference] =
      some [.reference] := rfl
#print axioms subtraction_kind

/-- Non-strict branches include equality, while strict branches exclude it. -/
theorem equal_position_branches :
    [CIL.Op.bltu 5, .bleu 5, .bgtu 5, .bgeu 5].map (fun operation =>
      (invoke [branch operation] 10 0
        [.reference (.address ⟨0, 2⟩), .reference (.address ⟨0, 2⟩)] memory).map Prod.snd) =
      [.ok [.scalar (.i32 0)], .ok [.scalar (.i32 1)],
        .ok [.scalar (.i32 0)], .ok [.scalar (.i32 1)]] := rfl
#print axioms equal_position_branches
end Tests.PointerOperations
