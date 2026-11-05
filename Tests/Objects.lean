import CIL.Safety.ObjectSteps

/-! Object references form only at offset 0 of a live object allocation, compare by identity
    and test presence only against null; every other shape is rejected. -/

namespace Tests.Objects

open CIL CIL.Safety

private def account : RuntimeType := ⟨.object "Examples" "Examples.Account"⟩

/-- Allocation 0 holds an object, 1 is an expired object and 2 is a caller stack buffer. -/
private def memory : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 => some ⟨.object account, ⟨0, 1, []⟩, true, []⟩
      | 1 => some ⟨.object account, ⟨0, 1, []⟩, false, []⟩
      | 2 => some ⟨.callerStack, ⟨8, 1, []⟩, true, []⟩
      | _ => none
    cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 3 }
private def frame : Frame := { activation := 0, locals := [], owned := [] }
private def body : CIL.Method := { returnsValue := true, locals := [], code := [] }
private def live : ManagedReference := .address ⟨0, 0⟩

/-- A live object allocation at offset 0 forms as itself. -/
theorem live_object_forms : formObject memory live = .ok (.object live) := rfl
#print axioms live_object_forms

/-- An interior offset of an object allocation is not an object reference. -/
theorem interior_offset_rejected :
    formObject memory (.address ⟨0, 1⟩) = .error .invalidState := rfl
#print axioms interior_offset_rejected

/-- A byte buffer cannot be reinterpreted as an object. -/
theorem buffer_not_object :
    formObject memory (.address ⟨2, 0⟩) = .error .invalidState := rfl
#print axioms buffer_not_object

/-- An expired object faults with the allocation's lifetime rule. -/
theorem expired_object_faults :
    formObject memory (.address ⟨1, 0⟩) =
      .error (.memory .expiredLifetime (.address ⟨1, 0⟩) 0) := rfl
#print axioms expired_object_faults

/-- `ceq` of an object with itself is 1 and with null is 0. -/
theorem identity_comparisons :
    CIL.Safety.step body .eq 0 [] frame [.object live, .object live] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) ∧
    CIL.Safety.step body .eq 0 [] frame [.object .null, .object live] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := ⟨rfl, rfl⟩
#print axioms identity_comparisons

/-- `cgt.un` on two objects is defined only against null. -/
theorem ordering_rejected :
    CIL.Safety.step body .gtu 0 [] frame [.object live, .object live] memory =
      .error .invalidState := rfl
#print axioms ordering_rejected

/-- Object and byref nulls are distinct: neither compares with the other. -/
theorem byref_null_not_object :
    CIL.Safety.step body .eq 0 [] frame [.object .null, .reference .null] memory =
      .error .invalidState ∧
    storeLocal memory (.object none) (.reference .null) = .error .invalidState := ⟨rfl, rfl⟩
#print axioms byref_null_not_object

/-- An object home never exposes an address. -/
theorem object_local_has_no_address :
    localAddress memory (.object (some live)) =
      .error (.unsupported "Address of object reference local") := rfl
#print axioms object_local_has_no_address

end Tests.Objects
