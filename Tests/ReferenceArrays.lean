import CIL.Safety.ObjectSteps

/-! `newarr` of a class allocates an object of the array type `E[]` on the heap budget, with one
    null reference slot per element. Its length is decoded like a primitive array's, and an
    allocation the budget cannot pay for is the model's resource fault, never a CLR exception. -/

namespace Tests.ReferenceArrays

open CIL CIL.Safety

private def node : CIL.Extraction.TypeExpr := .object "Examples" "Examples.Node"

/-- Caller memory granting 32 bytes of object budget and no other storage. -/
private def budgeted : CIL.Safety.Memory := { Memory.empty with heapBudget := 32 }

private def creator : CIL.Method :=
  { returnsValue := true, locals := [],
    code := [.const32 3, .newReferenceArray node, .ret none] }

/-- Three references take the next identity, three slots of budget, and every slot is null. -/
theorem allocation_charges_budget :
    (newReferenceArray budgeted node (.i32 3)).map (fun result =>
      (result.1, result.2.heapBudget, result.2.allocations 0 |>.map (·.kind),
        result.2.slots 0 16)) =
      .ok (⟨0, 0⟩, 8, some (.object (referenceArrayType node)), .null) := rfl
#print axioms allocation_charges_budget

/-- The array is returned as an object reference. -/
theorem allocation_returns_array :
    (invoke [creator] 8 0 [] budgeted).map Prod.snd = .ok [.object (.address ⟨0, 0⟩)] := rfl
#print axioms allocation_returns_array

/-- A negative length throws `OverflowException`; an unaffordable one is a model fault. -/
theorem allocation_faults :
    newReferenceArray budgeted node (.i32 (-1)) = .error (.thrown "System.OverflowException") ∧
    newReferenceArray budgeted node (.i64 5) = .error (.allocationFailure 40 32) ∧
    newReferenceArray budgeted node (.i64 0x80000000) =
      .error (.unsupported "Array length outside supported extent") := ⟨rfl, rfl, rfl⟩
#print axioms allocation_faults

/-- An empty array costs nothing and still has its own identity. -/
theorem empty_allocation :
    (newReferenceArray budgeted node (.i32 0)).map (fun result =>
      (result.1, result.2.heapBudget)) = .ok (⟨0, 0⟩, 32) := rfl
#print axioms empty_allocation

end Tests.ReferenceArrays
