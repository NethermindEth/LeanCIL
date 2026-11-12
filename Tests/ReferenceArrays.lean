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

private def shape : CIL.Extraction.TypeExpr := .object "Examples" "Examples.Shape"
private def circle : CIL.Extraction.TypeExpr := .object "Examples" "Examples.Circle"
private def square : CIL.Extraction.TypeExpr := .object "Examples" "Examples.Square"

/-- Caller memory holding one `Square`, a `Shape`, at identity 0, with 32 bytes of budget. -/
private def holdingSquare : CIL.Safety.Memory := objectMemory budgeted ⟨square, [shape]⟩ 8

/-- The `Square` the caller holds. -/
private def squareObject : CIL.Safety.Value := .object (.address ⟨0, 0⟩)

/-- Runs straight-line `code` returning one value, with the given arguments. -/
private def runs (code : List CIL.Instruction) (arguments : List CIL.Safety.Value)
    (memory : CIL.Safety.Memory) :
    Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value) :=
  invoke [{ returnsValue := true, locals := [], code := code }] 16 0 arguments memory

/-- `ldlen` reads the length back from the allocation's size. -/
theorem length_of_fresh :
    (runs [.const32 3, .newReferenceArray node, .memory .referenceArrayLength, .ret none] []
      budgeted).map Prod.snd = .ok [.scalar (.i64 3)] := rfl
#print axioms length_of_fresh

/-- `ldlen`, `ldelem.ref` and `stelem.ref` of a null array throw `NullReferenceException`. -/
theorem null_array_throws :
    runs [.memory .nullObject, .memory .referenceArrayLength, .ret none] [] budgeted =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ ∧
    runs [.memory .nullObject, .const32 0, .memory .referenceArrayLoad, .ret none] [] budgeted =
      .error ⟨0, 2, .thrown "System.NullReferenceException"⟩ ∧
    runs [.memory .nullObject, .const32 0, .memory .nullObject, .memory .referenceArrayStore,
      .const32 0, .ret none] [] budgeted =
      .error ⟨0, 3, .thrown "System.NullReferenceException"⟩ := ⟨rfl, rfl, rfl⟩
#print axioms null_array_throws

/-- An index at the length, or a negative one read unsigned, throws `IndexOutOfRangeException`
    before a stored value's class is checked. -/
theorem index_out_of_range :
    runs [.const32 2, .newReferenceArray node, .const32 2, .memory .referenceArrayLoad,
      .ret none] [] budgeted = .error ⟨0, 3, .thrown "System.IndexOutOfRangeException"⟩ ∧
    runs [.const32 2, .newReferenceArray circle, .const32 (-1), .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .ret none] [squareObject] holdingSquare =
      .error ⟨0, 4, .thrown "System.IndexOutOfRangeException"⟩ := ⟨rfl, rfl⟩
#print axioms index_out_of_range

/-- A fresh element is null, and null is storable into any array of class references. -/
theorem null_elements :
    (runs [.const32 1, .newReferenceArray node, .const32 0, .memory .referenceArrayLoad,
      .ret none] [] budgeted).map Prod.snd = .ok [.object .null] ∧
    (runs [.const32 1, .newReferenceArray circle, .dup, .const32 0, .memory .nullObject,
      .memory .referenceArrayStore, .const32 0, .memory .referenceArrayLoad, .ret none] []
      budgeted).map Prod.snd = .ok [.object .null] := ⟨rfl, rfl⟩
#print axioms null_elements

/-- A `Square` is storable into an array of `Shape` and loads back as itself. -/
theorem covariant_store :
    (runs [.const32 1, .newReferenceArray shape, .dup, .const32 0, .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .memory .referenceArrayLoad, .ret none]
      [squareObject] holdingSquare).map Prod.snd = .ok [squareObject] := rfl
#print axioms covariant_store

/-- Storing a `Square` into an array of `Circle` throws `ArrayTypeMismatchException`, and the
    element keeps what it held. -/
theorem mismatched_store :
    runs [.const32 1, .newReferenceArray circle, .const32 0, .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .ret none] [squareObject] holdingSquare =
      .error ⟨0, 4, .thrown "System.ArrayTypeMismatchException"⟩ := rfl
#print axioms mismatched_store

/-- Storing an array, whose class is no admitted class, is outside the model rather than an
    exception the CLR might not throw. -/
theorem array_store_unsupported :
    runs [.const32 1, .newReferenceArray shape, .dup, .const32 0, .const32 1,
      .newReferenceArray shape, .memory .referenceArrayStore, .const32 0, .ret none] []
      budgeted = .error ⟨0, 6, .unsupported "Array store outside the admitted classes"⟩ := rfl
#print axioms array_store_unsupported

/-- `System.String`, a class outside the model: arrays of it hold opaque references. -/
private def text : CIL.Extraction.TypeExpr := .object Extraction.runtimeScope "System.String"

/-- Caller memory holding one string at identity 0 and one `Square` at identity 1. -/
private def holdingText : CIL.Safety.Memory :=
  objectMemory (objectMemory budgeted ⟨text, []⟩ 0) ⟨square, [shape]⟩ 8

/-- A string stores into an array of strings and loads back as itself: the element class is
    the string's own class. -/
theorem opaque_store :
    (runs [.const32 1, .newReferenceArray text, .dup, .const32 0, .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .memory .referenceArrayLoad, .ret none]
      [.object (.address ⟨0, 0⟩)] holdingText).map Prod.snd =
      .ok [.object (.address ⟨0, 0⟩)] := rfl
#print axioms opaque_store

/-- A `Square` stored into an array of strings throws `ArrayTypeMismatchException`, and a string
    stored into an array of `Shape` does too: neither class derives from the other. -/
theorem opaque_mismatch :
    runs [.const32 1, .newReferenceArray text, .const32 0, .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .ret none] [.object (.address ⟨1, 0⟩)]
      holdingText = .error ⟨0, 4, .thrown "System.ArrayTypeMismatchException"⟩ ∧
    runs [.const32 1, .newReferenceArray shape, .const32 0, .arg 0 none,
      .memory .referenceArrayStore, .const32 0, .ret none] [.object (.address ⟨0, 0⟩)]
      holdingText = .error ⟨0, 4, .thrown "System.ArrayTypeMismatchException"⟩ := ⟨rfl, rfl⟩
#print axioms opaque_mismatch

end Tests.ReferenceArrays
