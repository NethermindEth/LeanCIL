import CIL.Safety.ObjectSteps
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

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
    code := [.ldc_i4 3, .newarr node, .ret] }

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
    newReferenceArray budgeted node (.i32 (-1)) = .error (.thrown .overflow) ∧
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
    (runs [.ldc_i4 3, .newarr node, .ldlen, .ret] []
      budgeted).map Prod.snd = .ok [.scalar (.i64 3)] := rfl
#print axioms length_of_fresh

/-- `ldlen`, `ldelem.ref` and `stelem.ref` of a null array throw `NullReferenceException`. -/
theorem null_array_throws :
    runs [.ldnull, .ldlen, .ret] [] budgeted =
      .error ⟨0, 1, .thrown .nullReference⟩ ∧
    runs [.ldnull, .ldc_i4 0, .ldelem_ref, .ret] [] budgeted =
      .error ⟨0, 2, .thrown .nullReference⟩ ∧
    runs [.ldnull, .ldc_i4 0, .ldnull, .stelem_ref,
      .ldc_i4 0, .ret] [] budgeted =
      .error ⟨0, 3, .thrown .nullReference⟩ := ⟨rfl, rfl, rfl⟩
#print axioms null_array_throws

/-- An index at the length, or a negative one read unsigned, throws `IndexOutOfRangeException`
    before a stored value's class is checked. -/
theorem index_out_of_range :
    runs [.ldc_i4 2, .newarr node, .ldc_i4 2, .ldelem_ref,
      .ret] [] budgeted = .error ⟨0, 3, .thrown .indexOutOfRange⟩ ∧
    runs [.ldc_i4 2, .newarr circle, .ldc_i4 (-1), .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ret] [squareObject] holdingSquare =
      .error ⟨0, 4, .thrown .indexOutOfRange⟩ := ⟨rfl, rfl⟩
#print axioms index_out_of_range

/-- A fresh element is null, and null is storable into any array of class references. -/
theorem null_elements :
    (runs [.ldc_i4 1, .newarr node, .ldc_i4 0, .ldelem_ref,
      .ret] [] budgeted).map Prod.snd = .ok [.object .null] ∧
    (runs [.ldc_i4 1, .newarr circle, .dup, .ldc_i4 0, .ldnull,
      .stelem_ref, .ldc_i4 0, .ldelem_ref, .ret] []
      budgeted).map Prod.snd = .ok [.object .null] := ⟨rfl, rfl⟩
#print axioms null_elements

/-- A `Square` is storable into an array of `Shape` and loads back as itself. -/
theorem covariant_store :
    (runs [.ldc_i4 1, .newarr shape, .dup, .ldc_i4 0, .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ldelem_ref, .ret]
      [squareObject] holdingSquare).map Prod.snd = .ok [squareObject] := rfl
#print axioms covariant_store

/-- Storing a `Square` into an array of `Circle` throws `ArrayTypeMismatchException`, and the
    element keeps what it held. -/
theorem mismatched_store :
    runs [.ldc_i4 1, .newarr circle, .ldc_i4 0, .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ret] [squareObject] holdingSquare =
      .error ⟨0, 4, .thrown .arrayTypeMismatch⟩ := rfl
#print axioms mismatched_store

/-- Storing an array, whose class is no admitted class, is outside the model rather than an
    exception the CLR might not throw. -/
theorem array_store_unsupported :
    runs [.ldc_i4 1, .newarr shape, .dup, .ldc_i4 0, .ldc_i4 1,
      .newarr shape, .stelem_ref, .ldc_i4 0, .ret] []
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
    (runs [.ldc_i4 1, .newarr text, .dup, .ldc_i4 0, .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ldelem_ref, .ret]
      [.object (.address ⟨0, 0⟩)] holdingText).map Prod.snd =
      .ok [.object (.address ⟨0, 0⟩)] := rfl
#print axioms opaque_store

/-- A `Square` stored into an array of strings throws `ArrayTypeMismatchException`, and a string
    stored into an array of `Shape` does too: neither class derives from the other. -/
theorem opaque_mismatch :
    runs [.ldc_i4 1, .newarr text, .ldc_i4 0, .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ret] [.object (.address ⟨1, 0⟩)]
      holdingText = .error ⟨0, 4, .thrown .arrayTypeMismatch⟩ ∧
    runs [.ldc_i4 1, .newarr shape, .ldc_i4 0, .ldarg 0,
      .stelem_ref, .ldc_i4 0, .ret] [.object (.address ⟨0, 0⟩)]
      holdingText = .error ⟨0, 4, .thrown .arrayTypeMismatch⟩ := ⟨rfl, rfl⟩
#print axioms opaque_mismatch

/-- `System.Object`, whose arrays may hold interface and boxed value instances. -/
private def rootObject : CIL.Extraction.TypeExpr :=
  .object Extraction.runtimeScope ElementShape.rootObjectName

/-- An array of `System.Object` has no shape, so `newarr` of it is outside the model, before
    any allocation; a class of the same name in another assembly is still a class element. -/
theorem root_object_refused :
    runs [.ldc_i4 1, .newarr rootObject, .ret] [] budgeted =
      .error ⟨0, 1, .unsupported ElementShape.rootObjectElement⟩ ∧
    (runs [.ldc_i4 1, .newarr (.object "Examples" "Examples.Object"), .ret] []
      budgeted).map Prod.snd = .ok [.object (.address ⟨0, 0⟩)] := ⟨rfl, rfl⟩
#print axioms root_object_refused

/-- `newarr` of two `Node` references. -/
@[cil_code] def allocating : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldc_i4 2, .newarr node, .ret] }

/-- The steps resolve the element shape of a class and allocate through
    `newReferenceArray`, so its budget fact discharges the allocation and the fresh array
    forms where it is returned. -/
theorem stepped_allocation (memory : CIL.Safety.Memory) (formed : memory.WellFormed)
    (budget : objectFieldSlot * 2 ≤ memory.heapBudget) :
    ∃ fuel, invoke [allocating] fuel 0 [] memory =
      .ok (objectMemory memory (referenceArrayType node) (objectFieldSlot * 2),
        [.object (.address ⟨memory.nextIdentity, 0⟩)]) := by
  have allocated := newReferenceArray_ok formed node (value := .i32 2) (length := 2)
    (Or.inl rfl) (by decide) (by decide) budget
  simp only [node]
  cil_checked_steps [allocated, node, objectMemory_formObject]
#print axioms stepped_allocation

end Tests.ReferenceArrays
