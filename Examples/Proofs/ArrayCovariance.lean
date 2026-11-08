import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ReferenceArrayElements

/-!
# Covariant stores into an array of class references

`NodeArrays.Put(shapes, index, shape)` stores `shape` into `shapes[index]`. C# lets a `Circle[]`
stand in for a `Shape[]`, so the CLR checks each store against the array's actual element
class. Proved: a `Circle` stored into an array of `Circle` lands in its element and changes
nothing else, null is storable into any array, a `Square` stored into the same array throws
`ArrayTypeMismatchException`, and an index past the length throws `IndexOutOfRangeException`
before the type check, as does a null array `NullReferenceException`.
-/

open CIL.Safety
namespace ExampleProof

/-- The scope every example class lives in. -/
def examples : String := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The class identities of `Shape` and its derived classes. -/
def shapeType : CIL.Extraction.TypeExpr := .object examples "Examples.Shape"
def circleType : CIL.Extraction.TypeExpr := .object examples "Examples.Circle"
def squareType : CIL.Extraction.TypeExpr := .object examples "Examples.Square"

/-- The runtime types of a `Circle` and a `Square`, each deriving from `Shape`. -/
def circle : RuntimeType := ⟨circleType, [shapeType]⟩
def square : RuntimeType := ⟨squareType, [shapeType]⟩

bind_method put putBody :=
  "System.Void Examples.NodeArrays::Put(Examples.Shape[],System.Int32,Examples.Shape)"

/-- Storing a live `Circle` into an owned element of a `Circle[]` makes the element hold it, and
    the method's only effect is that one slot. -/
theorem correctness (memory : Memory) (shapes target : Reference) (length : Nat)
    (index : BitVec 32) (owned : ReferenceArray.Owned memory shapes circleType length index.toNat)
    (live : LiveObject memory target) (allocation : Allocation)
    (found : liveAllocation memory target.allocation = .ok allocation)
    (kind : allocation.kind = .object circle) :
    ∃ fuel final, invoke Extracted.program fuel put
        [.object (.address shapes), .scalar (.i32 index), .object (.address target)] memory =
        .ok (final, []) ∧
      Confined [ReferenceArray.entry shapes index.toNat] memory final ∧
      ReferenceArray.Holds final shapes circleType length index.toNat (.address target) := by
  have storable := ReferenceArray.storableIn_of_lineage (element := circleType) found kind rfl
    rfl (by decide)
  obtain ⟨located, checked, stored, framed, held⟩ := owned.store live storable
  refine ⟨CIL.executionBound Extracted.program put, _, ?_, framed, held⟩
  cil_checked_steps [owned.formed, live.formed, located, checked, stored]

#print axioms correctness

/-- Null is storable into any array of class references. -/
theorem stores_null (memory : Memory) (shapes : Reference) (length : Nat) (index : BitVec 32)
    (owned : ReferenceArray.Owned memory shapes circleType length index.toNat) :
    ∃ fuel final, invoke Extracted.program fuel put
        [.object (.address shapes), .scalar (.i32 index), .object .null] memory =
        .ok (final, []) ∧
      ReferenceArray.Holds final shapes circleType length index.toNat .null := by
  obtain ⟨located, checked, stored, -, held⟩ := owned.store_null
  refine ⟨CIL.executionBound Extracted.program put, _, ?_, held⟩
  cil_checked_steps [owned.formed, located, checked, stored]

#print axioms stores_null

/-- A `Square` is a `Shape` but not a `Circle`: storing it into a `Circle[]` passed as a
    `Shape[]` throws `ArrayTypeMismatchException` at the `stelem.ref`, pc 3. -/
theorem square_mismatch (memory : Memory) (shapes target : Reference) (length : Nat)
    (index : BitVec 32) (owned : ReferenceArray.Owned memory shapes circleType length index.toNat)
    (live : LiveObject memory target) (allocation : Allocation)
    (found : liveAllocation memory target.allocation = .ok allocation)
    (kind : allocation.kind = .object square) :
    ∃ fuel, invoke Extracted.program fuel put
        [.object (.address shapes), .scalar (.i32 index), .object (.address target)] memory =
      .error ⟨put, 3, .thrown "System.ArrayTypeMismatchException"⟩ := by
  have mismatch := ReferenceArray.storableIn_mismatch (element := circleType) found kind rfl
    rfl (by decide)
  have located := owned.slot_located owned.inside
  refine ⟨CIL.executionBound Extracted.program put, ?_⟩
  cil_checked_steps [owned.formed, live.formed, located, mismatch]

#print axioms square_mismatch

/-- An index at or past the length throws `IndexOutOfRangeException` whatever is stored: the
    bounds check precedes the type check. -/
theorem index_out_of_range (memory : Memory) (shapes : Reference) (length : Nat)
    (index : BitVec 32) (live : ReferenceArray.Live memory shapes circleType length)
    (outside : length ≤ index.toNat) (shape : ManagedReference)
    (formed : formObject memory shape = .ok (.object shape)) :
    ∃ fuel, invoke Extracted.program fuel put
        [.object (.address shapes), .scalar (.i32 index), .object shape] memory =
      .error ⟨put, 3, .thrown "System.IndexOutOfRangeException"⟩ := by
  have past := live.slot_outside outside
  refine ⟨CIL.executionBound Extracted.program put, ?_⟩
  cil_checked_steps [live.formed, formed, past]

#print axioms index_out_of_range

/-- A null array throws `NullReferenceException` at the `stelem.ref`. -/
theorem null_array (memory : Memory) (index : BitVec 32) (shape : ManagedReference)
    (formed : formObject memory shape = .ok (.object shape)) :
    ∃ fuel, invoke Extracted.program fuel put [.object .null, .scalar (.i32 index), .object shape]
        memory = .error ⟨put, 3, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program put, ?_⟩
  cil_checked_steps [formed]

#print axioms null_array

end ExampleProof
