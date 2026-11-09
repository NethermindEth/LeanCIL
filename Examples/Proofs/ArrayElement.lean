import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ReferenceArrayElements

/-!
# Reading an element of an array of class references

`NodeArrays.At(nodes, index)` returns `nodes[index]`. Proved: an index inside the array returns
the reference its element holds, null included, and changes nothing; an index at or past the
length throws `IndexOutOfRangeException` at the `ldelem.ref`, as does a negative index, which
the CLR reads unsigned; a null array throws `NullReferenceException` there.
-/

open CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Node`. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

bind_method elementAt elementAtBody :=
  "Examples.Node Examples.NodeArrays::At(Examples.Node[],System.Int32)"

/-- An element inside the array that holds a live node returns that node and changes nothing. -/
theorem correctness (memory : Memory) (nodes target : Reference) (length : Nat)
    (index : BitVec 32)
    (readable : ReferenceArray.Readable memory nodes nodeType length index.toNat)
    (held : ReferenceArray.of memory nodes index.toNat = .address target)
    (live : LiveObject memory target) :
    ∃ fuel, invoke Extracted.program fuel elementAt
        [.object (.address nodes), .scalar (.i32 index)] memory =
      .ok (memory, [.object (.address target)]) := by
  have loaded := readable.facts held live
  cil_checked_steps [readable.formed, live.formed, loaded.1, loaded.2]

#print axioms correctness

/-- An element inside the array that holds null returns null. -/
theorem returns_null (memory : Memory) (nodes : Reference) (length : Nat) (index : BitVec 32)
    (readable : ReferenceArray.Readable memory nodes nodeType length index.toNat)
    (held : ReferenceArray.of memory nodes index.toNat = .null) :
    ∃ fuel, invoke Extracted.program fuel elementAt
        [.object (.address nodes), .scalar (.i32 index)] memory =
      .ok (memory, [.object .null]) := by
  have loaded := readable.facts_null held
  cil_checked_steps [readable.formed, loaded.1, loaded.2]

#print axioms returns_null

/-- An index at or past the length throws `IndexOutOfRangeException` at pc 2. A negative int32
    index reads as at least `2^31`, so it is past every array's length. -/
theorem index_out_of_range (memory : Memory) (nodes : Reference) (length : Nat)
    (index : BitVec 32) (live : ReferenceArray.Live memory nodes nodeType length)
    (outside : length ≤ index.toNat) :
    ∃ fuel, invoke Extracted.program fuel elementAt
        [.object (.address nodes), .scalar (.i32 index)] memory =
      .error ⟨elementAt, 2, .thrown "System.IndexOutOfRangeException"⟩ := by
  have past := live.slot_outside outside
  cil_checked_steps [live.formed, past]

#print axioms index_out_of_range

/-- A negative index is out of range for every array the model can allocate. -/
theorem negative_out_of_range (memory : Memory) (nodes : Reference) (length : Nat)
    (index : BitVec 32) (live : ReferenceArray.Live memory nodes nodeType length)
    (small : length ≤ 2 ^ 31) (negative : index.toInt < 0) :
    ∃ fuel, invoke Extracted.program fuel elementAt
        [.object (.address nodes), .scalar (.i32 index)] memory =
      .error ⟨elementAt, 2, .thrown "System.IndexOutOfRangeException"⟩ :=
  index_out_of_range memory nodes length index live (by
    rw [BitVec.toInt_eq_toNat_cond] at negative
    split at negative <;> omega)

#print axioms negative_out_of_range

/-- A null array throws `NullReferenceException` at pc 2. -/
theorem null_array (memory : Memory) (index : BitVec 32) :
    ∃ fuel, invoke Extracted.program fuel elementAt [.object .null, .scalar (.i32 index)]
        memory = .error ⟨elementAt, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps []

#print axioms null_array

end ExampleProof
