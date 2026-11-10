import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ReferenceArrayElements

/-!
# The length of an array of class references

`NodeArrays.Count(nodes)` returns `nodes.Length`. The length is the allocation's slot count,
read without touching any element; a null array throws `NullReferenceException` at `ldlen`.
-/

open CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Node`. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

bind_method count countBody := "System.Int32 Examples.NodeArrays::Count(Examples.Node[])"

/-- A live array of `length` nodes returns `length` and changes nothing. -/
theorem correctness (memory : Memory) (nodes : Reference) (length : Nat)
    (live : ReferenceArray.Live memory nodes nodeType length) :
    ∃ fuel, invoke Extracted.program fuel count [.object (.address nodes)] memory =
      .ok (memory, [.scalar (.i32 ((BitVec.ofNat 64 length).setWidth 32))]) := by
  cil_checked_steps

#print axioms correctness

/-- A null array throws `NullReferenceException` at `ldlen`, pc 1. -/
theorem null_array (memory : Memory) :
    ∃ fuel, invoke Extracted.program fuel count [.object .null] memory =
      .error ⟨count, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

#print axioms null_array

end ExampleProof
