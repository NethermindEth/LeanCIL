import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceArrayElements

/-!
# An array of class references held in a class field

`Examples.Bucket` holds its `Items`, an array of nodes, in a field. The field's slot holds the
array's reference like any class-typed field, so `Bucket.Items` is a `ReferenceField` and the
array it names has the elements of `ReferenceArray`. `NodeArrays.First(bucket)` returns
`bucket.Items[0]`. Proved: it returns the node the first element holds and changes nothing,
throws `NullReferenceException` at the `ldelem.ref` when the field holds null, and
`IndexOutOfRangeException` there for an empty array.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

/-- The class identity of `Examples.Node`. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

bind_method first firstBody := "Examples.Node Examples.NodeArrays::First(Examples.Bucket)"

/-- A bucket whose array holds a live node first returns that node and changes nothing. -/
theorem correctness (memory : Memory) (bucket items target : Reference) (length : Nat)
    (readable : Bucket.Items.Readable memory bucket)
    (array : Bucket.Items.of memory bucket = .address items)
    (element : ReferenceArray.Readable memory items nodeType length 0)
    (held : ReferenceArray.of memory items 0 = .address target)
    (live : LiveObject memory target) :
    ∃ fuel, invoke Extracted.program fuel first [.object (.address bucket)] memory =
      .ok (memory, [.object (.address target)]) := by
  have loaded := element.facts held live
  refine ⟨CIL.executionBound Extracted.program first, ?_⟩
  cil_checked_steps [readable.facts array element.object, readable.live.formed, live.formed,
    loaded.1, loaded.2, leaveFrame]

#print axioms correctness

/-- A bucket whose field holds null throws `NullReferenceException` at the `ldelem.ref`, pc 3:
    the field load succeeds and pushes the null it reads. -/
theorem null_items (memory : Memory) (bucket : Reference)
    (readable : Bucket.Items.Readable memory bucket)
    (array : Bucket.Items.of memory bucket = .null) :
    ∃ fuel, invoke Extracted.program fuel first [.object (.address bucket)] memory =
      .error ⟨first, 3, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program first, ?_⟩
  cil_checked_steps [readable.live.formed, readable.located, readable.load_null array]

#print axioms null_items

/-- A bucket holding an empty array throws `IndexOutOfRangeException` at the `ldelem.ref`. -/
theorem empty_items (memory : Memory) (bucket items : Reference)
    (readable : Bucket.Items.Readable memory bucket)
    (array : Bucket.Items.of memory bucket = .address items)
    (live : ReferenceArray.Live memory items nodeType 0) :
    ∃ fuel, invoke Extracted.program fuel first [.object (.address bucket)] memory =
      .error ⟨first, 3, .thrown "System.IndexOutOfRangeException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program first, ?_⟩
  cil_checked_steps [readable.facts array live.object, readable.live.formed,
    live.slot_outside (index := 0) (Nat.le_refl _)]

#print axioms empty_items

end ExampleProof
