import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceArrayElements

/-!
# Replacing an array held in a class field

`NodeArrays.Refill(bucket, items)` stores the array `items` into `bucket.Items`. The field's
slot holds the array's reference, so the store is the class-typed field store: proved, it
changes that slot alone and leaves `items` there, and a null bucket throws
`NullReferenceException` at the `stfld`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

/-- The class identity of `Examples.Node`. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

bind_method refill refillBody :=
  "System.Void Examples.NodeArrays::Refill(Examples.Bucket,Examples.Node[])"

/-- `Refill(bucket, items)` leaves `items` in `bucket.Items` and changes only that slot. -/
theorem correctness (memory : Memory) (bucket items : Reference) (length : Nat)
    (owned : Bucket.Items.Owned memory bucket)
    (live : ReferenceArray.Live memory items nodeType length) :
    ∃ fuel final, invoke Extracted.program fuel refill
        [.object (.address bucket), .object (.address items)] memory = .ok (final, []) ∧
      Confined [Bucket.Items.entry bucket] memory final ∧
      Bucket.Items.Holds final bucket (.address items) := by
  obtain ⟨stored, framed, held⟩ := owned.store live.object
  refine ⟨CIL.executionBound Extracted.program refill, _, ?_, framed, held⟩
  cil_checked_steps [owned.live.formed, owned.located, live.formed, stored]

#print axioms correctness

/-- A null bucket throws `NullReferenceException` at the `stfld`, pc 2. -/
theorem null_bucket (memory : Memory) (items : Reference) (length : Nat)
    (live : ReferenceArray.Live memory items nodeType length) :
    ∃ fuel, invoke Extracted.program fuel refill [.object .null, .object (.address items)]
        memory = .error ⟨refill, 2, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program refill, ?_⟩
  cil_checked_steps [live.formed]

#print axioms null_bucket

end ExampleProof
