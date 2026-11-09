import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceArrayElements

/-!
# Storing an opaque reference into an array of strings

`TagArrays.Put(tags, index, tagged)` stores `tagged.Tag`, a string the model never reads
through, into `tags[index]`. `string` is sealed, so a `string[]` holds strings at run time and
the store's covariance check is decided by the stored object's own class. Proved: a string
lands in its element and changes nothing else, a null tag is always storable, and the store
throws `IndexOutOfRangeException` for an index past the length and `NullReferenceException` for
a null array, each at the `stelem.ref`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

/-- The class identity of `System.String`, outside the model. -/
def textType : CIL.Extraction.TypeExpr := .object CIL.Extraction.runtimeScope "System.String"

bind_method put putBody :=
  "System.Void Examples.TagArrays::Put(System.String[],System.Int32,Examples.Tagged)"

/-- A string held in `tagged.Tag` stores into an owned element of a `string[]`, which then holds
    it, and the method's only effect is that one slot. -/
theorem correctness (memory : Memory) (tags tagged text : Reference) (length : Nat)
    (index : BitVec 32) (owned : ReferenceArray.Owned memory tags textType length index.toNat)
    (readable : Tagged.Tag.Readable memory tagged)
    (held : Tagged.Tag.of memory tagged = .address text) (live : LiveObject memory text)
    (allocation : Allocation) (bases : List CIL.Extraction.TypeExpr)
    (found : liveAllocation memory text.allocation = .ok allocation)
    (kind : allocation.kind = .object ⟨textType, bases⟩) :
    ∃ fuel final, invoke Extracted.program fuel put
        [.object (.address tags), .scalar (.i32 index), .object (.address tagged)] memory =
        .ok (final, []) ∧
      Confined [ReferenceArray.entry tags index.toNat] memory final ∧
      ReferenceArray.Holds final tags textType length index.toNat (.address text) := by
  have storable := ReferenceArray.storableIn_of_lineage (element := textType) found kind rfl
    rfl (List.mem_cons_self ..)
  obtain ⟨located, checked, stored, framed, holds⟩ := owned.store live storable
  refine ⟨CIL.executionBound Extracted.program put, _, ?_, framed, holds⟩
  cil_checked_steps [owned.formed, readable.live.formed, readable.facts held live, live.formed,
    located, checked, stored]

#print axioms correctness

/-- A null tag stores into any element of a `string[]`. -/
theorem stores_null (memory : Memory) (tags tagged : Reference) (length : Nat)
    (index : BitVec 32) (owned : ReferenceArray.Owned memory tags textType length index.toNat)
    (readable : Tagged.Tag.Readable memory tagged)
    (held : Tagged.Tag.of memory tagged = .null) :
    ∃ fuel final, invoke Extracted.program fuel put
        [.object (.address tags), .scalar (.i32 index), .object (.address tagged)] memory =
        .ok (final, []) ∧
      ReferenceArray.Holds final tags textType length index.toNat .null := by
  obtain ⟨located, checked, stored, -, holds⟩ := owned.store_null
  refine ⟨CIL.executionBound Extracted.program put, _, ?_, holds⟩
  cil_checked_steps [owned.formed, readable.live.formed, readable.located,
    readable.load_null held, located, checked, stored]

#print axioms stores_null

/-- An index at or past the length throws `IndexOutOfRangeException` at the `stelem.ref`, pc 4,
    before the tag's class is checked. -/
theorem index_out_of_range (memory : Memory) (tags tagged : Reference) (length : Nat)
    (index : BitVec 32) (live : ReferenceArray.Live memory tags textType length)
    (outside : length ≤ index.toNat) (readable : Tagged.Tag.Readable memory tagged)
    (forms : Tagged.Tag.Forms memory tagged) :
    ∃ fuel, invoke Extracted.program fuel put
        [.object (.address tags), .scalar (.i32 index), .object (.address tagged)] memory =
      .error ⟨put, 4, .thrown "System.IndexOutOfRangeException"⟩ := by
  cil_checked_steps [live.formed, readable.live.formed, readable.located,
    readable.load_forms forms, live.slot_outside outside]

#print axioms index_out_of_range

/-- A null array throws `NullReferenceException` at the `stelem.ref`. -/
theorem null_array (memory : Memory) (tagged : Reference) (index : BitVec 32)
    (readable : Tagged.Tag.Readable memory tagged) (forms : Tagged.Tag.Forms memory tagged) :
    ∃ fuel, invoke Extracted.program fuel put
        [.object .null, .scalar (.i32 index), .object (.address tagged)] memory =
      .error ⟨put, 4, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [readable.live.formed, readable.located, readable.load_forms forms]

#print axioms null_array

end ExampleProof
