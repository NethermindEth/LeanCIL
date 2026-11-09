import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceArrayElements

/-!
# Loading an opaque reference from an array of strings

`TagArrays.Take(tagged, tags, index)` stores `tags[index]` into `tagged.Tag`. The element is a
string the model never reads through: it is loaded and stored as the reference it is. Proved:
the field ends up holding the element's string, or null, changing that field alone, and an index
past the length throws `IndexOutOfRangeException` at the `ldelem.ref`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

/-- The class identity of `System.String`, outside the model. -/
def textType : CIL.Extraction.TypeExpr := .object CIL.Extraction.runtimeScope "System.String"

bind_method take takeBody :=
  "System.Void Examples.TagArrays::Take(Examples.Tagged,System.String[],System.Int32)"

/-- The string an element holds becomes the tag, and only the tag's slot changes. -/
theorem correctness (memory : Memory) (tagged tags text : Reference) (length : Nat)
    (index : BitVec 32) (owned : Tagged.Tag.Owned memory tagged)
    (readable : ReferenceArray.Readable memory tags textType length index.toNat)
    (held : ReferenceArray.of memory tags index.toNat = .address text)
    (live : LiveObject memory text) :
    ∃ fuel final, invoke Extracted.program fuel take
        [.object (.address tagged), .object (.address tags), .scalar (.i32 index)] memory =
        .ok (final, []) ∧
      Confined [Tagged.Tag.entry tagged] memory final ∧
      Tagged.Tag.Holds final tagged (.address text) := by
  have loaded := readable.facts held live
  obtain ⟨stored, framed, holds⟩ := owned.store live
  refine ⟨CIL.executionBound Extracted.program take, _, ?_, framed, holds⟩
  cil_checked_steps [owned.live.formed, readable.formed, live.formed, loaded.1, loaded.2,
    owned.located, stored]

#print axioms correctness

/-- A null element becomes a null tag. -/
theorem takes_null (memory : Memory) (tagged tags : Reference) (length : Nat)
    (index : BitVec 32) (owned : Tagged.Tag.Owned memory tagged)
    (readable : ReferenceArray.Readable memory tags textType length index.toNat)
    (held : ReferenceArray.of memory tags index.toNat = .null) :
    ∃ fuel final, invoke Extracted.program fuel take
        [.object (.address tagged), .object (.address tags), .scalar (.i32 index)] memory =
        .ok (final, []) ∧
      Tagged.Tag.Holds final tagged .null := by
  have loaded := readable.facts_null held
  obtain ⟨stored, -, holds⟩ := owned.store_formed (value := .null) rfl
  refine ⟨CIL.executionBound Extracted.program take, _, ?_, holds⟩
  cil_checked_steps [owned.live.formed, readable.formed, loaded.1, loaded.2, owned.located,
    stored]

#print axioms takes_null

/-- An index at or past the length throws `IndexOutOfRangeException` at the `ldelem.ref`, pc 3. -/
theorem index_out_of_range (memory : Memory) (tagged tags : Reference) (length : Nat)
    (index : BitVec 32) (object : LiveObject memory tagged)
    (live : ReferenceArray.Live memory tags textType length) (outside : length ≤ index.toNat) :
    ∃ fuel, invoke Extracted.program fuel take
        [.object (.address tagged), .object (.address tags), .scalar (.i32 index)] memory =
      .error ⟨take, 3, .thrown "System.IndexOutOfRangeException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program take, ?_⟩
  cil_checked_steps [object.formed, live.formed, live.slot_outside outside]

#print axioms index_out_of_range

end ExampleProof
