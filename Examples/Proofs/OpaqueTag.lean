import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFields

/-!
# Opaque tag

`Examples.Tagged` holds a `string` `Tag`, a class the model does not represent. Its slot holds
an object reference the model copies without reading through it. `CopyTag(target, source)`
stores `source.Tag` into `target.Tag`. Proved: its contract, for a null tag and a present one
alike, with the one slot it writes as its whole footprint, and the `NullReferenceException` of
a null `source` at its load and of a null `target` at its store.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method copyTag copyTagBody :=
  "System.Void Examples.Objects::CopyTag(Examples.Tagged,Examples.Tagged)"

/-- `CopyTag(target, source)` leaves `target.Tag` holding the reference `source.Tag` held, null
    or not, and changes nothing else. -/
def copyTagContract : MethodContract (Reference × Reference) where
  args := fun (target, source) => [.object (.address target), .object (.address source)]
  pre := fun (target, source) memory => Tagged.Tag.Owned memory target ∧
    Tagged.Tag.Readable memory source ∧ Tagged.Tag.Forms memory source
  footprint := fun (target, _) => [Tagged.Tag.entry target]
  post := fun (target, source) initial final values => values = [] ∧
    Tagged.Tag.Holds final target (Tagged.Tag.of initial source)

/-- `CopyTag` meets its contract: one `ldfld` and one `stfld` of the tag's slot. -/
theorem correctness : copyTagContract.Holds Extracted.program copyTag := by
  rintro ⟨target, source⟩ memory ⟨owned, readable, forms⟩
  obtain ⟨stored, framed, held⟩ := owned.store_formed forms.formed
  refine MethodContract.Holds.intro _ [] ?_ framed ⟨rfl, held⟩
  cil_checked_steps [readable.load_forms forms, stored]

#print axioms correctness

/-- A null `source` throws `NullReferenceException` at the tag load, pc 2. -/
theorem copyTag_null_source_throws (memory : Memory) (target : Reference)
    (live : LiveObject memory target) :
    ∃ fuel, invoke Extracted.program fuel copyTag [.object (.address target), .object .null]
      memory = .error ⟨copyTag, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

#print axioms copyTag_null_source_throws

/-- A null `target` throws `NullReferenceException` at the tag store, pc 3, after the load of
    `source.Tag` succeeds. -/
theorem copyTag_null_target_throws (memory : Memory) (source : Reference)
    (readable : Tagged.Tag.Readable memory source) (forms : Tagged.Tag.Forms memory source) :
    ∃ fuel, invoke Extracted.program fuel copyTag [.object .null, .object (.address source)]
      memory = .error ⟨copyTag, 3, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [readable.load_forms forms]

#print axioms copyTag_null_target_throws

end ExampleProof
