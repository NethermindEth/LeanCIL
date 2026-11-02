import CIL.Safety.StaticMemory

/-!
# Caller memory that binds static values

An opaque readonly value is not extracted, so a load reads it from the caller's static binding
and faults without one. `Memory.boundStatics` is caller memory holding each listed field in its
own readable immutable static allocation, registered under the field's identity. A proof about
every value such a field may take quantifies over the bytes it passes here.
-/

namespace CIL.Safety

/-- Allocation `index` holds the bytes of the `index`-th entry, readable and immutable at byte
    alignment, and the static registry binds that entry's field identity to it. -/
def Memory.boundStatics (values : List (Nat × List (BitVec 8))) : Memory where
  allocations := fun id => values[id]?.map fun (_, bytes) =>
    ⟨.immutableStatic, ⟨bytes.length, 1, []⟩, true, [bytes.length]⟩
  cells := fun id offset =>
    match values[id]?.bind (fun (_, bytes) => bytes[offset]?) with
    | some byte => ⟨byte, true⟩
    | none => ⟨0, false⟩
  views := values.zipIdx.map fun ((_, bytes), id) => ⟨id, 0, bytes.length, true, false⟩
  nextIdentity := values.length
  staticBindings := values.zipIdx.map fun ((identity, _), id) => (identity, ⟨id, 0⟩)

end CIL.Safety
