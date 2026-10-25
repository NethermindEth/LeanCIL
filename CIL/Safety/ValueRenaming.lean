import CIL.Safety.AllocationRenaming
import CIL.Safety.Frames

/-!
# Values under allocation renaming

References change only allocation identity. Scalar bits, span bounds and mutability,
array element types, and local storage kinds remain exact. Prefix bounds ensure later
allocations cannot alter a value already held by an active frame.
-/

namespace CIL.Safety

/-- A null reference or an address within the already allocated identity prefix. -/
def ManagedReference.Below (limit : Nat) : ManagedReference → Prop
  | .null => True
  | .address reference => reference.allocation < limit

/-- Every reference carried by a checked value belongs to the allocated identity prefix. -/
def Value.Below (limit : Nat) : Value → Prop
  | .scalar _ => True
  | .reference address | .readOnlyReference address | .span address _ =>
    address.Below limit
  | .bufferSpan view => view.reference.Below limit
  | .array view => view.reference.Below limit

namespace AllocationRenaming

/-- Rename a managed reference, preserving null exactly. -/
def managedReference (mapping : AllocationRenaming) : ManagedReference → ManagedReference
  | .null => .null
  | .address reference => .address (mapping.reference reference)

/-- Rename the backing allocation of a span without changing its extent or mutability. -/
def spanView (mapping : AllocationRenaming) (view : SpanView) : SpanView :=
  { view with reference := mapping.managedReference view.reference }

/-- Rename array storage without changing the array length or element type. -/
def arrayView (mapping : AllocationRenaming) (view : ArrayView) : ArrayView :=
  { view with reference := mapping.managedReference view.reference }

/-- Rename every allocation-backed part of a checked value, leaving scalar bits unchanged. -/
def value (mapping : AllocationRenaming) : Value → Value
  | .scalar scalar => .scalar scalar
  | .reference reference => .reference (mapping.managedReference reference)
  | .readOnlyReference reference => .readOnlyReference (mapping.managedReference reference)
  | .span reference length => .span (mapping.managedReference reference) length
  | .bufferSpan view => .bufferSpan (mapping.spanView view)
  | .array view => .array (mapping.arrayView view)

/-- A bounded managed reference stays fixed when the allocation map extends. -/
theorem Extends.managedReference {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) (reference : ManagedReference)
    (bound : reference.Below earlier.sourceLimit) :
    later.managedReference reference = earlier.managedReference reference := by
  cases reference with
  | null => rfl
  | address reference =>
    exact congrArg ManagedReference.address (extension.reference reference bound)
#print axioms Extends.managedReference

/-- A value held across a nested call retains its mapped representation. -/
theorem Extends.value {earlier later : AllocationRenaming} (extension : earlier.Extends later)
    (value : Value) (bound : value.Below earlier.sourceLimit) :
    later.value value = earlier.value value := by
  cases value <;> simp only [AllocationRenaming.value, spanView, arrayView]
  all_goals first
    | rfl
    | rw [extension.managedReference _ bound]
#print axioms Extends.value

/-- The mapped reference lies below the target allocation watermark. -/
theorem managedReference_below (mapping : AllocationRenaming) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) :
    (mapping.managedReference reference).Below mapping.targetLimit := by
  cases reference with
  | null => trivial
  | address reference => exact mapping.bounded reference.allocation bound
#print axioms managedReference_below

/-- A mapped value refers only to already allocated target storage. -/
theorem value_below (mapping : AllocationRenaming) (value : Value)
    (bound : value.Below mapping.sourceLimit) :
    (mapping.value value).Below mapping.targetLimit := by
  cases value with
  | scalar _ => trivial
  | reference reference | readOnlyReference reference | span reference _ =>
    exact mapping.managedReference_below reference bound
  | bufferSpan view => exact mapping.managedReference_below view.reference bound
  | array view => exact mapping.managedReference_below view.reference bound
#print axioms value_below

/-- A scalar result is exactly invariant under every allocation renaming. -/
theorem scalar (mapping : AllocationRenaming) (bits : CIL.Value) :
    mapping.value (.scalar bits) = .scalar bits := rfl
#print axioms scalar

end AllocationRenaming
/-- A reference stays inside the allocated prefix when that prefix grows. -/
theorem ManagedReference.Below.mono {earlier later : Nat} (ordered : earlier ≤ later)
    (reference : ManagedReference) (bounded : reference.Below earlier) : reference.Below later := by
  cases reference with
  | null => trivial
  | address address => exact Nat.lt_of_lt_of_le bounded ordered
#print axioms ManagedReference.Below.mono

/-- Prefix bounds remain true when subsequent execution allocates more identities. -/
theorem Value.Below.mono {earlier later : Nat} (ordered : earlier ≤ later) (value : Value)
    (bounded : value.Below earlier) : value.Below later := by
  cases value <;> first | trivial | exact ManagedReference.Below.mono ordered _ bounded
#print axioms Value.Below.mono
/-- Extending the allocation map leaves all already bounded evaluation-stack values unchanged. -/
theorem AllocationRenaming.Extends.values {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) (values : List Value)
    (bounds : ∀ value ∈ values, value.Below earlier.sourceLimit) :
    values.map later.value = values.map earlier.value := by
  apply List.map_congr_left
  intro value member
  exact extension.value value (bounds value member)
#print axioms AllocationRenaming.Extends.values

end CIL.Safety
