import CIL.Safety.ValueRenaming

/-!
# Local slots under allocation renaming

The representation of a retained slot preserves its kind and initialization state.
Only stored references and byte-home identities change. Bounds allow suspended frames
to keep the same representation as later calls extend the allocation map.
-/

namespace CIL.Safety

/-- All references held in a local slot belong to the allocated identity prefix. -/
def LocalSlot.Below (limit : Nat) : LocalSlot → Prop
  | .bytes _ reference => reference.allocation < limit
  | .root reference => ∀ address ∈ reference, address.Below limit
  | .readOnlyRoot address => address.Below limit
  | .opaque128 _ | .methodPointer .. | .methodTable .. => True
  | .span _ _ view => ∀ span ∈ view, span.reference.Below limit
  | .array _ view => ∀ array ∈ view, array.reference.Below limit

/-- An existing local remains bounded as the allocation prefix grows. -/
theorem LocalSlot.Below.mono {before after : Nat} (growth : before ≤ after) (slot : LocalSlot)
    (bound : slot.Below before) : slot.Below after := by
  have reference (address : ManagedReference) (bound : address.Below before) :
      address.Below after := by
    cases address with
    | null => trivial
    | address reference => exact Nat.lt_of_lt_of_le bound growth
  cases slot with
  | bytes kind address => exact Nat.lt_of_lt_of_le bound growth
  | opaque128 _ | methodPointer _ _ | methodTable _ _ => trivial
  | root address => exact fun value member => reference value (bound value member)
  | readOnlyRoot address => exact reference address bound
  | span _ _ view => exact fun value member => reference value.reference (bound value member)
  | array _ view => exact fun value member => reference value.reference (bound value member)
#print axioms LocalSlot.Below.mono

namespace AllocationRenaming

/-- Retained slot metadata and scalar contents stay exact; backing identities are mapped. -/
def localSlot (mapping : AllocationRenaming) : LocalSlot → LocalSlot
  | .bytes kind reference => .bytes kind (mapping.reference reference)
  | .root reference => .root (reference.map mapping.managedReference)
  | .readOnlyRoot address => .readOnlyRoot (mapping.managedReference address)
  | .methodPointer signature value => .methodPointer signature value
  | .methodTable signature value => .methodTable signature value
  | .opaque128 contents => .opaque128 contents
  | .span width writable view => .span width writable (view.map mapping.spanView)
  | .array element view => .array element (view.map mapping.arrayView)

/-- A bounded slot keeps the same target representation across later allocations. -/
theorem Extends.localSlot {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) (slot : LocalSlot)
    (bound : slot.Below earlier.sourceLimit) : later.localSlot slot = earlier.localSlot slot := by
  cases slot with
  | bytes kind reference =>
    exact congrArg (LocalSlot.bytes kind) (extension.reference reference bound)
  | opaque128 _ | methodPointer _ _ | methodTable _ _ => rfl
  | readOnlyRoot reference =>
    exact congrArg LocalSlot.readOnlyRoot (extension.managedReference reference bound)
  | root reference =>
    cases reference with
    | none => rfl
    | some reference =>
      simp only [AllocationRenaming.localSlot, Option.map_some]
      rw [extension.managedReference reference (bound reference rfl)]
  | span width writable view =>
    cases view with
    | none => rfl
    | some view =>
      simp only [AllocationRenaming.localSlot, Option.map_some, spanView]
      rw [extension.managedReference view.reference (bound view rfl)]
  | array element view =>
    cases view with
    | none => rfl
    | some view =>
      simp only [AllocationRenaming.localSlot, Option.map_some, arrayView]
      rw [extension.managedReference view.reference (bound view rfl)]
#print axioms Extends.localSlot

/-- Mapped slots refer only to the already allocated target identity prefix. -/
theorem localSlot_below (mapping : AllocationRenaming) (slot : LocalSlot)
    (bound : slot.Below mapping.sourceLimit) :
    (mapping.localSlot slot).Below mapping.targetLimit := by
  cases slot with
  | bytes kind reference => exact mapping.bounded _ bound
  | opaque128 _ | methodPointer _ _ | methodTable _ _ => trivial
  | readOnlyRoot reference => exact mapping.managedReference_below reference bound
  | root reference =>
    cases reference with
    | none => intro address member; cases member
    | some reference =>
      intro address member
      cases member
      exact mapping.managedReference_below reference (bound reference rfl)
  | span width writable view =>
    cases view with
    | none => intro address member; cases member
    | some view =>
      intro address member
      cases member
      exact mapping.managedReference_below view.reference (bound view rfl)
  | array element view =>
    cases view with
    | none => intro address member; cases member
    | some view =>
      intro address member
      cases member
      exact mapping.managedReference_below view.reference (bound view rfl)
#print axioms localSlot_below

end AllocationRenaming
end CIL.Safety
