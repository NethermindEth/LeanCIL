import CIL.Safety.AllocationRenaming
import CIL.Safety.Frames
import CIL.Safety.LocalIndexMap

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
  -- A home names a slot of the frame whose stack holds it, not an allocation.
  | .scalar _ | .methodPointer _ | .methodTable _ | .spanHome _ => True
  | .reference address | .readOnlyReference address | .span address _ | .object address =>
    address.Below limit
  | .bufferSpan view => view.reference.Below limit
  | .array view => view.reference.Below limit

namespace AllocationRenaming

/-- Rename the backing allocation of a span without changing its extent or mutability. -/
def spanView (mapping : AllocationRenaming) (view : SpanView) : SpanView :=
  { view with reference := mapping.managedReference view.reference }

/-- Rename array storage without changing the array length or element type. -/
def arrayView (mapping : AllocationRenaming) (view : ArrayView) : ArrayView :=
  { view with reference := mapping.managedReference view.reference }

/-- Rename every allocation-backed part of a checked value, leaving scalar bits unchanged. -/
def value (mapping : AllocationRenaming) : Value → Value
  | .methodPointer pointer => .methodPointer pointer
  | .methodTable table => .methodTable table
  | .scalar scalar => .scalar scalar
  | .reference reference => .reference (mapping.managedReference reference)
  | .object reference => .object (mapping.managedReference reference)
  | .readOnlyReference reference => .readOnlyReference (mapping.managedReference reference)
  | .span reference length => .span (mapping.managedReference reference) length
  | .bufferSpan view => .bufferSpan (mapping.spanView view)
  | .array view => .array (mapping.arrayView view)
  | .spanHome slot => .spanHome slot

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
  | scalar _ | methodPointer _ | methodTable _ | spanHome _ => trivial
  | reference reference | readOnlyReference reference | span reference _ | object reference =>
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

/-- A stack value of a frame whose locals `indices` relocates: a home names the relocated slot,
    and every other value is renamed as `mapping.value` renames it. -/
def LocalIndexMap.value (indices : LocalIndexMap) (mapping : AllocationRenaming) : Value → Value
  | .spanHome slot => .spanHome (indices.index slot)
  | .methodPointer pointer => .methodPointer pointer
  | .methodTable table => .methodTable table
  | .scalar scalar => .scalar scalar
  | .reference reference => .reference (mapping.managedReference reference)
  | .object reference => .object (mapping.managedReference reference)
  | .readOnlyReference reference => .readOnlyReference (mapping.managedReference reference)
  | .span reference length => .span (mapping.managedReference reference) length
  | .bufferSpan view => .bufferSpan (mapping.spanView view)
  | .array view => .array (mapping.arrayView view)

/-- A value that is not a home is renamed as `mapping.value` renames it. -/
theorem LocalIndexMap.value_of_not_home (indices : LocalIndexMap) (mapping : AllocationRenaming)
    {value : Value} (free : value.isHome = false) :
    indices.value mapping value = mapping.value value := by
  cases value <;> first | rfl | cases free
#print axioms LocalIndexMap.value_of_not_home

/-- A list without homes, such as call arguments or results, is renamed by `mapping.value`. -/
theorem LocalIndexMap.values_of_not_home (indices : LocalIndexMap) (mapping : AllocationRenaming)
    {values : List Value} (free : ∀ value ∈ values, value.isHome = false) :
    values.map (indices.value mapping) = values.map mapping.value :=
  List.map_congr_left fun _ member => indices.value_of_not_home mapping (free _ member)
#print axioms LocalIndexMap.values_of_not_home

/-- Pushing a value that is not a home onto a renamed stack renames the whole stack. -/
theorem LocalIndexMap.push_of_not_home (indices : LocalIndexMap) (mapping : AllocationRenaming)
    {value : Value} (rest : List Value) (free : value.isHome = false) :
    mapping.value value :: rest.map (indices.value mapping) =
      (value :: rest).map (indices.value mapping) := by
  rw [List.map_cons, indices.value_of_not_home mapping free]
#print axioms LocalIndexMap.push_of_not_home

/-- Renaming keeps whether a value is a home. -/
theorem LocalIndexMap.value_isHome (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (value : Value) : (indices.value mapping value).isHome = value.isHome := by
  cases value <;> rfl
#print axioms LocalIndexMap.value_isHome

/-- Renaming keeps whether a value exposes unspecified scalar bits. -/
theorem LocalIndexMap.hasUnspecified (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (value : Value) : (indices.value mapping value).hasUnspecified = value.hasUnspecified := by
  cases value <;> rfl
#print axioms LocalIndexMap.hasUnspecified

/-- The unspecified-operand guard sees the same scalar operands after renaming. -/
theorem LocalIndexMap.unspecifiedOperands (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (count : Nat) (values : List Value) :
    unspecifiedOperands count (values.map (indices.value mapping)) =
      unspecifiedOperands count values := by
  simp only [CIL.Safety.unspecifiedOperands, ← List.map_take, List.any_map,
    Function.comp_def, indices.hasUnspecified]
#print axioms LocalIndexMap.unspecifiedOperands

/-- A renamed value lies below the target allocation watermark. -/
theorem LocalIndexMap.value_below (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (value : Value) (bound : value.Below mapping.sourceLimit) :
    (indices.value mapping value).Below mapping.targetLimit := by
  cases value <;> first | trivial | exact mapping.value_below _ bound
#print axioms LocalIndexMap.value_below

/-- A value held across a nested call keeps its renamed representation. -/
theorem LocalIndexMap.value_extends (indices : LocalIndexMap) {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) (value : Value) (bound : value.Below earlier.sourceLimit) :
    indices.value later value = indices.value earlier value := by
  cases value <;> first | rfl | exact extension.value _ bound
#print axioms LocalIndexMap.value_extends

/-- Extending the allocation map leaves every bounded stack value of a suspended frame
    unchanged. -/
theorem LocalIndexMap.values_extends (indices : LocalIndexMap)
    {earlier later : AllocationRenaming} (extension : earlier.Extends later) (values : List Value)
    (bounds : ∀ value ∈ values, value.Below earlier.sourceLimit) :
    values.map (indices.value later) = values.map (indices.value earlier) :=
  List.map_congr_left fun value member => indices.value_extends extension value (bounds _ member)
#print axioms LocalIndexMap.values_extends

end CIL.Safety
