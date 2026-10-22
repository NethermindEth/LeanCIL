import CIL.Extraction.Layout
import CIL.Instructions

namespace CIL.Extraction

inductive FieldAccess where
  | load | store | address
  deriving DecidableEq, Repr

inductive SizeAccess where
  | load | store | initialize | copy | sizeOf | construct | referenceAdd
  deriving DecidableEq, Repr

/-- Raw type/field identities at layout-dependent uses; no computed offsets or sizes. -/
inductive LayoutUse where
  | field (pc type field : Nat) (access : FieldAccess)
  | size (pc type : Nat) (access : SizeAccess)
  | local (slot type : Nat)
  | parameter (slot type : Nat)
  deriving DecidableEq, Repr

private def checkField (layout : FieldLayout) (signed : Bool) : FieldAccess → Op → Bool
  | .address, .fieldAddress offset => offset == layout.offset
  | .load, .fieldAt offset width actualSigned => !layout.aggregate && offset == layout.offset && width == layout.width && actualSigned == signed
  | .store, .setFieldAt offset width => !layout.aggregate && offset == layout.offset && width == layout.width
  | .load, .aggregateFieldAt offset width => layout.aggregate && offset == layout.offset && width == layout.width
  | .store, .setAggregateFieldAt offset width => layout.aggregate && offset == layout.offset && width == layout.width
  | _, _ => false

private def checkSize (size : Nat) : SizeAccess → Op → Bool
  | .load, .loadAggregate width | .store, .storeAggregate width
  | .initialize, .initAggregate width | .copy, .copyObject width => width == size
  | .sizeOf, .const32 bits => bits.toNat == size
  | .construct, .newAggregate _ _ width => width.val == size
  | .referenceAdd, .memory (.add width _) => width == size
  | _, _ => false

/-- Bind independently computed layout data to actual instructions and frame slots. -/
def validateLayoutUse (raw : List RawLayout) (layouts : Array ComputedLayout)
    (method : Method) : LayoutUse → Bool
  | .field pc type index access => (do
      let metadata ← raw[type]?
      let field ← metadata.fields[index]?
      let layout ← layouts[type]?
      let computed ← layout.layout.fields[index]?
      let operation ← method.code[pc]?
      let signed := field.type == FieldType.signed8 || field.type == FieldType.signed16
      return checkField computed signed access operation).getD false
  | .size pc type access => (do
      let layout ← layouts[type]?
      let operation ← method.code[pc]?
      return checkSize layout.layout.size access operation).getD false
  | .local slot type => (do
      let layout ← layouts[type]?
      match ← method.localKinds[slot]? with
      | .aggregate size => return size.val == layout.layout.size
      | _ => return false).getD false
  | .parameter slot type => (do
      let layout ← layouts[type]?
      match (← method.parameterHomes[slot]?).2 with
      | .aggregate size => return size.val == layout.layout.size
      | _ => return false).getD false

def MethodLayoutsValid (raw : List RawLayout) (layouts : Array ComputedLayout)
    (method : Method) (uses : List LayoutUse) : Prop :=
  LayoutsValid raw layouts method.profile.architecture ∧ ∀ use ∈ uses, validateLayoutUse raw layouts method use = true

instance (raw : List RawLayout) (layouts : Array ComputedLayout) (method : Method)
    (uses : List LayoutUse) : Decidable (MethodLayoutsValid raw layouts method uses) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem method_layout_use_checked {raw : List RawLayout} {layouts : Array ComputedLayout}
    {method : Method} {uses : List LayoutUse} (valid : MethodLayoutsValid raw layouts method uses)
    (use : LayoutUse) (present : use ∈ uses) : validateLayoutUse raw layouts method use = true :=
  valid.2 use present

end CIL.Extraction
