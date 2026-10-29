import CIL.Extraction.Layout
import CIL.Instructions

/-!
# Layout uses

Emitted instructions carry concrete field offsets, widths and struct sizes. A `LayoutUse`
names one such site by raw type and field identity only; `MethodLayoutsValid` then checks
each named site's emitted operands against the independently computed layout table.
`LayoutCoverage` separately proves that the list of uses names every such site.
-/

namespace CIL.Extraction

/-- How an instruction uses a struct field. -/
inductive FieldAccess where
  | load | store | address
  deriving DecidableEq, Repr

/-- How an instruction uses a struct's size, including scaled reference addition/subtraction. -/
inductive SizeAccess where
  | load | store | initialize | copy | sizeOf | construct | referenceAdd | referenceSubtract
  | spanElement | spanSource | spanTarget
  | arrayElement
  deriving DecidableEq, Repr

/-- The native-width negative stride used to subtract an element offset. -/
def subtractionStride (width : Nat) : Nat := (-(BitVec.ofNat 64 width)).toNat

/-- Scaling by the negative stride is exactly native-width subtraction of the scaled offset. -/
theorem subtractionStride_mul (width : Nat) (offset : BitVec 64) :
    BitVec.ofNat 64 (subtractionStride width) * offset = -(BitVec.ofNat 64 width * offset) := by
  simp only [subtractionStride, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.neg_mul]
#print axioms subtractionStride_mul

/-- Raw type/field identities at layout-dependent uses; no computed offsets or sizes. -/
inductive LayoutUse where
  | field (pc type field : Nat) (access : FieldAccess)
  | size (pc type : Nat) (access : SizeAccess)
  | local (slot type : Nat)
  | parameter (slot type : Nat)
  deriving DecidableEq, Repr

/-- The emitted field operation uses exactly the computed offset and width, and the
    aggregate form exactly when the field is a nested struct. -/
private def checkField (layout : FieldLayout) (signed : Bool) : FieldAccess → Op → Bool
  | .address, .fieldAddress offset => offset == layout.offset
  | .load, .fieldAt offset width actualSigned =>
    !layout.aggregate && offset == layout.offset && width == layout.width &&
      actualSigned == signed
  | .store, .setFieldAt offset width =>
    !layout.aggregate && offset == layout.offset && width == layout.width
  | .load, .aggregateFieldAt offset width =>
    layout.aggregate && offset == layout.offset && width == layout.width
  | .store, .setAggregateFieldAt offset width =>
    layout.aggregate && offset == layout.offset && width == layout.width
  | _, _ => false

/-- The emitted size-dependent operation uses exactly the computed struct size. -/
private def checkSize (size alignment : Nat) : SizeAccess → Op → Bool
  | .load, .memory (.pointerTransfer (.snapshot (.aggregate width)) actual false)
  | .store, .memory (.pointerTransfer (.snapshot (.aggregate width)) actual true) =>
    width == size && actual == alignment
  | .arrayElement, .newArray (.aggregate _ width)
  | .arrayElement, .memory (.arrayAddress (.aggregate _ width) _)
  | .arrayElement, .memory (.arrayTransfer (.aggregate _ width) _)
  | .arrayElement, .memory (.arraySpan (.aggregate _ width) _ _)
  | .arrayElement, .initializeSpanLocal _ (.array (.aggregate _ width) _ _) => width == size
  | .load, .memory (.marshalRead (.snapshot (.aggregate width)) _)
  | .store, .memory (.marshalWrite (.snapshot (.aggregate width)) _) => width == size
  | .load, .loadAggregate width | .store, .storeAggregate width
  | .initialize, .initAggregate width | .copy, .copyObject width => width == size
  | .sizeOf, .const32 bits => bits.toNat == size
  | .construct, .newAggregate _ _ width => width.val == size
  | .spanElement, .memory (.spanItem width)
  | .spanElement, .memory (.spanCopy width _)
  | .spanElement, .memory (.spanFill width _)
  | .spanElement, .memory (.spanFromReference width _)
  | .spanElement, .memory (.spanSingleReference width _)
  | .spanElement, .initializeSpanLocal _ (.reference width _)
  | .spanElement, .initializeSpanLocal _ (.singleReference width _) => width == size
  | .spanSource, .memory (.spanReinterpret width _ _) => width == size
  | .spanTarget, .memory (.spanReinterpret _ width _) => width == size
  | .referenceAdd, .memory (.add width _) => width == size
  | .referenceSubtract, .memory (.add stride _) => stride == subtractionStride size
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
      let metadata ← raw[type]?
      if access = SizeAccess.arrayElement ∧ metadata.byRefLike = true then none else pure ()
      let layout ← layouts[type]?
      let operation ← method.code[pc]?
      return checkSize layout.layout.size layout.alignment access operation).getD false
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

/-- The layout table is valid for the method's architecture and every listed use agrees
    with it. -/
def MethodLayoutsValid (raw : List RawLayout) (layouts : Array ComputedLayout)
    (method : Method) (uses : List LayoutUse) : Prop :=
  LayoutsValid raw layouts method.profile.architecture ∧
    ∀ use ∈ uses, validateLayoutUse raw layouts method use = true

instance (raw : List RawLayout) (layouts : Array ComputedLayout) (method : Method)
    (uses : List LayoutUse) : Decidable (MethodLayoutsValid raw layouts method uses) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem method_layout_use_checked {raw : List RawLayout} {layouts : Array ComputedLayout}
    {method : Method} {uses : List LayoutUse} (valid : MethodLayoutsValid raw layouts method uses)
    (use : LayoutUse) (present : use ∈ uses) : validateLayoutUse raw layouts method use = true :=
  valid.2 use present

end CIL.Extraction
