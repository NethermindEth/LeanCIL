import CIL.Extraction.Layout
import CIL.Instructions

/-!
# Layout uses

A `LayoutUse` names a struct construction, local or parameter home. `MethodLayoutsValid`
checks its size against the computed layout for the method's architecture. Instance field
instructions carry a typed field reference and read their offset and width from that layout.
`LayoutUsesComplete` derives the required uses from the raw method.
-/

namespace CIL.Extraction

/-- The native-width negative stride used to subtract an element offset. -/
def subtractionStride (width : Nat) : Nat := (-(BitVec.ofNat 64 width)).toNat

/-- Scaling by the negative stride is exactly native-width subtraction of the scaled offset. -/
theorem subtractionStride_mul (width : Nat) (offset : BitVec 64) :
    BitVec.ofNat 64 (subtractionStride width) * offset = -(BitVec.ofNat 64 width * offset) := by
  simp only [subtractionStride, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.neg_mul]
#print axioms subtractionStride_mul

/-- Whether a load of a field of this kind sign-extends it to the evaluation stack: only the
    narrow signed integers do. -/
def signedField (kind : FieldType) : Bool := kind == .signed8 || kind == .signed16

/-- The site and raw layout index of a struct construction or frame slot. -/
inductive LayoutUse where
  /-- A `newobj` of the struct, whose link states the size it allocates. -/
  | size (pc type : Nat)
  | local (slot type : Nat)
  | parameter (slot type : Nat)
  deriving DecidableEq, Repr

/-- Bind independently computed layout data to actual instructions and frame slots. -/
def validateLayoutUse (raw : List RawLayout) (layouts : Array ComputedLayout)
    (method : Method) : LayoutUse → Bool
  | .size pc type => (do
      let _ ← raw[type]?
      let layout ← layouts[type]?
      let operation ← method.code[pc]?
      -- A construction allocates the size its link states; its operand states none.
      return operation.constructs && match method.linkAt pc with
        | some (.aggregate _ width) => width.val == layout.layout.size
        | _ => false).getD false
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

end CIL.Extraction
