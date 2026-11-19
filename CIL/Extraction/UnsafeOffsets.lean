import CIL.Extraction.UnsafeModels

/-! Runtime models for allocation-relative offsets of checked Unsafe references. -/

namespace CIL.Extraction

/-- The two references whose byte displacement is measured. -/
private def offsetPair (element : TypeExpr) : List TypeExpr := [.byref element, .byref element]

/-- Byte displacements have native signed integer type. -/
private def displacement (_ : TypeExpr) : TypeExpr := .atom runtimeScope "System.IntPtr"

/-- Unsafe.ByteOffset computes a displacement between references to a sized element. -/
def unsafeByteOffsetModel (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel :=
  unsafeGuarded (unsafeSignature reader method offsetPair displacement) (.memory .byteOffset)

/-- The checked offset operations that keep their call. -/
def unsafeOffsetEntries : List ModelEntry :=
  [unsafeEntry name!"ByteOffset" "ByteOffset" "System.IntPtr" "!!0&,!!0&"
    (unsafeDeclaration offsetPair displacement) unsafeByteOffsetModel]

/-- Every resolved offset entry runs the byte displacement operation. -/
theorem unsafeOffsetEntries_yields {property : RuntimeModel → Prop}
    (byteOffset : property (.memory .byteOffset)) :
    ∀ entry ∈ unsafeOffsetEntries, entry.Yields property := by
  simp only [unsafeOffsetEntries, List.mem_singleton, forall_eq]
  intro environment method model found
  rw [unsafeGuarded_eq (admitted := unsafeSignature environment method offsetPair displacement)
    (model := .memory .byteOffset) found]
  exact byteOffset

#print axioms unsafeOffsetEntries_yields

end CIL.Extraction
