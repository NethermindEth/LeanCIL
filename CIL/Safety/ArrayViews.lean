import CIL.ArrayTypes
import CIL.Safety.SpanViews

/-!
# Supplied primitive arrays

An array retains its element type, length and allocation-relative data reference. Its contents
and authority use the existing checked memory model. Null and empty arrays remain distinct;
no operation here allocates an array or grants access to its bytes.
-/

namespace CIL.Safety

/-- A supplied array's immutable shape and backing storage, including the null array. -/
structure ArrayView where
  reference : ManagedReference
  length : Nat
  elementType : CIL.ArrayElement
  deriving DecidableEq, Repr

/-- The same extent as a writable buffer view; actual writes still require memory authority. -/
def ArrayView.storage (view : ArrayView) : SpanView :=
  ⟨view.reference, view.length, view.elementType.width, true⟩

/-- Formation checks preserve null arrays and validate live, bounded non-null extents. -/
def ArrayView.validate (view : ArrayView) (memory : Memory) : Checked Unit :=
  view.storage.validate memory

/-- An element position is always in bounds; an empty or null array has no element address. -/
def ArrayView.element (view : ArrayView) (memory : Memory) (index : Nat) : Checked Reference := do
  view.validate memory
  if view.reference == .null then .error .nullDereference else
    view.storage.element memory index

/-- Element reads require readable, initialized bytes in the original allocation. -/
def ArrayView.read (view : ArrayView) (memory : Memory) (index : Nat) :
    Checked (List (BitVec 8)) := do
  let reference ← view.element memory index
  Safety.read memory reference view.elementType.width 1

/-- Element writes require authority and preserve bytes outside the selected element. -/
def ArrayView.write (view : ArrayView) (memory : Memory) (index : Nat)
    (bytes : List (BitVec 8)) : Checked Memory := do
  let reference ← view.element memory index
  if bytes.length != view.elementType.width then .error .unsupportedLayout else
    Safety.write memory reference bytes 1

end CIL.Safety
