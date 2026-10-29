import CIL.Safety.Memory

/-!
# Contiguous span views

Spans of reference-free elements retain allocation identity, element width, length and whether the view may
be used for writing. Forming or slicing a view does not grant memory authority or assert
initialization. Reads and writes use the existing checked memory operations.
-/

namespace CIL.Safety

/-- A reference-free span over existing storage. Readonly views can still observe aliased writes. -/
structure SpanView where
  reference : ManagedReference
  length : Nat
  width : Nat
  writable : Bool
  deriving DecidableEq, Repr

/-- Validate the complete extent without requiring it to be initialized or readable.
    An empty view may end exactly at the allocation boundary. -/
def SpanView.validate (view : SpanView) (memory : Memory) : Checked Unit := do
  if (0 < view.width ∧ view.width < 2^64) then pure () else .error .unsupportedLayout
  if view.length < 2^31 then pure () else .error .outsideAllocation
  match view.reference with
  | .null => if view.length == 0 then return () else .error .nullDereference
  | .address reference =>
    let allocation ← liveAllocation memory reference.allocation
    let finish := reference.offset + view.length * view.width
    if reference.offset < nativeLimit && finish < nativeLimit &&
        finish ≤ allocation.layout.size then pure () else .error .outsideAllocation
    if allocation.layout.referenceSlots.any (fun slot =>
        decide (reference.offset < slot.1 + slot.2 ∧ slot.1 < finish)) then
      .error .unsupportedLayout else return ()

/-- A readonly conversion removes permission through this view without changing memory. -/
def SpanView.asReadOnly (view : SpanView) : SpanView := { view with writable := false }

/-- Slice with natural indices; instruction decoding rejects negative signed inputs first. -/
def SpanView.slice (view : SpanView) (memory : Memory) (start length : Nat) : Checked SpanView := do
  view.validate memory
  if start ≤ view.length && length ≤ view.length - start then pure ()
    else .error .outsideAllocation
  let reference := match view.reference with
    | .null => .null
    | .address reference => .address { reference with offset := reference.offset + start * view.width }
  let result := { view with reference, length }
  result.validate memory
  return result

/-- An element address retains allocation provenance and needs no read or write authority. -/
def SpanView.element (view : SpanView) (memory : Memory) (index : Nat) : Checked Reference := do
  view.validate memory
  if index < view.length then pure () else .error .outsideAllocation
  let .address reference := view.reference | .error .nullDereference
  form memory { reference with offset := reference.offset + index * view.width }

/-- Reading an element checks actual memory authority and initialization. -/
def SpanView.read (view : SpanView) (memory : Memory) (index : Nat) : Checked (List (BitVec 8)) := do
  let reference ← view.element memory index
  Safety.read memory reference view.width 1

/-- Writing requires both a writable span and existing authority over its element bytes. -/
def SpanView.write (view : SpanView) (memory : Memory) (index : Nat)
    (bytes : List (BitVec 8)) : Checked Memory := do
  if view.writable then pure () else .error .unwritable
  if bytes.length == view.width then pure () else .error .unsupportedLayout
  let reference ← view.element memory index
  Safety.write memory reference bytes 1

/-- Fill the entire writable view with one encoded element, validating authority once.
    Empty spans require no byte access; nonempty fills initialize their complete extent. -/
def SpanView.fill (view : SpanView) (memory : Memory)
    (element : List (BitVec 8)) : Checked Memory := do
  view.validate memory
  if view.writable then pure () else .error .unwritable
  if element.length == view.width then pure () else .error .unsupportedLayout
  if view.length == 0 then return memory else
  let .address reference := view.reference | .error .nullDereference
  Safety.write memory reference (List.replicate view.length element).flatten 1

end CIL.Safety
