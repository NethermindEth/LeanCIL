import CIL.Safety.ReferenceRenaming
import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.ViewPositionRenaming

/-!
# Checked memory primitives for instruction simulation

These lemmas preserve the diagnostic reference independently of the checked access address.
They compose raw memory correspondences with execution faults and successful results.
-/

namespace CIL.Safety

/-- Checked byte reads preserve bytes and rename the reported diagnostic reference. -/
theorem Memory.Renamed.checkedRead {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (width alignment : Nat)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping Eq
      (checkedAt diagnostic reportedWidth (CIL.Safety.read source reference width alignment))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        (CIL.Safety.read target (mapping.reference reference) width alignment)) := by
  rw [related.read reference bound]
  exact (ResultEquivalent.eq_refl _).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedRead

/-- Checked access guards preserve their success and mapped fault diagnostics. -/
theorem Memory.Renamed.checkedAccess {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (width alignment : Nat) (writing : Bool)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping Eq
      (checkedAt diagnostic reportedWidth
        (CIL.Safety.access source reference width alignment writing))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        (CIL.Safety.access target (mapping.reference reference) width alignment writing)) := by
  rw [related.access reference bound]
  exact (ResultEquivalent.eq_refl _).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedAccess

/-- Checked writes preserve the memory relation and mapped fault diagnostics. -/
theorem Memory.Renamed.checkedWrite {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (bytes : List (BitVec 8)) (alignment : Nat)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping (Memory.Renamed mapping scopes)
      (checkedAt diagnostic reportedWidth (CIL.Safety.write source reference bytes alignment))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        (CIL.Safety.write target (mapping.reference reference) bytes alignment)) :=
  (related.write reference bound bytes alignment).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedWrite

/-- Checked pointer arithmetic returns the mapped address or the corresponding fault. -/
theorem Memory.Renamed.checkedAdd {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (size : Nat) (offset : BitVec 64)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping (fun left right => right = mapping.reference left)
      (checkedAt diagnostic reportedWidth (CIL.Safety.add source reference size offset))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        (CIL.Safety.add target (mapping.reference reference) size offset)) := by
  rw [related.add reference bound]
  exact (ResultEquivalent.of_map _ _).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedAdd

/-- Span extent validation preserves exact checks with a mapped diagnostic reference. -/
theorem Memory.Renamed.checkedSpan {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping Eq (checkedAt diagnostic reportedWidth (view.validate source))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        ((mapping.spanView view).validate target)) := by
  rw [related.spanValidate view bound]
  exact (ResultEquivalent.eq_refl _).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedSpan

/-- Array extent validation preserves exact checks with a mapped diagnostic reference. -/
theorem Memory.Renamed.checkedArray {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : ArrayView)
    (bound : view.reference.Below mapping.sourceLimit)
    (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping Eq (checkedAt diagnostic reportedWidth (view.validate source))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        ((mapping.arrayView view).validate target)) := by
  rw [related.arrayValidate view bound]
  exact (ResultEquivalent.eq_refl _).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedArray

/-- Snapshot writes preserve initialization flags and mapped diagnostic references. -/
theorem Memory.Renamed.checkedWriteSnapshot {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (bytes : List (BitVec 8 × Bool))
    (alignment : Nat) (diagnostic : ManagedReference) (reportedWidth : Nat) :
    ResultRenamed mapping (Memory.Renamed mapping scopes)
      (checkedAt diagnostic reportedWidth
        (CIL.Safety.writeSnapshot source reference bytes alignment))
      (checkedAt (mapping.managedReference diagnostic) reportedWidth
        (CIL.Safety.writeSnapshot target (mapping.reference reference) bytes alignment)) :=
  (related.writeSnapshot reference bound bytes alignment).checkedAt diagnostic reportedWidth
#print axioms Memory.Renamed.checkedWriteSnapshot

/-- Managed dereferencing preserves bytes, null rejection and mapped fault diagnostics. -/
theorem Memory.Renamed.checkedDereference {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (width alignment : Nat) :
    ResultRenamed mapping Eq
      (checkedAt reference width (CIL.Safety.dereference source reference width alignment))
      (checkedAt (mapping.managedReference reference) width
        (CIL.Safety.dereference target (mapping.managedReference reference) width alignment)) := by
  rw [related.dereference reference bound]
  exact (ResultEquivalent.eq_refl _).checkedAt reference width
#print axioms Memory.Renamed.checkedDereference

end CIL.Safety
