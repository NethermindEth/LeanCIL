import CIL.Safety.ResultRenaming
import CIL.Safety.ViewRenaming
import CIL.Safety.LocalSlotRenaming

/-!
# Local reads under allocation renaming

Formation and snapshot reads preserve successful values and mapped memory faults.
These operations do not allocate, so the existing allocation map remains fixed.
-/

namespace CIL.Safety

/-- Formation yields the mapped reference, including the exact null case. -/
theorem Memory.Renamed.formValue {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun source target => target = mapping.value source)
      (formValue source reference) (formValue target (mapping.managedReference reference)) := by
  cases reference with
  | null => exact .ok rfl
  | address reference =>
    dsimp only [CIL.Safety.formValue, AllocationRenaming.managedReference]
    rw [related.form reference bound]
    cases checked : CIL.Safety.form source reference with
    | error fault => exact .error (.memory fault (.address reference) 0)
    | ok address => exact .ok rfl
#print axioms Memory.Renamed.formValue

/-- Snapshot reads preserve their scalar bits and initialization flags exactly. -/
theorem Memory.Renamed.loadSnapshot {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (shape : CIL.SnapshotShape) :
    ResultRenamed mapping Eq (loadSnapshot source reference shape)
      (loadSnapshot target (mapping.managedReference reference) shape) := by
  cases reference with
  | null => exact .error (.memory .nullDereference .null 0)
  | address reference =>
    dsimp only [CIL.Safety.loadSnapshot, referenceAt, AllocationRenaming.managedReference,
      Bind.bind, Except.bind]
    rw [related.readSnapshot reference bound]
    cases read : CIL.Safety.readSnapshot source reference shape.width 1 with
    | error fault => exact .error (.memory fault (.address reference) shape.width)
    | ok bytes => exact .ok rfl
#print axioms Memory.Renamed.loadSnapshot

/-- Taking a retained byte home's address preserves its mapped pointer and all checks. -/
theorem Memory.Renamed.localAddress {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (slot : LocalSlot)
    (bound : slot.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun source target => target = mapping.value source)
      (localAddress source slot) (localAddress target (mapping.localSlot slot)) := by
  cases slot with
  | bytes kind reference => exact related.formValue (.address reference) bound
  | root _ | readOnlyRoot _ | opaque128 _ | span _ _ _ | array _ _ => exact .error _
#print axioms Memory.Renamed.localAddress

/-- Reading a retained local preserves its value, including restricted references and snapshots. -/
theorem Memory.Renamed.loadLocal {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (slot : LocalSlot)
    (bound : slot.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun source target => target = mapping.value source)
      (loadLocal source slot) (loadLocal target (mapping.localSlot slot)) := by
  cases slot with
  | root reference =>
    cases reference with
    | none => exact .error .invalidState
    | some reference => exact related.formValue reference (bound reference rfl)
  | readOnlyRoot reference =>
    exact (related.formValue reference bound).bind _ _ (fun _ _ _ => .ok rfl)
  | opaque128 contents =>
    cases contents with
    | none => exact .error (.unsupported "Uninitialized opaque vector local")
    | some contents => exact .ok rfl
  | span width writable contents =>
    cases contents with
    | none => exact .error .invalidState
    | some view =>
      dsimp only [CIL.Safety.loadLocal, AllocationRenaming.localSlot, Option.map,
        AllocationRenaming.spanView]
      have validated := related.spanValidate view (bound view rfl)
      dsimp only [AllocationRenaming.spanView] at validated
      rw [validated]
      split
      · exact .error .invalidState
      · cases view.validate source with
        | error fault => exact .error (.memory fault view.reference 0)
        | ok value => exact .ok rfl
  | array element contents =>
    cases contents with
    | none => exact .error .invalidState
    | some view =>
      dsimp only [CIL.Safety.loadLocal, AllocationRenaming.localSlot, Option.map,
        AllocationRenaming.arrayView]
      have validated := related.arrayValidate view (bound view rfl)
      dsimp only [AllocationRenaming.arrayView] at validated
      rw [validated]
      split
      · exact .error .invalidState
      · cases view.validate source with
        | error fault => exact .error (.memory fault view.reference 0)
        | ok value => exact .ok rfl
  | bytes kind reference =>
    dsimp only [CIL.Safety.loadLocal, AllocationRenaming.localSlot]
    rw [related.read reference bound]
    cases shapeFound : localSnapshotShape kind with
    | none =>
      simp only
      cases CIL.Safety.read source reference (localWidth kind) 1 with
      | error fault => exact .error (.memory fault (.address reference) (localWidth kind))
      | ok bytes => cases kind <;> first | exact .ok rfl | exact .error .invalidState
    | some shape =>
      simp only
      cases CIL.Safety.read source reference (localWidth kind) 1 with
      | error fault =>
        cases fault <;> first
          | exact .error (.memory _ (.address reference) (localWidth kind))
          | exact (related.loadSnapshot (.address reference) bound shape).bind _ _
              (fun _ _ equal => by cases equal; exact .ok rfl)
      | ok bytes => cases kind <;> first | exact .ok rfl | exact .error .invalidState
#print axioms Memory.Renamed.loadLocal

end CIL.Safety
