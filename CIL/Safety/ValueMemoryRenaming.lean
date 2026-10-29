import CIL.Safety.LocalLoadRenaming
import CIL.Safety.SnapshotRenaming

/-!
# Scalar and snapshot memory operations under renaming

Mapped managed references observe identical scalar bytes and initialization state.
Writes retain the same access checks, mutability restrictions and target memory relation.
-/

namespace CIL.Safety

/-- Dereferencing a mapped managed pointer preserves its bytes and checked memory fault. -/
theorem Memory.Renamed.dereference {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (width alignment : Nat) :
    dereference target (mapping.managedReference reference) width alignment =
      dereference source reference width alignment := by
  cases reference with
  | null => rfl
  | address reference => exact related.read reference bound width alignment
#print axioms Memory.Renamed.dereference

/-- Scalar loads and vector snapshot fallback preserve their exact decoded contents. -/
theorem Memory.Renamed.loadValue {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (width : Nat) (signed : Bool) :
    ResultRenamed mapping Eq (loadValue source reference width signed)
      (loadValue target (mapping.managedReference reference) width signed) := by
  unfold CIL.Safety.loadValue
  rw [related.dereference reference bound]
  by_cases vector : (width = 16 || width = 32 || width = 64) = true
  all_goals simp only [vector, ite_true, ite_false]
  · cases CIL.Safety.dereference source reference width ordinaryAccessAlignment with
    | error fault =>
      cases fault <;> first
        | exact .error (.memory _ reference width)
        | exact related.loadSnapshot reference bound _
    | ok bytes =>
      repeat' first
        | contradiction | exact .ok rfl | exact .error (.unsupported "Memory value width") | split
  · cases CIL.Safety.dereference source reference width ordinaryAccessAlignment with
    | error fault => exact .error (.memory fault reference width)
    | ok bytes =>
      repeat' first
        | contradiction | exact .ok rfl | exact .error (.unsupported "Memory value width") | split
#print axioms Memory.Renamed.loadValue

/-- Stores preserve scalar bits or snapshot initialization flags on corresponding allocations. -/
theorem Memory.Renamed.storeValue {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (value : CIL.Value) :
    ResultRenamed mapping (Memory.Renamed mapping scopes)
      (storeValue source reference value)
      (storeValue target (mapping.managedReference reference) value) := by
  cases value <;> simp only [CIL.Safety.storeValue, CIL.Value.hasUnspecified,
    Bool.false_eq_true, Bool.true_eq, ite_true, ite_false]
  all_goals first
    | exact .error _
    | (split
       · cases reference with
         | null => exact .error (.memory .nullDereference .null 0)
         | address reference =>
           exact (related.writeSnapshot reference bound _ _).checkedAt (.address reference) _
       · exact .error .invalidState)
    | (cases reference with
       | null => exact .error (.memory .nullDereference .null 0)
       | address reference =>
         exact (related.write reference bound _ _).checkedAt (.address reference) _)
#print axioms Memory.Renamed.storeValue

/-- Typed transfer reads preserve the value and initialization mask under allocation renaming. -/
theorem Memory.Renamed.loadTransfer {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (kind : CIL.TransferKind) :
    ResultRenamed mapping Eq (loadTransfer source reference kind)
      (loadTransfer target (mapping.managedReference reference) kind) := by
  cases kind with
  | scalar width signed =>
    simp only [CIL.Safety.loadTransfer]
    split
    · exact related.loadValue reference bound width signed
    · exact .error _
  | snapshot shape => exact related.loadSnapshot reference bound shape
#print axioms Memory.Renamed.loadTransfer

/-- Typed transfer writes preserve checked authority and related final memory. -/
theorem Memory.Renamed.storeTransfer {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : ManagedReference)
    (bound : reference.Below mapping.sourceLimit) (kind : CIL.TransferKind) (value : CIL.Value) :
    ResultRenamed mapping (Memory.Renamed mapping scopes)
      (storeTransfer source reference kind value)
      (storeTransfer target (mapping.managedReference reference) kind value) := by
  cases reference with
  | null => exact .error (.memory .nullDereference .null 0)
  | address reference =>
    simp only [CIL.Safety.storeTransfer, referenceAt, AllocationRenaming.managedReference,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    repeat first
      | exact .error _
      | exact (related.write reference bound _ _).checkedAt (.address reference) _
      | exact (related.writeSnapshot reference bound _ _).checkedAt (.address reference) _
      | split
#print axioms Memory.Renamed.storeTransfer

end CIL.Safety
