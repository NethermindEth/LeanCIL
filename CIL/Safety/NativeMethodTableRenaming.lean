import CIL.Safety.NativeMethodTables
import CIL.Safety.MemoryRenaming

/-! Native handler-table access follows the existing allocation and static-binding renaming. -/

namespace CIL.Safety

/-- Rename the checked backing allocation without changing any callable identity. -/
def AllocationRenaming.nativeTable (mapping : AllocationRenaming) (table : NativeMethodTable) :
    NativeMethodTable :=
  { table with
    origin := mapping.reference table.origin
    cursor := mapping.reference table.cursor }

/-- Native cursor geometry is preserved when both references name the bound allocation. -/
theorem Memory.Renamed.nativeTableCheck {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (table : NativeMethodTable)
    (bound : table.origin.allocation < mapping.sourceLimit)
    (sameAllocation : table.cursor.allocation = table.origin.allocation) :
    (mapping.nativeTable table).check target = table.check source := by
  rcases table with ⟨signature, entries, ⟨originId, originOffset⟩, ⟨cursorId, cursorOffset⟩⟩
  dsimp only at bound sameAllocation
  subst cursorId
  have allocations := related.allocations originId bound
  dsimp only [AllocationRenaming.nativeTable, AllocationRenaming.reference]
  unfold NativeMethodTable.check liveAllocation
  generalize sourceFound : source.allocations originId = sourceAllocation at allocations ⊢
  generalize targetFound : target.allocations (mapping.image originId) = targetAllocation
    at allocations ⊢
  cases allocations with
  | none => rfl
  | @some sourceDescriptor targetDescriptor descriptor =>
    dsimp only
    simp only [← descriptor.live]
    cases sourceDescriptor.live <;>
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, ← descriptor.layout,
        bne, descriptor.kind.immutable]
#print axioms Memory.Renamed.nativeTableCheck

/-- Native loads preserve opaque identities when their backing allocation is renamed. -/
theorem Memory.Renamed.nativeTableLoad {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (table : NativeMethodTable)
    (bound : table.origin.allocation < mapping.sourceLimit)
    (sameAllocation : table.cursor.allocation = table.origin.allocation) :
    (mapping.nativeTable table).load target = table.load source := by
  unfold NativeMethodTable.load
  rw [related.nativeTableCheck table bound sameAllocation]
  have cursorBound : table.cursor.allocation < mapping.sourceLimit := sameAllocation ▸ bound
  simp only [AllocationRenaming.nativeTable, AllocationRenaming.reference]
  rw [show CIL.Safety.read target
      { allocation := mapping.image table.cursor.allocation, offset := table.cursor.offset }
      nativeMethodWidth nativeMethodWidth =
      CIL.Safety.read source table.cursor nativeMethodWidth nativeMethodWidth from
    related.read table.cursor cursorBound _ _]
  rfl
#print axioms Memory.Renamed.nativeTableLoad

/-- Moving a native cursor commutes with allocation renaming. -/
theorem Memory.Renamed.nativeTableAdd {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (table : NativeMethodTable)
    (bound : table.origin.allocation < mapping.sourceLimit)
    (sameAllocation : table.cursor.allocation = table.origin.allocation) (offset : BitVec 64) :
    (mapping.nativeTable table).addBytes target offset =
      (table.addBytes source offset).map mapping.nativeTable := by
  let moved : NativeMethodTable := { table with cursor := { table.cursor with offset :=
    (BitVec.ofNat 64 table.cursor.offset + offset).toNat } }
  have movedCheck := related.nativeTableCheck moved bound sameAllocation
  unfold NativeMethodTable.addBytes
  rw [related.nativeTableCheck table bound sameAllocation]
  change (table.check source >>= fun _ => (mapping.nativeTable moved).check target >>= fun _ =>
    pure (mapping.nativeTable moved)) =
    (table.check source >>= fun _ => moved.check source >>= fun _ => pure moved).map
      mapping.nativeTable
  rw [movedCheck]
  cases table.check source <;> cases moved.check source <;> rfl
#print axioms Memory.Renamed.nativeTableAdd

/-- Successful geometry validation establishes a live source allocation. -/
theorem NativeMethodTable.check_bounded (table : NativeMethodTable) (memory : Memory)
    (formed : memory.WellFormed) (checked : table.check memory = .ok ()) :
    table.origin.allocation < memory.nextIdentity := by
  cases found : memory.allocations table.origin.allocation with
  | none => simp [NativeMethodTable.check, liveAllocation, found, Bind.bind, Except.bind] at checked
  | some allocation => exact (formed.1 _ _ found).1
#print axioms NativeMethodTable.check_bounded

/-- A successfully resolved native binding remains resolved after allocation renaming. -/
theorem Memory.Renamed.nativeTableView_success {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (table : CIL.MethodTable) (view : NativeMethodTable)
    (viewed : nativeTableView table source = .ok view) :
    nativeTableView table target = .ok (mapping.nativeTable view) := by
  unfold nativeTableView at viewed ⊢
  cases targets : table.targets with
  | none => simp [targets] at viewed
  | some entries =>
    simp only [targets] at viewed ⊢
    cases backingFound : table.backing with
    | none => simp [backingFound] at viewed
    | some backing =>
      simp only [backingFound] at viewed ⊢
      cases found : source.staticBindings.find? (·.1 == backing.identity) with
      | none => simp [found] at viewed
      | some binding =>
        rcases binding with ⟨identity, origin⟩
        have targetFound : target.staticBindings.find? (·.1 == backing.identity) =
            some (identity, mapping.reference origin) := by
          rw [related.staticBindings]
          simpa only [List.find?_map, Function.comp_def, found, Option.map_some]
        simp only [found, targetFound] at viewed ⊢
        let original : NativeMethodTable := ⟨table.signature, entries, origin,
          { origin with offset := origin.offset + backing.byteOffset }⟩
        change (original.check source >>= fun _ => pure original) = .ok view at viewed
        cases checked : original.check source with
        | error fault => simp [checked, Bind.bind, Except.bind] at viewed
        | ok unit =>
          cases unit
          simp only [checked, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Except.ok.injEq] at viewed
          subst view
          have bound : original.origin.allocation < mapping.sourceLimit := by
            rw [related.sourceLimit]
            exact original.check_bounded source formed checked
          change ((mapping.nativeTable original).check target >>= fun _ =>
            pure (mapping.nativeTable original)) = .ok (mapping.nativeTable original)
          rw [related.nativeTableCheck original bound rfl, checked]
          rfl
#print axioms Memory.Renamed.nativeTableView_success

/-- A resolved view has checked geometry and both references share one allocation. -/
theorem nativeTableView_checked (table : CIL.MethodTable) (memory : Memory)
    (view : NativeMethodTable) (viewed : nativeTableView table memory = .ok view) :
    view.check memory = .ok () ∧ view.cursor.allocation = view.origin.allocation := by
  unfold nativeTableView at viewed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at viewed
  repeat' first
    | contradiction
    | split at viewed
  all_goals simp_all only [Except.ok.injEq]
  subst view
  constructor
  · simpa using ‹_ = Except.ok _›
  · rfl
#print axioms nativeTableView_checked

/-- Successful native loads preserve their checked opaque result under allocation renaming. -/
theorem Memory.Renamed.loadNativeTable_success {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (table : CIL.MethodTable) (pointer : CIL.MethodPointer)
    (loaded : loadNativeTable table source = .ok pointer) :
    loadNativeTable table target = .ok pointer := by
  unfold loadNativeTable at loaded ⊢
  cases viewed : nativeTableView table source with
  | error fault => simp [viewed, Bind.bind, Except.bind] at loaded
  | ok view =>
    simp only [viewed, Bind.bind, Except.bind] at loaded
    rw [related.nativeTableView_success formed table view viewed]
    simp only [Bind.bind, Except.bind]
    have valid := nativeTableView_checked table source view viewed
    have bound : view.origin.allocation < mapping.sourceLimit := by
      rw [related.sourceLimit]
      exact view.check_bounded source formed valid.1
    rw [related.nativeTableLoad view bound valid.2, loaded]
#print axioms Memory.Renamed.loadNativeTable_success

/-- Successful native offsets preserve their stable binding and relative byte position. -/
theorem Memory.Renamed.addNativeTable_success {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : source.WellFormed)
    (table result : CIL.MethodTable) (offset : BitVec 64)
    (added : addNativeTable table source offset = .ok result) :
    addNativeTable table target offset = .ok result := by
  unfold addNativeTable at added ⊢
  cases viewed : nativeTableView table source with
  | error fault => simp [viewed, Bind.bind, Except.bind] at added
  | ok view =>
    simp only [viewed, Bind.bind, Except.bind] at added
    rw [related.nativeTableView_success formed table view viewed]
    simp only [Bind.bind, Except.bind]
    have valid := nativeTableView_checked table source view viewed
    have bound : view.origin.allocation < mapping.sourceLimit := by
      rw [related.sourceLimit]
      exact view.check_bounded source formed valid.1
    rw [related.nativeTableAdd view bound valid.2]
    cases moved : view.addBytes source offset with
    | error fault => simp [moved, Bind.bind, Except.bind] at added
    | ok next =>
      simpa only [moved, Except.map, Bind.bind, Except.bind,
        AllocationRenaming.nativeTable, AllocationRenaming.reference] using added
#print axioms Memory.Renamed.addNativeTable_success

end CIL.Safety
