import CIL.Safety.MemoryRenamingOperations
import CIL.Safety.SnapshotMemory

/-!
# Snapshot writes under allocation renaming

Typed copies preserve both byte contents and initialization flags on corresponding
allocations. An uninitialized byte remains uninitialized in the target memory.
-/

namespace CIL.Safety

/-- A snapshot store preserves the relation without inventing initialization. -/
theorem Memory.Renamed.writeSnapshot {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat) :
    ResultEquivalent (Memory.Renamed mapping scopes)
      (writeSnapshot source reference bytes alignment)
      (writeSnapshot target (mapping.reference reference) bytes alignment) := by
  unfold CIL.Safety.writeSnapshot
  apply ResultEquivalent.bind (related.write reference bound (bytes.map Prod.fst) alignment)
  intro sourceWritten targetWritten written
  apply ResultEquivalent.ok
  refine ⟨written.sourceLimit, written.targetLimit, written.allocations, ?_,
    written.permissions, written.staticBindings, written.stackLimit⟩
  intro identity identityBound offset
  have identities : mapping.image identity = mapping.image reference.allocation ↔
      identity = reference.allocation :=
    ⟨mapping.injective _ _ identityBound bound, congrArg mapping.image⟩
  simp only [AllocationRenaming.reference, identities, related.cells identity identityBound]
#print axioms Memory.Renamed.writeSnapshot

end CIL.Safety
