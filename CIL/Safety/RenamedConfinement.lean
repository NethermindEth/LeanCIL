import CIL.Safety.RenamedMemoryBelow
import CIL.Safety.ExecutionLifetime

/-!
# Caller confinement from renamed executions

The initial identity map fixes caller storage. Existing execution lifetime theorems
preserve its descriptors; the final memory relation supplies equal bytes and authority.
Fresh references and allocation identities are deliberately absent from the conclusion.
-/

namespace CIL.Safety

/-- Two executions preserving caller descriptors agree exactly on their original caller prefix. -/
theorem Memory.Renamed.callerPrefix {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {initial source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (extension : (AllocationRenaming.identity initial.nextIdentity).Extends mapping)
    (sourceLifetime : AllocationsBelow initial source initial.nextIdentity)
    (targetLifetime : AllocationsBelow initial target initial.nextIdentity) :
    Memory.RenamedBelow initial.nextIdentity mapping scopes source target := by
  refine ⟨related, extension.source, extension.target, ?_, ?_⟩
  · intro identity bound
    exact extension.image identity bound
  · intro identity bound
    exact (targetLifetime.lookup identity bound).trans (sourceLifetime.lookup identity bound).symm
#print axioms Memory.Renamed.callerPrefix

/-- A MemoryBelow postcondition transfers after corresponding successful executions. -/
theorem Memory.Renamed.confined {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {initial source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (extension : (AllocationRenaming.identity initial.nextIdentity).Extends mapping)
    (sourceLifetime : AllocationsBelow initial source initial.nextIdentity)
    (targetLifetime : AllocationsBelow initial target initial.nextIdentity)
    (confined : MemoryBelow initial.nextIdentity initial source) :
    MemoryBelow initial.nextIdentity initial target :=
  (related.callerPrefix extension sourceLifetime targetLifetime).confined confined
#print axioms Memory.Renamed.confined

end CIL.Safety
