import CIL.Safety.FrameHomeRenaming
import CIL.Safety.LocalSlotRenaming

/-!
# Uninitialized local setup under renaming

Unmodeled extracted locals preserve their physical home and initialization behavior.
Numeric homes allocate paired identities; roots, spans and arrays allocate no bytes.
-/

namespace CIL.Safety

/-- A valid unmodeled local can be prepared in both memories with an extended allocation map. -/
theorem Memory.Renamed.makeLocalUnmodeled {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceActivation targetActivation : Nat) (scope : scopes sourceActivation targetActivation)
    (kind : CIL.LocalKind) (bounded : localWidth kind < nativeLimit)
    (spanWidth : ∀ width writable, kind = .span width writable → width ∈ [1, 2, 4, 8]) :
    ∃ later slot owned sourceAfter targetAfter,
      mapping.Extends later ∧
      makeLocal sourceActivation kind .unmodeled source = .ok (slot, owned, sourceAfter) ∧
      makeLocal targetActivation kind .unmodeled target =
        .ok (later.localSlot slot, owned.map later.image, targetAfter) ∧
      Memory.Renamed later scopes sourceAfter targetAfter ∧
      slot.Below later.sourceLimit ∧ ∀ identity ∈ owned, identity < later.sourceLimit := by
  have bytes (kind : CIL.LocalKind) (bounded : localWidth kind < nativeLimit) :
      ∃ sourceAfter targetAfter,
        CIL.Safety.allocateHome source sourceActivation (localWidth kind) (localAlignment kind) =
          .ok (⟨source.nextIdentity, 0⟩, sourceAfter) ∧
        CIL.Safety.allocateHome target targetActivation (localWidth kind) (localAlignment kind) =
          .ok (⟨target.nextIdentity, 0⟩, targetAfter) ∧
        Memory.Renamed mapping.allocate scopes sourceAfter targetAfter :=
    related.allocateHome sourceFormed targetFormed staticBounds sourceActivation
      targetActivation _ _ scope bounded (localAlignment_pos kind)
  have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
    change source.nextIdentity < mapping.sourceLimit + 1
    rw [related.sourceLimit]
    exact Nat.lt_succ_self _
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  let slotKind := kind
  cases kind with
  | reference =>
    refine ⟨mapping, .root none, [], source, target, .refl mapping, rfl, rfl, related, ?_, ?_⟩
    · intro address member; cases member
    · intro identity member; cases member
  | array element =>
    refine ⟨mapping, .array element none, [], source, target, .refl mapping,
      rfl, rfl, related, ?_, ?_⟩
    · intro view member; cases member
    · intro identity member; cases member
  | span width writable =>
    have widthOK := spanWidth width writable rfl
    refine ⟨mapping, .span width writable none, [], source, target, .refl mapping,
      ?_, ?_, related, ?_, ?_⟩
    · simp [makeLocal, widthOK]
    · simp [makeLocal, widthOK, AllocationRenaming.localSlot]
    · intro view member; cases member
    · intro identity member; cases member
  | byte | word32 | word64 | narrow _ | aggregate _ | vector128 | vector256 | vector512 =>
    obtain ⟨sourceAfter, targetAfter, sourceHome, targetHome, homes⟩ := bytes _ bounded
    refine ⟨mapping.allocate, .bytes slotKind ⟨source.nextIdentity, 0⟩, [source.nextIdentity],
      sourceAfter, targetAfter, mapping.allocate_extends, ?_, ?_, homes, freshBound, ?_⟩
    · simp only [makeLocal, sourceHome, slotKind, Bind.bind, Except.bind, ite_true,
        Pure.pure, Except.pure]
    · simp only [makeLocal, targetHome, slotKind, Bind.bind, Except.bind, ite_true,
        Pure.pure, Except.pure, AllocationRenaming.localSlot, AllocationRenaming.reference,
        List.map_cons, List.map_nil, freshImage]
    · intro identity member
      have equal := List.mem_singleton.mp member
      exact equal.symm ▸ freshBound
#print axioms Memory.Renamed.makeLocalUnmodeled

/-- A deleted unmodeled local creates private target storage and preserves mapped observations. -/
theorem Memory.Renamed.skipLocalUnmodeled {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (targetFormed : target.WellFormed)
    (activation : Nat) (kind : CIL.LocalKind) (bounded : localWidth kind < nativeLimit)
    (spanWidth : ∀ width writable, kind = .span width writable → width ∈ [1, 2, 4, 8]) :
    ∃ later slot owned targetAfter,
      mapping.Extends later ∧ makeLocal activation kind .unmodeled target =
        .ok (slot, owned, targetAfter) ∧
      Memory.Renamed later scopes source targetAfter ∧
      ∀ identity ∈ owned, identity < later.targetLimit ∧
        ∀ sourceIdentity, sourceIdentity < later.sourceLimit →
          later.image sourceIdentity ≠ identity := by
  have bytes (kind : CIL.LocalKind) (bounded : localWidth kind < nativeLimit) :
      ∃ targetAfter, CIL.Safety.allocateHome target activation
        (localWidth kind) (localAlignment kind) =
          .ok (⟨target.nextIdentity, 0⟩, targetAfter) ∧
        Memory.Renamed mapping.skipTarget scopes source targetAfter :=
    related.skipHome targetFormed activation _ _ bounded (localAlignment_pos kind)
  let slotKind := kind
  cases kind with
  | reference =>
    refine ⟨mapping, .root none, [], target, .refl mapping, rfl, related, ?_⟩
    intro identity member; cases member
  | array element =>
    refine ⟨mapping, .array element none, [], target, .refl mapping, rfl, related, ?_⟩
    intro identity member; cases member
  | span width writable =>
    refine ⟨mapping, .span width writable none, [], target, .refl mapping, ?_, related, ?_⟩
    · simp [makeLocal, spanWidth width writable rfl]
    · intro identity member; cases member
  | byte | word32 | word64 | narrow _ | aggregate _ | vector128 | vector256 | vector512 =>
    obtain ⟨targetAfter, targetHome, homes⟩ := bytes _ bounded
    refine ⟨mapping.skipTarget, .bytes slotKind ⟨target.nextIdentity, 0⟩,
      [target.nextIdentity], targetAfter, mapping.skipTarget_extends, ?_, homes, ?_⟩
    · simp only [makeLocal, targetHome, slotKind, Bind.bind, Except.bind, ite_true,
        Pure.pure, Except.pure]
    · intro identity member
      have equal := List.mem_singleton.mp member
      subst identity
      constructor
      · change target.nextIdentity < mapping.targetLimit + 1
        rw [related.targetLimit]
        exact Nat.lt_succ_self _
      · intro sourceIdentity bound
        change mapping.image sourceIdentity ≠ target.nextIdentity
        rw [← related.targetLimit]
        exact Nat.ne_of_lt (mapping.bounded sourceIdentity bound)
#print axioms Memory.Renamed.skipLocalUnmodeled

end CIL.Safety
