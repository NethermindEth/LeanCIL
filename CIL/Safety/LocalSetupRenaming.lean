import CIL.Safety.FrameHomeRenaming
import CIL.Safety.LocalSlotRenaming
import CIL.Safety.LocalStoreRenaming
import CIL.Safety.FrameProgress

/-!
# Local setup under renaming

Retained locals preserve their physical home and checked initializer. Numeric homes
allocate paired identities; deleted homes with valid initializers remain private to the target.
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

/-- A retained initializer performs the same checked store in its corresponding fresh home. -/
theorem Memory.Renamed.makeLocalInitialized {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceActivation targetActivation : Nat) (scope : scopes sourceActivation targetActivation)
    (kind : CIL.LocalKind) (initial : CIL.Value) (bounded : localWidth kind < nativeLimit)
    (spanWidth : ∀ width writable, kind = .span width writable → width ∈ [1, 2, 4, 8])
    {slot : LocalSlot} {owned : List AllocationId} {sourceAfter : Memory}
    (made : makeLocal sourceActivation kind initial source = .ok (slot, owned, sourceAfter)) :
    ∃ later targetAfter, mapping.Extends later ∧
      makeLocal targetActivation kind initial target =
        .ok (later.localSlot slot, owned.map later.image, targetAfter) ∧
      Memory.Renamed later scopes sourceAfter targetAfter ∧
      slot.Below later.sourceLimit ∧ ∀ identity ∈ owned, identity < later.sourceLimit := by
  by_cases unmodeled : initial = .unmodeled
  · subst initial
    obtain ⟨later, actualSlot, actualOwned, actualAfter, targetAfter, extension,
      sourceMade, targetMade, remains, slotBound, ownedBound⟩ :=
      related.makeLocalUnmodeled sourceFormed targetFormed staticBounds sourceActivation
        targetActivation scope kind bounded spanWidth
    rw [made] at sourceMade
    cases sourceMade
    exact ⟨later, targetAfter, extension, targetMade, remains, slotBound, ownedBound⟩
  have bytes (kind : CIL.LocalKind) (bounded : localWidth kind < nativeLimit) :=
    related.allocateHome sourceFormed targetFormed staticBounds sourceActivation
      targetActivation (localWidth kind) (localAlignment kind) scope bounded
      (localAlignment_pos kind)
  have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
    rw [← related.sourceLimit]
    exact Nat.lt_succ_self _
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  let retainedKind := kind
  cases kind with
  | reference | array _ =>
    cases initial <;> simp only [CIL.Safety.makeLocal] at made
    all_goals first | contradiction | cases made
    all_goals refine ⟨mapping, target, .refl mapping, ?_, related, ?_, ?_⟩
    all_goals simp [CIL.Safety.makeLocal, AllocationRenaming.localSlot,
      AllocationRenaming.managedReference,
      AllocationRenaming.arrayView, LocalSlot.Below, ManagedReference.Below]
  | span width writable =>
    have widthOK := spanWidth width writable rfl
    cases initial <;> simp only [CIL.Safety.makeLocal, widthOK, not_true_eq_false,
      ite_false] at made
    all_goals first | contradiction | cases made
    all_goals refine ⟨mapping, target, .refl mapping, ?_, related, ?_, ?_⟩
    all_goals simp [CIL.Safety.makeLocal, widthOK, AllocationRenaming.localSlot,
      AllocationRenaming.managedReference, AllocationRenaming.spanView,
      LocalSlot.Below, ManagedReference.Below]
  | byte | word32 | word64 | narrow _ | aggregate _ | vector128 | vector256 | vector512 =>
    obtain ⟨sourceHome, targetHome, sourceAllocated, targetAllocated, homes⟩ := bytes _ bounded
    simp only [CIL.Safety.makeLocal, sourceAllocated, unmodeled, ite_false,
      Bind.bind, Except.bind] at made
    split at made
    · cases made
    rename_i stored sourceStored
    cases stored with
    | mk storedSlot storedMemory =>
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at made
      obtain ⟨rfl, rfl, rfl⟩ := made
      have stores := homes.storeLocal (.bytes retainedKind ⟨source.nextIdentity, 0⟩)
        (.scalar initial) freshBound (by trivial)
      rw [sourceStored] at stores
      obtain ⟨⟨targetSlot, targetMemory⟩, targetStored, slots, remains⟩ := stores.success
      dsimp only at slots remains
      subst targetSlot
      refine ⟨mapping.allocate, targetMemory, mapping.allocate_extends, ?_, remains,
        storeLocal_below (slot := .bytes retainedKind ⟨source.nextIdentity, 0⟩)
          (value := .scalar initial) freshBound (by trivial) sourceStored, ?_⟩
      · simp only [CIL.Safety.makeLocal, targetAllocated, unmodeled, ite_false,
          Bind.bind, Except.bind]
        simp only [AllocationRenaming.localSlot, AllocationRenaming.reference,
          AllocationRenaming.value, freshImage, retainedKind] at targetStored
        simp only [targetStored, List.map_cons, List.map_nil, freshImage,
          Pure.pure, Except.pure, AllocationRenaming.localSlot, AllocationRenaming.reference]
      · intro identity member
        exact (List.mem_singleton.mp member).symm ▸ freshBound
#print axioms Memory.Renamed.makeLocalInitialized

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

/-- Initializing an unmapped numeric home preserves every mapped allocation and permission. -/
private theorem Memory.Renamed.storePrivateLocal {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target after : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (privateHome : ∀ identity, identity < mapping.sourceLimit →
      mapping.image identity ≠ reference.allocation)
    (kind : CIL.LocalKind) (initial : CIL.Value) (number : Nat)
    (encoded : localNumber kind initial = .ok number) {slot : LocalSlot}
    (stored : CIL.Safety.storeLocal target (.bytes kind reference) (.scalar initial) =
      .ok (slot, after)) :
    Memory.Renamed mapping scopes source after := by
  cases initial
  case snapshot shape bytes =>
    cases kind <;> simp [localNumber, CIL.Value.hasUnspecified] at encoded
  case v128Low64 low => simp [localNumber, CIL.Value.hasUnspecified] at encoded
  all_goals
    simp only [CIL.Safety.storeLocal, encoded, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at stored
    cases written : CIL.Safety.write target reference (numberBytes number (localWidth kind)) 1 <;>
      simp only [written] at stored
    · cases stored
    · cases stored
      exact related.writePrivate reference privateHome _ _ written
#print axioms Memory.Renamed.storePrivateLocal

/-- Valid inserted initializers use only private target homes, without a source setup premise. -/
theorem Memory.Renamed.skipLocalInitialized {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (targetFormed : target.WellFormed)
    (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value)
    (fits : InitializerFits kind initial) (bounded : localWidth kind < nativeLimit)
    (spanWidth : ∀ width writable, kind = .span width writable → width ∈ [1, 2, 4, 8]) :
    ∃ later slot owned targetAfter,
      mapping.Extends later ∧ makeLocal activation kind initial target =
        .ok (slot, owned, targetAfter) ∧
      Memory.Renamed later scopes source targetAfter ∧
      ∀ identity ∈ owned, identity < later.targetLimit ∧
        ∀ sourceIdentity, sourceIdentity < later.sourceLimit →
          later.image sourceIdentity ≠ identity := by
  by_cases unknown : initial = .unmodeled
  · subst initial
    exact related.skipLocalUnmodeled targetFormed activation kind bounded spanWidth
  have privateHome : ∀ identity, identity < mapping.skipTarget.sourceLimit →
      mapping.skipTarget.image identity ≠ target.nextIdentity := by
    intro identity bound
    rw [← related.targetLimit]
    exact Nat.ne_of_lt (mapping.bounded identity bound)
  let retainedKind := kind
  cases kind with
  | reference =>
    cases initial <;> simp [InitializerFits] at fits unknown
    refine ⟨mapping, .root (some .null), [], target, .refl mapping, rfl, related, ?_⟩
    intro identity member; cases member
  | array element =>
    cases initial <;> simp [InitializerFits] at fits unknown
    refine ⟨mapping, .array element (some ⟨.null, 0, element⟩), [], target,
      .refl mapping, rfl, related, ?_⟩
    intro identity member; cases member
  | span width writable =>
    cases initial <;> simp [InitializerFits] at fits unknown
    refine ⟨mapping, .span width writable (some ⟨.null, 0, width, writable⟩), [], target,
      .refl mapping, ?_, related, ?_⟩
    all_goals simp_all [makeLocal]
  | byte | word32 | word64 | narrow _ | aggregate _ | vector128 | vector256 | vector512 =>
    obtain ⟨home, allocated, homes⟩ := related.skipHome targetFormed activation
      (localWidth retainedKind) (localAlignment retainedKind) bounded (localAlignment_pos _)
    obtain ⟨number, encoded⟩ := initializer_numeric_number fits (by simp)
      (by intros; simp) (by intros; simp) unknown
    obtain ⟨slot, after, stored⟩ := fresh_home_storeLocal_succeeds _ _ _ _ _ _ _ allocated encoded
    have remains := homes.storePrivateLocal _ privateHome _ _ _ encoded stored
    refine ⟨mapping.skipTarget, slot, [target.nextIdentity], after,
      mapping.skipTarget_extends, ?_, remains, ?_⟩
    · simp only [makeLocal, retainedKind, allocated, unknown, ite_false, Bind.bind,
        Except.bind, stored, Pure.pure, Except.pure]
    · intro identity member
      have equal := List.mem_singleton.mp member
      subst identity
      constructor
      · change target.nextIdentity < mapping.targetLimit + 1
        rw [related.targetLimit]
        exact Nat.lt_succ_self _
      · exact privateHome
#print axioms Memory.Renamed.skipLocalInitialized

end CIL.Safety
