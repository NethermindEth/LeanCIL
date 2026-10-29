import CIL.Safety.LocalSetupRenaming
import CIL.Safety.LocalIndexMap
import CIL.Safety.FrameExitRenaming
import CIL.Safety.FrameSetupLemmas

/-!
# Frame setup with interleaved dead declarations

Local lists are built by the actual frame allocator. Retained initializers receive
paired homes and valid inserted declarations receive private target homes. The result
binds the executable local operand map, ownership and evolving allocation correspondence.
-/

namespace CIL.Safety

/-- Retained initializers remain exact; inserted dead homes must have compatible initializers. -/
inductive LocalDeclarations : LocalIndexMap → List CIL.LocalKind → List CIL.Value →
    List CIL.LocalKind → List CIL.Value → Prop
  | nil : LocalDeclarations .nil [] [] [] []
  | keep {indices sourceKinds sourceValues targetKinds targetValues}
      (kind : CIL.LocalKind) (initial : CIL.Value)
      (rest : LocalDeclarations indices sourceKinds sourceValues targetKinds targetValues) :
      LocalDeclarations (.keep indices) (kind :: sourceKinds) (initial :: sourceValues)
        (kind :: targetKinds) (initial :: targetValues)
  | skip {indices sourceKinds sourceValues targetKinds targetValues}
      (kind : CIL.LocalKind) (initial : CIL.Value) (fits : InitializerFits kind initial)
      (rest : LocalDeclarations indices sourceKinds sourceValues targetKinds targetValues) :
      LocalDeclarations (.skip indices) sourceKinds sourceValues
        (kind :: targetKinds) (initial :: targetValues)

/-- Corresponding retained slots remain bounded across subsequent calls. -/
def LocalSlot.Renamed (mapping : AllocationRenaming) (source target : LocalSlot) : Prop :=
  source.Below mapping.sourceLimit ∧ target = mapping.localSlot source

/-- Extending the allocation map preserves slots already held by a suspended activation. -/
theorem LocalSlot.Renamed.extend {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) {source target : LocalSlot}
    (related : LocalSlot.Renamed earlier source target) : LocalSlot.Renamed later source target :=
  ⟨related.1.mono extension.source source,
    related.2.trans (extension.localSlot source related.1).symm⟩
#print axioms LocalSlot.Renamed.extend

/-- Local setup supports numeric dead declarations before, between or after retained slots. -/
theorem Memory.Renamed.makeLocalsUnmodeled {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceActivation targetActivation : Nat) (scope : scopes sourceActivation targetActivation)
    {indices : LocalIndexMap} {sourceKinds targetKinds : List CIL.LocalKind}
    (selected : indices.Selects Eq sourceKinds targetKinds)
    (ready : ∀ kind ∈ targetKinds, localWidth kind < nativeLimit ∧
      ∀ width writable, kind = .span width writable → (0 < width ∧ width < 2^64)) :
    ∃ later sourceSlots targetSlots sourceOwned targetOwned sourceAfter targetAfter,
      mapping.Extends later ∧
      makeLocals sourceActivation sourceKinds (sourceKinds.map fun _ => .unmodeled) source =
        .ok (sourceSlots, sourceOwned, sourceAfter) ∧
      makeLocals targetActivation targetKinds (targetKinds.map fun _ => .unmodeled) target =
        .ok (targetSlots, targetOwned, targetAfter) ∧
      Memory.Renamed later scopes sourceAfter targetAfter ∧
      indices.Selects (LocalSlot.Renamed later) sourceSlots targetSlots ∧
      OwnedAllocations later sourceOwned targetOwned := by
  induction selected generalizing mapping source target with
  | nil =>
    exact ⟨mapping, [], [], [], [], source, target, .refl mapping, rfl, rfl,
      related, .nil, .nil⟩
  | @keep indices sourceKinds targetKinds sourceKind targetKind kindEqual selected induction =>
    cases kindEqual
    obtain ⟨bounded, spanWidth⟩ := ready sourceKind List.mem_cons_self
    obtain ⟨paired, slot, owned, sourceHome, targetHome, extension, sourceMade,
      targetMade, homes, slotBound, ownedBounds⟩ := related.makeLocalUnmodeled sourceFormed
        targetFormed staticBounds sourceActivation targetActivation scope sourceKind
        bounded spanWidth
    have sourceSetup := makeLocal_setup _ _ _ _ _ _ _ sourceMade
    have targetSetup := makeLocal_setup _ _ _ _ _ _ _ targetMade
    have nextStatic : ∀ binding ∈ sourceHome.staticBindings,
        binding.2.allocation < paired.sourceLimit := by
      intro binding member
      rw [sourceSetup.registry] at member
      exact Nat.lt_of_lt_of_le (staticBounds binding member) extension.source
    obtain ⟨later, sourceSlots, targetSlots, sourceOwned, targetOwned, sourceAfter, targetAfter,
      following, sourceRest, targetRest, remains, slots, ownedRest⟩ :=
      induction homes (sourceSetup.wellFormed sourceFormed) (targetSetup.wellFormed targetFormed)
        nextStatic (fun kind member => ready kind (List.mem_cons_of_mem _ member))
    refine ⟨later, slot :: sourceSlots, paired.localSlot slot :: targetSlots,
      owned ++ sourceOwned, owned.map paired.image ++ targetOwned, sourceAfter, targetAfter,
      extension.trans following, ?_, ?_, remains, ?_, ?_⟩
    · simp only [List.map_cons, makeLocals, sourceMade, sourceRest, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
    · simp only [List.map_cons, makeLocals, targetMade, targetRest, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
    · exact .keep ((show LocalSlot.Renamed paired slot (paired.localSlot slot) from
        ⟨slotBound, rfl⟩).extend following) slots
    · exact ((OwnedAllocations.mapped paired owned ownedBounds).extend following).append ownedRest
  | @skip indices sourceKinds targetKinds kind selected induction =>
    obtain ⟨bounded, spanWidth⟩ := ready kind List.mem_cons_self
    obtain ⟨skipped, slot, owned, home, extension, made, homes, privateOwned⟩ :=
      related.skipLocalUnmodeled targetFormed targetActivation kind bounded spanWidth
    have targetSetup := makeLocal_setup _ _ _ _ _ _ _ made
    have nextStatic : ∀ binding ∈ source.staticBindings,
        binding.2.allocation < skipped.sourceLimit :=
      fun binding member => Nat.lt_of_lt_of_le (staticBounds binding member) extension.source
    obtain ⟨later, sourceSlots, targetSlots, sourceOwned, targetOwned, sourceAfter, targetAfter,
      following, sourceRest, targetRest, remains, slots, ownedRest⟩ :=
      induction homes sourceFormed (targetSetup.wellFormed targetFormed) nextStatic
        (fun other member => ready other (List.mem_cons_of_mem _ member))
    refine ⟨later, sourceSlots, slot :: targetSlots, sourceOwned, owned ++ targetOwned,
      sourceAfter, targetAfter, extension.trans following, sourceRest, ?_, remains,
      .skip slot slots, ?_⟩
    · simp only [List.map_cons, makeLocals, made, targetRest, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · exact ((OwnedAllocations.privateList skipped owned privateOwned).extend following).append
        ownedRest
#print axioms Memory.Renamed.makeLocalsUnmodeled

/-- Actual successful initialization is preserved for every retained declaration. -/
theorem Memory.Renamed.makeLocalsInitialized {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceActivation targetActivation : Nat) (scope : scopes sourceActivation targetActivation)
    {indices : LocalIndexMap} {sourceKinds targetKinds : List CIL.LocalKind}
    {sourceValues targetValues : List CIL.Value}
    (selected : LocalDeclarations indices sourceKinds sourceValues targetKinds targetValues)
    (ready : ∀ kind ∈ targetKinds, localWidth kind < nativeLimit ∧
      ∀ width writable, kind = .span width writable → (0 < width ∧ width < 2^64))
    {sourceSlots : List LocalSlot} {sourceOwned : List AllocationId} {sourceAfter : Memory}
    (made : makeLocals sourceActivation sourceKinds sourceValues source =
      .ok (sourceSlots, sourceOwned, sourceAfter)) :
    ∃ later targetSlots targetOwned targetAfter, mapping.Extends later ∧
      makeLocals targetActivation targetKinds targetValues target =
        .ok (targetSlots, targetOwned, targetAfter) ∧
      Memory.Renamed later scopes sourceAfter targetAfter ∧
      indices.Selects (LocalSlot.Renamed later) sourceSlots targetSlots ∧
      OwnedAllocations later sourceOwned targetOwned := by
  induction selected generalizing mapping source target sourceSlots sourceOwned sourceAfter with
  | nil =>
    cases made
    exact ⟨mapping, [], [], target, .refl mapping, rfl, related, .nil, .nil⟩
  | @keep indices sourceKinds sourceValues targetKinds targetValues kind initial
      selected induction =>
    simp only [makeLocals, Bind.bind, Except.bind] at made
    split at made
    · cases made
    rename_i head sourceMade
    rcases head with ⟨slot, owned, sourceHome⟩
    split at made
    · cases made
    rename_i tail sourceRest
    rcases tail with ⟨slots, other, after⟩
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl, rfl⟩ := made
    obtain ⟨bounded, spanWidth⟩ := ready kind List.mem_cons_self
    obtain ⟨paired, targetHome, extension, targetMade, homes, slotBound, ownedBounds⟩ :=
      related.makeLocalInitialized sourceFormed targetFormed staticBounds sourceActivation
        targetActivation scope kind initial bounded spanWidth sourceMade
    have sourceSetup := makeLocal_setup _ _ _ _ _ _ _ sourceMade
    have targetSetup := makeLocal_setup _ _ _ _ _ _ _ targetMade
    have nextStatic : ∀ binding ∈ sourceHome.staticBindings,
        binding.2.allocation < paired.sourceLimit := by
      intro binding member
      rw [sourceSetup.registry] at member
      exact Nat.lt_of_lt_of_le (staticBounds binding member) extension.source
    obtain ⟨later, targetSlots, targetOwned, targetAfter, following, targetRest,
      remains, renamedSlots, ownedRest⟩ :=
      induction homes (sourceSetup.wellFormed sourceFormed) (targetSetup.wellFormed targetFormed)
        nextStatic (fun kind member => ready kind (List.mem_cons_of_mem _ member)) sourceRest
    refine ⟨later, paired.localSlot slot :: targetSlots, owned.map paired.image ++ targetOwned,
      targetAfter, extension.trans following, ?_, remains, ?_, ?_⟩
    · simp only [makeLocals, targetMade, targetRest, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · exact .keep ((show LocalSlot.Renamed paired slot (paired.localSlot slot) from
        ⟨slotBound, rfl⟩).extend following) renamedSlots
    · exact ((OwnedAllocations.mapped paired owned ownedBounds).extend following).append ownedRest
  | @skip indices sourceKinds sourceValues targetKinds targetValues kind initial fits
      selected induction =>
    obtain ⟨bounded, spanWidth⟩ := ready kind List.mem_cons_self
    obtain ⟨skipped, slot, owned, home, extension, madeHome, homes, privateOwned⟩ :=
      related.skipLocalInitialized targetFormed targetActivation kind initial fits bounded spanWidth
    have targetSetup := makeLocal_setup _ _ _ _ _ _ _ madeHome
    have nextStatic : ∀ binding ∈ source.staticBindings,
        binding.2.allocation < skipped.sourceLimit :=
      fun binding member => Nat.lt_of_lt_of_le (staticBounds binding member) extension.source
    obtain ⟨later, targetSlots, targetOwned, targetAfter, following, targetRest,
      remains, slots, ownedRest⟩ :=
      induction homes sourceFormed (targetSetup.wellFormed targetFormed) nextStatic
        (fun other member => ready other (List.mem_cons_of_mem _ member)) made
    refine ⟨later, slot :: targetSlots, owned ++ targetOwned, targetAfter,
      extension.trans following, ?_, remains, .skip slot slots, ?_⟩
    · simp only [makeLocals, madeHome, targetRest, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · exact ((OwnedAllocations.privateList skipped owned privateOwned).extend following).append
        ownedRest
#print axioms Memory.Renamed.makeLocalsInitialized

end CIL.Safety
