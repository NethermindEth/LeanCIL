import CIL.Safety.ReferenceRenaming
import CIL.Safety.AllocationRenamingSteps
import CIL.Safety.StaticMemory

/-!
# Static field lookup under allocation renaming

Static identities and descriptor bytes stay exact. Cached references are revalidated
through their mapped allocation; first access allocates paired immutable storage.
-/

namespace CIL.Safety

/-- Static registry lookup finds the same field identity with its mapped storage reference. -/
theorem Memory.Renamed.staticLookup {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (identity : Nat) :
    target.staticBindings.find? (fun binding => binding.1 == identity) =
      (source.staticBindings.find? (fun binding => binding.1 == identity)).map
        (fun binding => (binding.1, mapping.reference binding.2)) := by
  rw [related.staticBindings]
  induction source.staticBindings with
  | nil => rfl
  | cons binding rest induction =>
    simp only [List.map_cons, List.find?_cons, Prod.fst]
    split
    · rfl
    · exact induction
#print axioms Memory.Renamed.staticLookup

/-- Cached statics retain exact descriptor-byte validation and immutable storage checks. -/
theorem Memory.Renamed.cachedStatic {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (descriptor : CIL.StaticDescriptor)
    (key : Nat) (reference : Reference) (bound : reference.allocation < mapping.sourceLimit)
    (cached : source.staticBindings.find? (fun binding => binding.1 == descriptor.identity) =
      some (key, reference)) :
    ResultRenamed mapping (fun sourceResult targetResult =>
      Memory.Renamed mapping scopes sourceResult.1 targetResult.1 ∧
      targetResult.2 = mapping.reference sourceResult.2)
      (staticReference descriptor source) (staticReference descriptor target) := by
  unfold CIL.Safety.staticReference
  rw [related.staticLookup descriptor.identity, cached]
  dsimp only [Option.map]
  apply ((related.liveAllocation reference.allocation bound).checkedAt
    (.address reference) descriptor.bytes.length).bind
  intro sourceAllocation targetAllocation allocations
  have immutable := allocations.kind.immutable
  dsimp only [AllocationRenaming.reference]
  rw [← immutable, ← allocations.layout]
  split
  · rename_i valid
    simp only [valid, ite_true]
    apply ((show ResultEquivalent Eq
        (CIL.Safety.read source reference descriptor.bytes.length 1)
        (CIL.Safety.read target (mapping.reference reference) descriptor.bytes.length 1) from by
      rw [related.read reference bound]
      cases CIL.Safety.read source reference descriptor.bytes.length 1 with
      | error fault => exact .error fault
      | ok bytes => exact .ok rfl).checkedAt (.address reference) descriptor.bytes.length).bind
    intro sourceBytes targetBytes equal
    cases equal
    split <;> first | exact .error .invalidState | exact .ok ⟨related, rfl⟩
  · rename_i invalid
    simp only [invalid, ite_false]
    exact .error .invalidState
#print axioms Memory.Renamed.cachedStatic

/-- Static initialization precedes exposure of the readonly view and registry binding. -/
private def initializedStatic (descriptor : CIL.StaticDescriptor) (identity : AllocationId)
    (memory : Memory) : Memory :=
  { memory with
    cells := fun other offset => if other == identity then
      match descriptor.bytes[offset]? with
      | some byte => ⟨byte, true⟩
      | none => ⟨0, false⟩
      else memory.cells other offset
    views := ⟨identity, 0, descriptor.bytes.length, true, false⟩ :: memory.views
    staticBindings := (descriptor.identity, ⟨identity, 0⟩) :: memory.staticBindings }

/-- Initializing corresponding immutable homes preserves exact static contents and authority. -/
private theorem initializedStatic_related {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (descriptor : CIL.StaticDescriptor)
    (identity : AllocationId) (bound : identity < mapping.sourceLimit) :
    Memory.Renamed mapping scopes (initializedStatic descriptor identity source)
      (initializedStatic descriptor (mapping.image identity) target) := by
  have views := related.prependView ⟨identity, 0, descriptor.bytes.length, true, false⟩ bound
  refine ⟨related.sourceLimit, related.targetLimit, related.allocations, ?_, views.permissions,
    ?_, related.stackLimit⟩
  · intro queried queryBound offset
    have identities : mapping.image queried = mapping.image identity ↔ queried = identity :=
      ⟨mapping.injective _ _ queryBound bound, congrArg mapping.image⟩
    simp only [initializedStatic, beq_iff_eq, identities, related.cells queried queryBound]
  · simp only [initializedStatic, List.map_cons, AllocationRenaming.reference]
    exact congrArg (fun bindings => (descriptor.identity, ⟨mapping.image identity, 0⟩) :: bindings)
      related.staticBindings
#print axioms initializedStatic_related

/-- A static cache miss extends the map with fresh immutable storage in both executions. -/
theorem Memory.Renamed.freshStatic {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (descriptor : CIL.StaticDescriptor) (bounded : descriptor.bytes.length < nativeLimit)
    (missing : source.staticBindings.find? (fun binding => binding.1 == descriptor.identity) =
      none) :
    ∃ sourceAfter targetAfter,
      staticReference descriptor source = .ok (sourceAfter, ⟨source.nextIdentity, 0⟩) ∧
      staticReference descriptor target = .ok (targetAfter, ⟨target.nextIdentity, 0⟩) ∧
      Memory.Renamed mapping.allocate scopes sourceAfter targetAfter := by
  let allocation : Allocation :=
    ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩, true, [descriptor.bytes.length]⟩
  have valid : allocation.valid = true := by simp [allocation, Allocation.valid, bounded]
  obtain ⟨sourceAllocated, targetAllocated, sourceMade, targetMade, allocations⟩ :=
    related.allocate sourceFormed targetFormed staticBounds allocation allocation
      (Allocation.Related.refl scopes allocation) valid
  dsimp only [allocation] at sourceMade targetMade
  have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
    change source.nextIdentity < mapping.sourceLimit + 1
    rw [related.sourceLimit]
    exact Nat.lt_succ_self _
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  refine ⟨initializedStatic descriptor source.nextIdentity sourceAllocated,
    initializedStatic descriptor target.nextIdentity targetAllocated, ?_, ?_, ?_⟩
  · simp only [CIL.Safety.staticReference, missing, sourceMade, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure, initializedStatic]
    rfl
  · rw [CIL.Safety.staticReference, related.staticLookup descriptor.identity, missing]
    simp only [Option.map_none, targetMade, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure, initializedStatic]
    rfl
  · simpa only [freshImage] using
      initializedStatic_related allocations descriptor source.nextIdentity freshBound
#print axioms Memory.Renamed.freshStatic

/-- Successful static lookup carries an unchanged or extended allocation map to its result. -/
theorem Memory.Renamed.staticReference {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target sourceAfter : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (descriptor : CIL.StaticDescriptor) (reference : Reference)
    (loaded : staticReference descriptor source = .ok (sourceAfter, reference)) :
    ∃ later targetAfter,
      mapping.Extends later ∧
      staticReference descriptor target = .ok (targetAfter, later.reference reference) ∧
      Memory.Renamed later scopes sourceAfter targetAfter := by
  cases cached : source.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨key, address⟩ := binding
    have bound := staticBounds (key, address) (List.mem_of_find?_eq_some cached)
    have corresponding := related.cachedStatic descriptor key address bound cached
    rw [loaded] at corresponding
    obtain ⟨⟨targetAfter, targetReference⟩, targetLoaded, memories, references⟩ :=
      corresponding.success
    exact ⟨mapping, targetAfter, .refl mapping, references ▸ targetLoaded, memories⟩
  | none =>
    have bounded : descriptor.bytes.length < nativeLimit := by
      by_cases outside : descriptor.bytes.length < nativeLimit
      · exact outside
      simp only [CIL.Safety.staticReference, cached, CIL.Safety.allocate, Allocation.valid,
        outside, decide_false, Bool.false_and, Bool.not_false, ite_true, checkedAt,
        Except.mapError, Bind.bind, Except.bind] at loaded
      cases loaded
    obtain ⟨sourceAllocated, targetAllocated, sourceLoaded, targetLoaded, memories⟩ :=
      related.freshStatic sourceFormed targetFormed staticBounds descriptor bounded cached
    rw [sourceLoaded] at loaded
    cases loaded
    refine ⟨mapping.allocate, targetAllocated, mapping.allocate_extends, ?_, memories⟩
    have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
      rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
    simpa only [AllocationRenaming.reference, freshImage] using targetLoaded
#print axioms Memory.Renamed.staticReference

end CIL.Safety
