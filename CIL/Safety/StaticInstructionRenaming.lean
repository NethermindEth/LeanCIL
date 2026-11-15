import CIL.Safety.MemoryInstructionRenaming
import CIL.Safety.StaticReferenceRenaming
import CIL.Safety.StaticMemoryLemmas

/-!
# Static instruction simulation under allocation renaming

Extraction-bound static identities stay exact. A first lookup extends the allocation map,
while cached fields preserve their existing allocation correspondence.
-/

namespace CIL.Safety

/-- Static resolution reports model or memory faults, never a named CLR exception. -/
theorem staticReference_not_thrown (descriptor : CIL.StaticDescriptor) (memory : Memory)
    (exception : ExceptionType) :
    staticReference descriptor memory ≠ .error (.thrown exception) := by
  intro raised
  unfold staticReference at raised
  repeat' first
    | cases raised
    | split at raised
    | simp only [checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        at raised
  all_goals rename_i found
  all_goals split at found <;> cases found
#print axioms staticReference_not_thrown

/-- Static operations preserve successful values or named throws with an extended allocation map. -/
theorem Memory.Renamed.staticInstructionResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed)
    (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp) (stack : List Value)
    (bounds : ∀ value ∈ stack, value.Below mapping.sourceLimit)
    (observable : SuccessOrThrow (staticInstruction body pc operation stack source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later
        (fun left right => Memory.Renamed later scopes left.1 right.1 ∧
          right.2 = left.2.map later.value)
        (staticInstruction body pc operation stack source)
        (staticInstruction body pc operation (stack.map mapping.value) target) := by
  unfold CIL.Safety.staticInstruction at observable ⊢
  exact ⟨mapping, .refl mapping, related.memoryInstructionResult _ sourceFormed _ bounds observable⟩

#print axioms Memory.Renamed.staticInstructionResult

/-- `ldsfld` allocates nothing, so it keeps the allocation map and renames its value with it. -/
theorem Memory.Renamed.staticLoadResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (body : CIL.Method) (pc : Nat) :
    ResultRenamed mapping
      (fun left right => Memory.Renamed mapping scopes left.1 right.1 ∧
        right.2 = mapping.value left.2)
      (staticLoad body pc source) (staticLoad body pc target) := by
  unfold CIL.Safety.staticLoad
  cases found : body.staticAt pc with
  | none => exact .error _
  | some descriptor =>
    simp only
    cases flagged : descriptor.opaqueValue
    case false =>
      simp only [Bool.false_eq_true, ite_false]
      repeat first
        | exact .ok ⟨related, rfl⟩
        | exact .error _
        | (split <;> try simp only [Bind.bind, Except.bind])
    simp only [ite_true]
    cases cached : source.staticBindings.find?
        (fun binding => binding.1 == descriptor.identity)
    case none =>
      simp only [CIL.Safety.staticReference, related.staticLookup descriptor.identity, cached,
        Option.map_none, flagged, ite_true, Bind.bind, Except.bind]
      exact .error _
    rename_i binding
    obtain ⟨name, address⟩ := binding
    have bound := staticBounds (name, address) (List.mem_of_find?_eq_some cached)
    apply (related.cachedStatic descriptor name address bound cached).bindWithSuccess
    intro sourceResult targetResult sourceLoaded paired
    obtain ⟨sourceAfter, sourceReference⟩ := sourceResult
    obtain ⟨targetAfter, targetReference⟩ := targetResult
    obtain ⟨memories, rfl⟩ := paired
    obtain ⟨rfl, rfl, _⟩ := cached_static_reference_checked _ _ _ _ _ _ cached sourceLoaded
    dsimp only
    rw [memories.read sourceReference bound]
    apply ((ResultEquivalent.eq_refl _).checkedAt (.address sourceReference) _).bind
    intro loaded other same
    subst same
    split <;> first | exact .ok ⟨memories, rfl⟩ | exact .error _

#print axioms Memory.Renamed.staticLoadResult

/-- `ldsflda` and a field `ldtoken` extend the allocation map only when they allocate the
    field's storage, and rename the reference they push with it. -/
theorem Memory.Renamed.staticAddressResult {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (body : CIL.Method) (pc : Nat) (observable : SuccessOrThrow (staticAddress body pc source)) :
    ∃ later, mapping.Extends later ∧
      ResultRenamed later
        (fun left right => Memory.Renamed later scopes left.1 right.1 ∧
          right.2 = later.value left.2)
        (staticAddress body pc source) (staticAddress body pc target) := by
  unfold CIL.Safety.staticAddress at observable ⊢
  cases found : body.staticAt pc with
  | none => exact ⟨mapping, .refl mapping, .error _⟩
  | some descriptor =>
    simp only [found, Bind.bind, Except.bind] at observable ⊢
    cases resolved : CIL.Safety.staticReference descriptor source with
    | error fault =>
      cases fault <;> simp only [resolved, SuccessOrThrow] at observable
      rename_i exception
      exact False.elim (staticReference_not_thrown descriptor source exception resolved)
    | ok result =>
      obtain ⟨sourceAfter, reference⟩ := result
      obtain ⟨later, targetAfter, extension, targetLoaded, memories⟩ :=
        related.staticReference sourceFormed targetFormed staticBounds descriptor reference
          resolved
      refine ⟨later, extension, ?_⟩
      simp only [targetLoaded]
      exact .ok ⟨memories, by
        simp only [AllocationRenaming.value, AllocationRenaming.managedReference]⟩

#print axioms Memory.Renamed.staticAddressResult

end CIL.Safety
