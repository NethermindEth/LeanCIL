import CIL.Safety.MemoryInstructionRenaming
import CIL.Safety.StaticReferenceRenaming
import CIL.Safety.StaticMemoryLemmas

/-!
# Static instruction simulation under allocation renaming

Extraction-bound static identities stay exact. A first lookup extends the allocation map,
while cached fields and span construction preserve their existing allocation correspondence.
-/

namespace CIL.Safety

/-- Static resolution reports model or memory faults, never a named CLR exception. -/
theorem staticReference_not_thrown (descriptor : CIL.StaticDescriptor) (memory : Memory)
    (exception : String) :
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
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
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
  split at observable
  all_goals try simp only [List.map_cons, AllocationRenaming.value,
    AllocationRenaming.managedReference]
  -- Only the `.staticAddress` and `.staticValue` arms resolve the static site at `pc`.
  any_goals first
    | (rename_i bytes
       cases found : body.staticSites.find? (fun site => site.1 == pc) with
       | none => simp only [found, SuccessOrThrow] at observable
       | some site =>
         obtain ⟨key, descriptor⟩ := site
         simp only [found] at observable ⊢
         by_cases matched : (descriptor.bytes == bytes) = true
         · simp only [matched, ite_true, Bind.bind, Except.bind] at observable ⊢
           cases resolved : CIL.Safety.staticReference descriptor source with
           | error fault =>
             cases fault <;> simp only [resolved, SuccessOrThrow] at observable
             rename_i exception
             exact False.elim (staticReference_not_thrown descriptor source exception resolved)
           | ok result =>
             obtain ⟨sourceAfter, reference⟩ := result
             obtain ⟨later, targetAfter, extension, targetLoaded, memories⟩ :=
               related.staticReference sourceFormed targetFormed staticBounds
                 descriptor reference resolved
             refine ⟨later, extension, ?_⟩
             simp only [resolved, targetLoaded, Bind.bind, Except.bind]
             exact .ok ⟨memories, by
               simp only [List.map_cons, AllocationRenaming.value,
                 AllocationRenaming.managedReference, extension.values stack bounds]⟩
         · simp only [matched, Bool.false_eq_true, ite_false, Bind.bind, Except.bind,
             SuccessOrThrow] at observable)
    | (rename_i bytes
       refine ⟨mapping, .refl mapping, ?_⟩
       cases found : body.staticSites.find? (fun site => site.1 == pc) with
       | none => exact .error _
       | some site =>
         obtain ⟨key, descriptor⟩ := site
         simp only [found] at observable ⊢
         cases flagged : descriptor.opaqueValue
         case false =>
           simp only [Bool.false_eq_true, ite_false]
           repeat first
             | exact .ok ⟨related, rfl⟩
             | exact .error _
             | (split <;> try simp only [Bind.bind, Except.bind])
         simp only [flagged, ite_true] at observable ⊢
         split
         case isFalse => exact .error _
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
         split <;> first | exact .ok ⟨memories, rfl⟩ | exact .error _)
    | fail "not a static-site arm"
  -- Only the fallback arm keeps `operation`, with `.staticAddress` excluded.
  any_goals first
    | (have excludesAddress : ∀ bytes, operation = .staticAddress bytes → False := by assumption
       clear excludesAddress
       refine ⟨mapping, .refl mapping, ?_⟩
       cases operation <;> first
         | exact related.memoryInstructionResult _ sourceFormed _ bounds observable
         | (unfold CIL.Safety.memoryInstruction at observable
            repeat' first
              | contradiction
              | cases observable
              | split at observable
              | simp only [Bind.bind, Except.bind, SuccessOrThrow] at observable))
    | fail "not the fallback arm"
  all_goals refine ⟨mapping, .refl mapping, ?_⟩
  all_goals try exact related.memoryInstructionResult _ sourceFormed _ bounds observable
  all_goals simp only [List.mem_cons, forall_eq_or_imp, Value.Below,
    ManagedReference.Below] at bounds
  all_goals repeat' rcases bounds with ⟨_, bounds⟩
  all_goals repeat first
    | exact .ok ⟨related, rfl⟩
    | exact .error _
    | (apply ((related.liveAllocation _ (by assumption)).checkedAt _ _).bindWithSuccess
       intro first second sourceStep descriptors
       rw [← descriptors.layout, ← descriptors.kind.immutable]
       try (unfold staticSpanAligned; rw [← descriptors.layout]))
    | (apply (related.formValue _ (by assumption)).bindWithSuccess
       intro first second sourceStep same
       subst second)
    | dsimp +instances only [AllocationRenaming.reference]
    | (split <;> try simp only [*, Bind.bind, Except.bind])

#print axioms Memory.Renamed.staticInstructionResult

end CIL.Safety
