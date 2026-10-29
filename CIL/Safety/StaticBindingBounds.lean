import CIL.Safety.ExecutionInvariants
import CIL.Safety.ExecutionLifetime

/-!
# Allocation bounds for the static binding registry

Frame setup, checked instructions and successful runs preserve the registry's allocated
identity bounds. No static byte contents or descriptor validity are assumed here.
-/

namespace CIL.Safety

/-- Every cached static reference names an identity below the allocation watermark. -/
def Memory.StaticBindingsBounded (memory : Memory) : Prop :=
  ∀ binding ∈ memory.staticBindings, binding.2.allocation < memory.nextIdentity

/-- Unchanged registry entries retain their bounds when the allocation watermark grows. -/
theorem Memory.StaticBindingsBounded.preserve {source target : Memory}
    (bounded : source.StaticBindingsBounded)
    (registry : target.staticBindings = source.staticBindings)
    (watermark : source.nextIdentity ≤ target.nextIdentity) : target.StaticBindingsBounded := by
  intro binding member
  rw [registry] at member
  exact Nat.lt_of_lt_of_le (bounded binding member) watermark
#print axioms Memory.StaticBindingsBounded.preserve

/-- Ordinary allocation does not edit the cached static registry. -/
theorem allocate_staticBindings {source target : Memory} {descriptor : Allocation}
    {identity : AllocationId} (allocated : allocate source descriptor = .ok (identity, target)) :
    target.staticBindings = source.staticBindings := by
  unfold allocate at allocated
  repeat' first | cases allocated | split at allocated
  rfl
#print axioms allocate_staticBindings

/-- A local home adds storage without changing existing static references. -/
theorem allocateHome_staticBindings {source target : Memory} {activation width alignment : Nat}
    {reference : Reference}
    (allocated : allocateHome source activation width alignment = .ok (reference, target)) :
    target.staticBindings = source.staticBindings := by
  unfold allocateHome at allocated
  repeat' first
    | solve | exact allocate_staticBindings (checkedAt_ok (by assumption))
    | solve | exact allocate_staticBindings (by assumption)
    | cases allocated
    | split at allocated
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at allocated
  rename_i pair allocation
  rcases pair with ⟨identity, memory⟩
  change memory.staticBindings = source.staticBindings
  exact allocate_staticBindings (checkedAt_ok allocation)
#print axioms allocateHome_staticBindings

/-- Ordinary memory effects retain all registry bounds. -/
theorem InstructionEffect.staticBindingsBounded {source target : Memory}
    (effect : InstructionEffect source target) (bounded : source.StaticBindingsBounded) :
    target.StaticBindingsBounded := by
  apply bounded.preserve ?_ effect.allocations.next
  cases effect with
  | unchanged => rfl
  | write success => exact write_staticBindings success
  | snapshot success => exact writeSnapshot_staticBindings success
#print axioms InstructionEffect.staticBindingsBounded

/-- Frame-local storage preserves existing registry bounds. -/
theorem allocateHome_staticBindingsBounded {source target : Memory}
    {activation width alignment : Nat} {reference : Reference}
    (bounded : source.StaticBindingsBounded)
    (allocated : allocateHome source activation width alignment = .ok (reference, target)) :
    target.StaticBindingsBounded :=
  bounded.preserve (allocateHome_staticBindings allocated)
    (allocateHome_fresh _ _ _ _ _ allocated).1.next
#print axioms allocateHome_staticBindingsBounded

/-- Resolving a static reference either retains its binding or adds a fresh allocated identity. -/
theorem staticReference_staticBindingsBounded {source target : Memory}
    {descriptor : CIL.StaticDescriptor} {reference : Reference}
    (bounded : source.StaticBindingsBounded)
    (success : staticReference descriptor source = .ok (target, reference)) :
    target.StaticBindingsBounded := by
  cases cached : source.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, address⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ cached success
    exact bounded
  | none =>
    simp only [staticReference, cached] at success
    cases allocated : allocate source
        ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩, true, [descriptor.bytes.length]⟩ <;>
      simp only [allocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at success
    · cases success
    · rename_i pair
      obtain ⟨identity, memory⟩ := pair
      cases success
      have registry := allocate_staticBindings allocated
      have fresh := allocation_identity_fresh _ _ _ _ allocated
      intro binding member
      simp only [List.mem_cons, registry] at member
      rcases member with rfl | member
      · change identity < memory.nextIdentity
        rw [fresh.1, fresh.2]
        exact Nat.lt_succ_self _
      · change binding.2.allocation < memory.nextIdentity
        exact Nat.lt_of_lt_of_le (bounded binding member)
          (allocate_extends_allocations _ _ _ _ allocated).next
#print axioms staticReference_staticBindingsBounded

/-- Static and ordinary memory effects preserve registry bounds without a static-world premise. -/
theorem StaticInstructionEffect.staticBindingsBounded {body : CIL.Method} {source target : Memory}
    (effect : StaticInstructionEffect body source target)
    (bounded : source.StaticBindingsBounded) : target.StaticBindingsBounded := by
  cases effect with
  | ordinary effect => exact effect.staticBindingsBounded bounded
  | reference _ success => exact staticReference_staticBindingsBounded bounded success
#print axioms StaticInstructionEffect.staticBindingsBounded

/-- Dynamic stack storage leaves static references bounded. -/
theorem StackAllocationEffect.staticBindingsBounded {source target : Memory}
    {frame final : Frame} {reference : ManagedReference}
    (effect : StackAllocationEffect source frame reference final target)
    (bounded : source.StaticBindingsBounded) : target.StaticBindingsBounded := by
  cases effect with
  | empty => exact bounded
  | fresh allocated initialized =>
    have retained := allocateHome_staticBindingsBounded bounded allocated
    rcases initialized with rfl | written
    · exact retained
    · exact (InstructionEffect.write written).staticBindingsBounded retained
#print axioms StackAllocationEffect.staticBindingsBounded

/-- Every checked dispatcher effect preserves static allocation bounds. -/
theorem StepEffect.staticBindingsBounded {body : CIL.Method} {source target : Memory}
    {frame final : Frame} (effect : StepEffect body frame source final target)
    (bounded : source.StaticBindingsBounded) : target.StaticBindingsBounded := by
  cases effect with
  | stackAllocation effect => exact effect.staticBindingsBounded bounded
  | memory effect => exact effect.staticBindingsBounded bounded
  | store _ stored =>
    exact bounded.preserve (storeLocal_staticBindings stored)
      (storeLocal_extends_allocations _ _ _ _ _ stored).next
  | valueHome allocated stored =>
    exact (storeValue_effect _ _ _ _ stored).staticBindingsBounded
      (allocateHome_staticBindingsBounded bounded allocated)
  | localHome allocated stored =>
    exact (allocateHome_staticBindingsBounded bounded allocated).preserve
      (storeLocal_staticBindings stored) (storeLocal_extends_allocations _ _ _ _ _ stored).next
#print axioms StepEffect.staticBindingsBounded

/-- Successful frame entry only adds fresh homes and keeps the static registry. -/
theorem enterFrame_staticBindingsBounded {source target : Memory} {body : CIL.Method}
    {arguments : List Value} {frame : Frame} (bounded : source.StaticBindingsBounded)
    (entered : enterFrame body arguments source = .ok (frame, target)) :
    target.StaticBindingsBounded := by
  have setup := enterFrame_setup _ _ _ _ _ entered
  exact bounded.preserve setup.registry setup.fresh.1.next
#print axioms enterFrame_staticBindingsBounded

/-- Expiration changes allocation liveness, not the registry's allocated identity bounds. -/
theorem leaveFrame_staticBindingsBounded {source : Memory} (frame : Frame)
    (bounded : source.StaticBindingsBounded) : (leaveFrame frame source).StaticBindingsBounded := by
  have retained := expireAll_retained_fields frame.owned source
  exact bounded.preserve retained.2.2.1 (Nat.le_of_eq retained.2.2.2.symm)
#print axioms leaveFrame_staticBindingsBounded

/-- Every successful run, including nested calls, keeps cached static identities allocated. -/
theorem run_staticBindingsBounded {program : CIL.Program} {fuel method pc : Nat}
    {arguments stack values : List Value} {frame : Frame} {source target : Memory}
    (bounded : source.StaticBindingsBounded)
    (success : run program fuel method pc arguments frame stack source = .ok (target, values)) :
    target.StaticBindingsBounded := by
  have trace := run_success_trace _ _ _ _ _ _ _ _ _ _ success
  clear success
  induction trace with
  | next step _ induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction ((step_effect _ _ _ _ _ _ _ _ stepped).staticBindingsBounded bounded)
  | returned step _ =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact leaveFrame_staticBindingsBounded _
      ((step_effect _ _ _ _ _ _ _ _ stepped).staticBindingsBounded bounded)
  | tailCall step _ _ _ _ entered _ _ induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction (enterFrame_staticBindingsBounded
      (leaveFrame_staticBindingsBounded _
        ((step_effect _ _ _ _ _ _ _ _ stepped).staticBindingsBounded bounded)) entered)
  | call step _ entered _ _ _ childInduction induction
  | construct step _ entered _ _ _ _ childInduction induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction (childInduction (enterFrame_staticBindingsBounded
      ((step_effect _ _ _ _ _ _ _ _ stepped).staticBindingsBounded bounded) entered))
#print axioms run_staticBindingsBounded

end CIL.Safety
