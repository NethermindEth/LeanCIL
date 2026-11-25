import CIL.Safety.FrameStaticWorld
import CIL.Safety.ExecutionFrameOwnership
import CIL.Safety.StaticLifetime

/-!
# Static data stays valid through execution

`StaticWorldValid` (static bindings and their storage, for the descriptors the program
declares) is preserved by every checked step, every successful run and invocation, and every
memory observed along a run. The descriptors come from the program's own metadata through
`programStaticDescriptors`, so consumers need no separate static-site assumption.
-/

namespace CIL.Safety

/-- Static selection comes from the actual extracted method metadata. -/
def programStaticDescriptors (program : CIL.Program) : List CIL.StaticDescriptor :=
  program.flatMap fun body => body.staticSites.map Prod.snd

theorem program_static_sites_valid (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (found : program[method]? = some body) :
    StaticSitesValid (programStaticDescriptors program) body := by
  intro site member
  apply List.mem_flatMap.mpr
  refine ⟨body, List.mem_of_getElem? found, ?_⟩
  exact List.mem_map.mpr ⟨site, member, rfl⟩

theorem step_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (sites : StaticSitesValid descriptors body)
    (world : StaticWorldValid descriptors m)
    (h : step body operation pc args frame stack m = .ok action) :
    StaticWorldValid descriptors action.memory := by
  have effect := step_effect _ _ _ _ _ _ _ _ h
  generalize action.frameAfter frame = final, action.memory = result at effect ⊢
  cases effect with
  | arrayAllocation effect =>
    apply PreservesImmutable.world (m := m) (result := result) ?_ descriptors world effect.registry
    intro identity allocation present _
    have old := (hm.allocations identity allocation present).1
    exact ⟨(effect.below.allocations identity old).trans present, effect.below.cells identity old,
      fun offset => effect.below.permissions identity old offset false⟩
  | objectAllocation effect =>
    apply PreservesImmutable.world (m := m) (result := result) ?_ descriptors world effect.registry
    intro identity allocation present _
    have old := (hm.allocations identity allocation present).1
    exact ⟨(effect.below.allocations identity old).trans present, effect.below.cells identity old,
      fun offset => effect.below.permissions identity old offset false⟩
  | stackAllocation effect =>
    cases effect with
    | empty => exact world
    | fresh allocated initialized =>
      have ready := allocateHome_preserves_static_world _ _ _ _ _ _ hm world allocated
      rcases initialized with rfl | written
      · exact ready
      · exact write_preserves_static_world _ _ _ _ _ _ ready written
  | memory effect => exact effect.staticWorld descriptors hm sites world
  | store _ stored => exact storeLocal_preserves_static_world _ _ _ _ _ _ world stored
  | valueHome allocated stored =>
    exact storeValue_preserves_static_world _ _ _ _ _
      (allocateHome_preserves_static_world _ _ _ _ _ _ hm world allocated) stored
  | localHome allocated stored =>
    exact storeLocal_preserves_static_world _ _ _ _ _ _
      (allocateHome_preserves_static_world _ _ _ _ _ _ hm world allocated) stored
  | resume => exact world

theorem programStep_preserves_static_world {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (step : ProgramStep program method pc args frame stack m action) (hm : m.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) m) :
    StaticWorldValid (programStaticDescriptors program) action.memory := by
  obtain ⟨body, op, found, _, success⟩ := step
  exact step_preserves_static_world _ _ _ _ _ _ _ _ _ hm
    (program_static_sites_valid _ _ _ found) world success

theorem programStep_preserves_frame_allocations {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (step : ProgramStep program method pc args frame stack m action) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned) :
    FrameAllocations action.memory (action.frameAfter frame).activation
      (action.frameAfter frame).owned := by
  obtain ⟨body, op, _, _, success⟩ := step
  exact step_preserves_frame_allocations _ _ _ _ _ _ _ _ hm owns success

/-- Every run from well-formed memory whose frame owns its allocations, through caught faults,
    calls and frame exits, keeps the program's static world valid in the memory it ends in and
    in both memories a fault leaves. -/
theorem OutcomeTrace.staticWorld {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {memory : Memory}
    {outcome : Except FaultState (Memory × List Value)}
    (trace : OutcomeTrace program fuel method pc args frame stack memory outcome)
    (formed : memory.WellFormed) (owns : FrameAllocations memory frame.activation frame.owned)
    (world : StaticWorldValid (programStaticDescriptors program) memory) :
    OutcomeHolds (StaticWorldValid (programStaticDescriptors program)) outcome := by
  induction trace with
  | exhausted | missing => exact ⟨world, leaveFrame_preserves_static_world _ _ _ owns world⟩
  | faulted _ _ _ recovered =>
    have left := leaveFrame_preserves_static_world _ _ _ owns world
    rcases recover_error_state recovered with rfl | ⟨same, unwound⟩
    · exact ⟨world, left⟩
    · exact ⟨same ▸ world, unwound ▸ left⟩
  | caught _ _ _ recovered _ ih =>
    have kept := recover_ok_frame recovered
    exact ih formed (by rw [kept.1, kept.2.2.1]; exact owns) world
  | next found fetched stepped _ ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
        ⟨_, _, found, fetched, stepped⟩)
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns)
      (programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world)
  | raised found fetched stepped recovered =>
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    have left := leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) updated
    rcases recover_error_state recovered with rfl | ⟨same, unwound⟩
    · exact ⟨updated, left⟩
    · exact ⟨same ▸ updated, unwound ▸ left⟩
  | raiseCaught found fetched stepped recovered _ ih =>
    have kept := recover_ok_frame recovered
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
        ⟨_, _, found, fetched, stepped⟩)
      (by
        rw [kept.1, kept.2.2.1]
        exact programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns)
      (programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world)
  | callMissing found fetched stepped | callUnentered found fetched stepped
  | tailMissing found fetched stepped | tailMismatched found fetched stepped
  | constructMissing found fetched stepped | constructUnentered found fetched stepped =>
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    exact ⟨updated, leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) updated⟩
  | tailUnchecked found fetched stepped | tailUnentered found fetched stepped
  | returnUnchecked found fetched stepped =>
    have left := leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns)
      (programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world)
    exact ⟨left, left⟩
  | returned found fetched stepped =>
    exact leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns)
      (programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world)
  | tailed found fetched stepped _ _ _ enter _ ih =>
    have stepFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
      ⟨_, _, found, fetched, stepped⟩
    have updated := leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns)
      (programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world)
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _
        (leaveFrame_preserves_wellFormed _ _ stepFormed) enter)
      (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _
        (leaveFrame_preserves_wellFormed _ _ stepFormed) updated enter)
  | called found fetched stepped _ enter childTrace _ childIH ih
  | constructed found fetched stepped _ enter childTrace _ _ childIH ih =>
    have stepFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
      ⟨_, _, found, fetched, stepped⟩
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    have childFormed := enterFrame_preserves_wellFormed _ _ _ _ _ stepFormed enter
    exact ih (childTrace.wellFormed childFormed)
      (childTrace.parentFrame stepFormed
        (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) enter)
      (childIH childFormed (enterFrame_owned _ _ _ _ _ enter)
        (enterFrame_preserves_static_world _ _ _ _ _ _ stepFormed updated enter))
  | callFaulted found fetched stepped _ enter childTrace recovered childIH
  | constructFaulted found fetched stepped _ enter childTrace recovered childIH =>
    have stepFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
      ⟨_, _, found, fetched, stepped⟩
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    have childFormed := enterFrame_preserves_wellFormed _ _ _ _ _ stepFormed enter
    have child := childIH childFormed (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _ stepFormed updated enter)
    have parent := childTrace.parentFrame stepFormed
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) enter
    have left := leaveFrame_preserves_static_world _ _ _ parent.2 child.2
    rcases recover_error_state recovered with rfl | ⟨same, unwound⟩
    · exact ⟨child.1, left⟩
    · exact ⟨same ▸ child.2, unwound ▸ left⟩
  | callCaught found fetched stepped _ enter childTrace recovered _ childIH ih
  | constructCaught found fetched stepped _ enter childTrace recovered _ childIH ih =>
    have stepFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
      ⟨_, _, found, fetched, stepped⟩
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    have childFormed := enterFrame_preserves_wellFormed _ _ _ _ _ stepFormed enter
    have parent := childTrace.parentFrame stepFormed
      (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) enter
    have kept := recover_ok_frame recovered
    exact ih (childTrace.wellFormed childFormed).2 (by rw [kept.1, kept.2.2.1]; exact parent.2)
      (childIH childFormed (enterFrame_owned _ _ _ _ _ enter)
        (enterFrame_preserves_static_world _ _ _ _ _ _ stepFormed updated enter)).2
  | constructValued found fetched stepped _ enter childTrace _ childIH
  | constructUnloaded found fetched stepped _ enter childTrace _ childIH =>
    have stepFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
      ⟨_, _, found, fetched, stepped⟩
    have updated := programStep_preserves_static_world ⟨_, _, found, fetched, stepped⟩ formed world
    have childFormed := enterFrame_preserves_wellFormed _ _ _ _ _ stepFormed enter
    have child := childIH childFormed (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _ stepFormed updated enter)
    exact ⟨child, leaveFrame_preserves_static_world _ _ _
      (childTrace.parentFrame stepFormed
        (programStep_preserves_frame_allocations ⟨_, _, found, fetched, stepped⟩ formed owns) enter)
      child⟩

#print axioms OutcomeTrace.staticWorld

theorem run_preserves_static_world (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    StaticWorldValid (programStaticDescriptors program) final := by
  exact (run_ok_trace h).staticWorld hm owns world

theorem invoke_preserves_static_world (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (h : invoke program fuel method args m = .ok (final, values)) :
    StaticWorldValid (programStaticDescriptors program) final := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact run_preserves_static_world _ _ _ _ _ _ _ _ _ _
    (enterFrame_preserves_wellFormed _ _ _ _ _ hm setup)
    (enterFrame_owned _ _ _ _ _ setup)
    (enterFrame_preserves_static_world _ _ _ _ _ _ hm world setup) executed

/-- This invariant holds at actual instruction boundaries, nested calls and
    teardown, even when a later instruction faults. -/
theorem runVisits_preserves_static_world {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (world : StaticWorldValid (programStaticDescriptors program) m) :
    StaticWorldValid (programStaticDescriptors program) observed := by
  induction visit with
  | initial => exact world
  | tailExpired step _ _ _ =>
    exact leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)
  | @tailChild fuel method pc args frame stack m callee arguments updated body child checked
      childFrame childMemory observed step _ _ _ _ enter _ ih =>
    have hw := leaveFrame_preserves_wellFormed frame _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
    have updated := leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _ hw enter)
      (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter)
  | stepped step => exact programStep_preserves_static_world step hm world
  | next step later ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)
  | entered step call lookup enter =>
    exact enterFrame_preserves_static_world _ _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
      (programStep_preserves_static_world step hm world) enter
  | child step call lookup enter later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _ hw enter)
      (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter)
  | callContinue step lookup enter finish later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    have ownership := programStep_preserves_frame_allocations step hm owns
    have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw enter
    have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF finish)
      (child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership enter finish)
      (run_preserves_static_world _ _ _ _ _ _ _ _ _ _ childWF
        (enterFrame_owned _ _ _ _ _ enter) childWorld finish)
  | constructContinue step lookup enter finish load later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    have ownership := programStep_preserves_frame_allocations step hm owns
    have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw enter
    have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF finish)
      (child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership enter finish)
      (run_preserves_static_world _ _ _ _ _ _ _ _ _ _ childWF
        (enterFrame_owned _ _ _ _ _ enter) childWorld finish)
  | expired step =>
    exact leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)

#print axioms program_static_sites_valid
#print axioms step_preserves_static_world
#print axioms run_preserves_static_world
#print axioms invoke_preserves_static_world
#print axioms runVisits_preserves_static_world

end CIL.Safety
