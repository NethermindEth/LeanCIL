import CIL.Safety.ExecutionTrace
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.StaticMemoryLemmas
namespace CIL.Safety

def FrameAction.memory : FrameAction → Memory
  | .next _ _ _ m | .call _ _ _ m | .construct _ _ _ _ _ _ m | .returned _ m => m

/-- Calls and returns keep the current frame until the run dispatcher acts;
    ordinary steps and constructor allocation supply their updated frame. -/
def FrameAction.frameAfter (action : FrameAction) (current : Frame) : Frame :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ => frame
  | .call _ _ _ _ | .returned _ _ => current

/-- A step's memory and frame changes, with successful primitive operations as
    evidence. Value-stack validity is independent of this effect classification. -/
inductive StepEffect (body : CIL.Method) (frame : Frame) (m : Memory) : Frame → Memory → Prop where
  | memory {result} (effect : StaticInstructionEffect body m result) : StepEffect body frame m frame result
  | store {index slot final value result}
      (found : frame.locals[index]? = some slot)
      (stored : storeLocal m slot value = .ok (final, result)) :
      StepEffect body frame m { frame with locals := frame.locals.set index final } result
  | valueHome {home result r width value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeValue home (.address r) value = .ok result) :
      StepEffect body frame m { frame with owned := r.allocation :: frame.owned } result
  | localHome {home result r width slot final value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeLocal home slot value = .ok (final, result)) :
      StepEffect body frame m { frame with owned := r.allocation :: frame.owned } result

theorem step_effect (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    StepEffect body frame m (action.frameAfter frame) action.memory := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .memory (.ordinary (.unchanged _))
      | solve | exact .store (by assumption) (by assumption)
      | solve | exact .memory (staticInstruction_effect _ _ _ _ _ _ _ (by assumption))
      | solve | exact .memory (.ordinary (instruction_effect _ _ _ _ _ (by assumption)))
      | solve | exact .valueHome (by assumption) (by assumption)
      | solve | exact .localHome (by assumption) (by assumption)
      | cases h
      | split at h

theorem StepEffect.wellFormed {body : CIL.Method} {frame final : Frame} {m result : Memory}
    (effect : StepEffect body frame m final result) (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | memory effect => exact effect.wellFormed hm
  | store _ stored => exact storeLocal_preserves_wellFormed _ _ _ _ _ hm stored
  | valueHome allocated stored =>
    exact storeValue_preserves_wellFormed _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored
  | localHome allocated stored =>
    exact storeLocal_preserves_wellFormed _ _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored

theorem StepEffect.allocations {body : CIL.Method} {frame final : Frame} {m result : Memory}
    (effect : StepEffect body frame m final result) : AllocationExtension m result := by
  cases effect with
  | memory effect => exact effect.allocations
  | store _ stored => exact storeLocal_extends_allocations _ _ _ _ _ stored
  | valueHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans (storeValue_effect _ _ _ _ stored).allocations
  | localHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans (storeLocal_extends_allocations _ _ _ _ _ stored)

theorem step_preserves_wellFormed (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (h : step body operation pc args frame stack m = .ok action) : action.memory.WellFormed := by
  exact (step_effect _ _ _ _ _ _ _ _ h).wellFormed hm

#print axioms step_preserves_wellFormed

theorem programStep_preserves_wellFormed (program : CIL.Program) (method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (hs : ProgramStep program method pc args frame stack m action) :
    action.memory.WellFormed := by
  obtain ⟨body, op, _, _, hs⟩ := hs
  exact step_preserves_wellFormed _ _ _ _ _ _ _ _ hm hs

theorem run_preserves_wellFormed (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    final.WellFormed := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | next step _ ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | returned step _ =>
    exact leaveFrame_preserves_wellFormed _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | call step _ enter _ _ _ childIH ih
  | construct step _ enter _ _ _ _ childIH ih =>
    exact ih (childIH (enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter))

#print axioms run_preserves_wellFormed

theorem invoke_preserves_wellFormed (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (h : invoke program fuel method args m = .ok (final, values)) : final.WellFormed := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
    (enterFrame_preserves_wellFormed _ _ _ _ _ hm setup) executed

#print axioms invoke_preserves_wellFormed
end CIL.Safety
