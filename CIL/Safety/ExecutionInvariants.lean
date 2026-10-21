import CIL.Safety.ExecutionTrace
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.StaticMemoryLemmas
namespace CIL.Safety

def FrameAction.memory : FrameAction → Memory
  | .next _ _ _ m | .call _ _ _ m | .construct _ _ _ _ _ _ m | .returned _ m => m

theorem step_preserves_wellFormed (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (h : step body operation pc args frame stack m = .ok action) : action.memory.WellFormed := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact hm
      | solve | apply storeLocal_preserves_wellFormed _ _ _ _ _ hm; assumption
      | solve | apply staticInstruction_preserves_wellFormed _ _ _ _ _ _ _ hm; assumption
      | solve | apply instruction_preserves_wellFormed _ _ _ _ _ hm; assumption
      | solve |
          apply storeValue_preserves_wellFormed
          · apply allocateHome_preserves_wellFormed _ _ _ _ _ hm; assumption
          · assumption
      | solve |
          apply storeLocal_preserves_wellFormed
          · apply allocateHome_preserves_wellFormed _ _ _ _ _ hm; assumption
          · assumption
      | cases h
      | split at h

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
