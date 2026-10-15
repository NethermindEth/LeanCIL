import CIL.Safety.StepComposition

namespace CIL.Safety

/-- A loop cutpoint includes the checked frame, stack and memory. -/
structure LoopState where
  pc : Nat
  frame : Frame
  stack : List Value
  memory : Memory

def LoopState.run (state : LoopState) (program : CIL.Program) (method : Nat)
    (args : List Value) (fuel : Nat) :=
  Safety.run program fuel method state.pc args state.frame state.stack state.memory

/-- A proved finite segment of actual execution, valid for every continuation budget.
    It cannot hide a fault or replace the loop body by an assumed summary. -/
def LoopSegment (program : CIL.Program) (method : Nat) (args : List Value)
    (source target : LoopState) (cost : Nat) : Prop :=
  ∀ fuel, source.run program method args (fuel + cost) = target.run program method args fuel

def LoopTerminates (program : CIL.Program) (method : Nat) (args : List Value)
    (post : Memory → List Value → Prop) (state : LoopState) : Prop :=
  ∃ fuel final values, state.run program method args fuel = .ok (final, values) ∧ post final values

/-- An invariant and a strictly decreasing natural measure establish a finite,
    successful checked execution. Exit obligations include the desired postcondition.
    No uniform fuel bound or bounded unrolling assumption is required. -/
theorem loop_terminates {α : Type} (program : CIL.Program) (method : Nat) (args : List Value)
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (post : Memory → List Value → Prop)
    (progress : ∀ state, invariant state →
      LoopTerminates program method args post (configuration state) ∨
      ∃ next cost, invariant next ∧ measure next < measure state ∧
        LoopSegment program method args (configuration state) (configuration next) cost)
    (state : α) (valid : invariant state) :
    LoopTerminates program method args post (configuration state) := by
  generalize rank : measure state = n
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
    rcases progress state valid with finished | ⟨next, cost, preserved, decreases, segment⟩
    · exact finished
    · obtain ⟨fuel, final, values, executed, satisfied⟩ :=
        ih (measure next) (by omega) next preserved rfl
      exact ⟨fuel + cost, final, values, (segment fuel).trans executed, satisfied⟩

#print axioms loop_terminates
end CIL.Safety
