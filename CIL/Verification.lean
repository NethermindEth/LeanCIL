import CIL.Safety.Certificate

namespace CIL.Safety

/-- Total correctness relative to the checked CIL semantics. The existential
    fuel must witness normal return; a fault or exhausted bound cannot satisfy it. -/
def Ensures (program : CIL.Program) (method : Nat)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop) : Prop :=
  ∀ args initial, pre args initial →
    ∃ fuel final values, invoke program fuel method args initial = .ok (final, values) ∧
      post args initial final values

/-- The finite execution verification condition, with a caller-selected bound.
    Reducing it exposes instruction, allocation and call obligations directly. -/
def VC (program : CIL.Program) (method fuel : Nat) (args : List Value)
    (initial : Memory) (post : Memory → List Value → Prop) : Prop :=
  ∃ final values, invoke program fuel method args initial = .ok (final, values) ∧ post final values

theorem ensures_of_vc (program : CIL.Program) (method : Nat)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop)
    (bound : List Value → Memory → Nat)
    (verified : ∀ args initial, pre args initial →
      VC program method (bound args initial) args initial (post args initial)) :
    Ensures program method pre post := by
  intro args initial permitted
  obtain ⟨final, values, executed, result⟩ := verified args initial permitted
  exact ⟨bound args initial, final, values, executed, result⟩

#print axioms ensures_of_vc
end CIL.Safety
