import CIL.Safety.Certificate
import CIL.Safety.Loops

/-!
# Total correctness

Hoare-style statements over the checked interpreter `CIL.Safety.invoke`. `Ensures` is the
specification a proof establishes; `VC` is the bounded obligation that reduces by stepping,
and `ensures_of_vc` and `ensures_of_loop` turn bounded or loop proofs into `Ensures`.
-/

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
  ∃ final values, invoke program fuel method args initial = .ok (final, values) ∧
    post final values

/-- A verification condition for every admitted input, with a fuel bound chosen per input,
    establishes total correctness. -/
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

/-- Lift a loop termination proof through checked invocation setup to total correctness. -/
theorem ensures_of_loop (program : CIL.Program) (method : Nat)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop)
    (verified : ∀ args initial, pre args initial →
      ∃ body frame entered,
        program[method]? = some body ∧
        args.mapM (checkedValue initial) = .ok args ∧
        enterFrame body args initial = .ok (frame, entered) ∧
        LoopTerminates program method args (post args initial) ⟨0, frame, [], entered⟩) :
    Ensures program method pre post := by
  intro args initial permitted
  obtain ⟨body, frame, entered, found, checked, setup, fuel, final, values, executed,
    satisfied⟩ := verified args initial permitted
  exact ⟨fuel, final, values, invoke_of_run found checked setup executed, satisfied⟩

#print axioms ensures_of_loop
end CIL.Safety
