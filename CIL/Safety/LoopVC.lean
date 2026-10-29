import CIL.Safety.NumericLocals
import CIL.Safety.LoopAutomation

/-!
# Checked numeric-store verification conditions

A numeric store creates a post-state obligation with its checked step, readback and writable
home available as hypotheses. The rule reuses checked memory progress and preservation; it
does not assume the invariant or decreasing measure that the remaining obligation must prove.
-/

namespace CIL.Safety

/-- A writable numeric home supplies a checked store and reusable post-state facts.
    The continuation must still establish the requested goal for that state. -/
theorem numeric_store_vc {memory : Memory} {reference : Reference} (kind : CIL.LocalKind)
    (value : CIL.Value) (number : Nat) (fits : localNumber kind value = .ok number)
    (writable : access memory reference (localWidth kind) 1 true = .ok ())
    {goal : Prop}
    (continuation : ∀ updated,
      storeLocal memory (.bytes kind reference) (.scalar value) =
        .ok (.bytes kind reference, updated) →
      loadLocal updated (.bytes kind reference) = .ok (.scalar (localResult kind value)) →
      access updated reference (localWidth kind) 1 true = .ok () → goal) : goal := by
  obtain ⟨updated, written, stored, bytes⟩ := store_numeric_local kind value number fits writable
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact continuation updated stored (load_numeric_local kind value number fits bytes)
    (ready.after_write written).access
#print axioms numeric_store_vc

/-- A checked path to the proposed next state leaves precisely preservation and decrease
    obligations for the loop's progress rule. Its instruction budget is inferred. -/
theorem loop_continue_vc {α : Type} {program : CIL.Program} {method : Nat}
    {args : List Value} {configuration : α → LoopState} {invariant : α → Prop}
    {measure : α → Nat} {post : Memory → List Value → Prop} {state next : α}
    (path : LoopReaches program method args (configuration state) (configuration next))
    (preserved : invariant next) (decreases : measure next < measure state) :
    LoopTerminates program method args post (configuration state) ∨
      ∃ next cost, invariant next ∧ measure next < measure state ∧
        LoopSegment program method args (configuration state) (configuration next) cost := by
  obtain ⟨cost, segment⟩ := path
  exact Or.inr ⟨next, cost, preserved, decreases, segment⟩
#print axioms loop_continue_vc

/-- Generate invariant-preservation and measure-decrease goals after checking the path.
    A path that cannot be justified leaves its checked execution obligation unsolved. -/
syntax "cil_loop_continue " term:max " [" term,* "]" : tactic

macro_rules
  | `(tactic| cil_loop_continue $next [$facts,*]) =>
    `(tactic| (
      apply loop_continue_vc (next := $next)
      · cil_loop_steps [$facts,*]))

/-- Generate the post-store obligation and name its memory, checked store, load and authority.
    The numeric encoding is checked by reduction; unsupported stores do not apply. -/
syntax "cil_store_vc " ident ident ident ident " := " term:max term:max " using " term:max : tactic

macro_rules
  | `(tactic| cil_store_vc $updated $stored $loaded $writable := $kind $value using $ready) =>
    `(tactic| (
      apply numeric_store_vc $kind $value _ (by rfl) $ready
      intro $updated $stored $loaded $writable
      simp only [localResult, BitVec.ofNat_eq_ofNat] at $stored $loaded))

end CIL.Safety
