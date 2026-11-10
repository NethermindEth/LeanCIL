import CIL.Safety.MethodContract
import CIL.Safety.LocalCalls

/-!
# Checked weakest-precondition composition

These fixtures retain symbolic inputs, arbitrary caller memory and actual checked execution.
They exercise structural rules and reject a changed arithmetic result and located faults.
-/

namespace Tests.WeakestPrecondition
open CIL.Safety

/-- A scalar addition body used to check postconditions against the actual instructions. -/
@[cil_code] def addBody : CIL.Method :=
  { locals := [], code := [.arg 0, .arg 1, .add, .ret], returnsValue := true }

/-- A scalar subtraction body with the same argument and return convention. -/
@[cil_code] def subtractBody : CIL.Method :=
  { locals := [], code := [.arg 0, .arg 1, .sub, .ret], returnsValue := true }

/-- Addition terminates with wrapping arithmetic and exactly preserves caller memory. -/
theorem add (memory : Memory) (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [addBody] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left + right))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms add

/-- Subtraction terminates with wrapping arithmetic and exactly preserves caller memory. -/
theorem subtract (memory : Memory) (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [subtractBody] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left - right))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms subtract

/-- Weakening an arithmetic guarantee does not change the execution obligation. -/
theorem add_result (memory : Memory) (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [addBody] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (_, values) => values = [.scalar (.i64 (left + right))]) :=
  (add memory left right).consequence (fun _ result => result.2)

#print axioms add_result

/-- A run over an abstract program obtains its budget from the known body, without a witness. -/
theorem abstract_run {program : CIL.Program} {method : Nat} (memory : Memory) (frame : Frame)
    (found : program[method]? = some addBody) (left right : CIL.W64) :
    ∃ fuel, run program fuel method 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i64 (left + right))]) := by
  cil_checked_steps [found]

#print axioms abstract_run

/-- A prefix composes a suffix with its own budget without arithmetic on either witness. -/
theorem abstract_prefix {program : CIL.Program} {method : Nat} {post : Memory → List Value → Prop}
    (memory : Memory) (frame : Frame) (found : program[method]? = some addBody)
    (left right : CIL.W64)
    (suffix : WP (Execution (fun fuel => run program fuel method 2
      [.scalar (.i64 left), .scalar (.i64 right)] frame
      [.scalar (.i64 right), .scalar (.i64 left)] memory)) (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method 0
      [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory)) (Function.uncurry post) := by
  cil_contract_steps [found] until suffix

#print axioms abstract_prefix

/-- A computation that always faults cannot establish any total postcondition. -/
theorem fault_rejected (fault : LocatedFault) (post : Memory → List Value → Prop) :
    ¬ WP (Execution (fun _ => .error fault)) (Function.uncurry post) := by
  rintro ⟨_, _, executed, _⟩
  cases executed

#print axioms fault_rejected

/-- Weakening a postcondition cannot turn a false result into a proved one. -/
theorem false_post_rejected (execution : Nat → Except LocatedFault (Memory × List Value)) :
    ¬ WP (Execution execution) (fun _ => False) := by
  rintro ⟨_, _, _, impossible⟩
  exact impossible

#print axioms false_post_rejected

/-- Budgets selected separately for each continuation do not give a uniform prefix budget. -/
theorem uniform_budget_required :
    (∀ fuel : Nat, ∃ cost, fuel ≤ cost) ∧
      ¬ WP (fun cost (_ : Unit) => ∀ fuel : Nat, fuel ≤ cost) (fun _ => True) := by
  constructor
  · intro fuel
    exact ⟨fuel, Nat.le_refl _⟩
  · rintro ⟨cost, _, bounded, _⟩
    have impossible := bounded (cost + 1)
    omega

#print axioms uniform_budget_required

/-- An exact loop path preserves every located fault with its original continuation budget. -/
theorem path_faults {program : CIL.Program} {method : Nat} {args : List Value}
    {source target : LoopState} (path : LoopReaches program method args source target) :
    ∃ cost, ∀ fuel fault,
      target.run program method args fuel = .error fault →
      source.run program method args (fuel + cost) = .error fault := by
  obtain ⟨cost, ran⟩ := WP.exact_iff.mp path
  exact ⟨cost, fun fuel _ failed => (ran fuel).trans failed⟩

#print axioms path_faults

/-- A contract with no input requirements still promises a normal checked return. -/
def returnContract : MethodContract Unit where
  args _ := []
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := True

/-- A located missing-argument fault refutes the contract for all fuel budgets. -/
theorem missing_argument_refutes_contract :
    ¬ returnContract.Holds [{ locals := [], code := [.arg 0, .ret], returnsValue := false }] 0 := by
  apply returnContract.not_holds_of_fault (input := ()) (initial := Memory.empty)
    (observed := 1) (fault := ⟨0, 0, .invalidState⟩) trivial (by decide)
  rfl

#print axioms missing_argument_refutes_contract

end Tests.WeakestPrecondition
