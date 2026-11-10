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
    WP (fun fuel => invoke [addBody] fuel 0 [.scalar (.i64 left), .scalar (.i64 right)] memory)
      (fun final values => final = memory ∧ values = [.scalar (.i64 (left + right))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms add

/-- Subtraction terminates with wrapping arithmetic and exactly preserves caller memory. -/
theorem subtract (memory : Memory) (left right : CIL.W64) :
    WP (fun fuel => invoke [subtractBody] fuel 0 [.scalar (.i64 left), .scalar (.i64 right)] memory)
      (fun final values => final = memory ∧ values = [.scalar (.i64 (left - right))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms subtract

/-- Weakening an arithmetic guarantee does not change the execution obligation. -/
theorem add_result (memory : Memory) (left right : CIL.W64) :
    WP (fun fuel => invoke [addBody] fuel 0 [.scalar (.i64 left), .scalar (.i64 right)] memory)
      (fun _ values => values = [.scalar (.i64 (left + right))]) :=
  (add memory left right).consequence (fun _ _ result => result.2)

#print axioms add_result

/-- A computation that always faults cannot establish any total postcondition. -/
theorem fault_rejected (fault : LocatedFault) (post : Memory → List Value → Prop) :
    ¬ WP (fun _ => .error fault) post := by
  rintro ⟨_, _, _, executed, _⟩
  cases executed

#print axioms fault_rejected

/-- Weakening a postcondition cannot turn a false result into a proved one. -/
theorem false_post_rejected (execution : Nat → Except LocatedFault (Memory × List Value)) :
    ¬ WP execution (fun _ _ => False) := by
  rintro ⟨_, _, _, _, impossible⟩
  exact impossible

#print axioms false_post_rejected

end Tests.WeakestPrecondition
