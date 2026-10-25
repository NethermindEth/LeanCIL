import CIL.Safety.MethodContract
import CIL.Safety.Certificate

/-! Contract stepping composes opaque child invocations with independent fuel. -/
namespace Tests.ContractCalls
open CIL CIL.Safety

/-- The caller has no access to the helper body. -/
@[cil_code] def caller : Method := {
  returnsValue := true, locals := [], code := [.call 1 0, .ret] }

/-- A separately proved child run supplies the result without unfolding the helper. -/
theorem child_exists (program : Program) (memory final : Safety.Memory) (value : W32)
    (found : program[0]? = some caller)
    (child : ∃ fuel, Safety.invoke program fuel 1 [] memory =
      .ok (final, [.scalar (.i32 value)])) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        result = final ∧ returned = [.scalar (.i32 value)] := by
  cil_contract_steps [found, child]
  exact ⟨rfl, rfl⟩
#print axioms child_exists

/-- A certificate is also sufficient; its additional lifetime facts remain available. -/
theorem child_certificate (program : Program) (memory final : Safety.Memory) (value : W32)
    (fuel : Nat) (found : program[0]? = some caller)
    (child : InvocationCertificate program 1 [] memory fuel final [.scalar (.i32 value)]) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        result = final ∧ returned = [.scalar (.i32 value)] := by
  cil_contract_steps [found, child]
  exact ⟨rfl, rfl⟩
#print axioms child_certificate

/-- Fixed child fuel is independent of the fuel selected for the caller. -/
theorem child_fixed (program : Program) (memory final : Safety.Memory) (value : W32)
    (fuel : Nat) (found : program[0]? = some caller)
    (child : Safety.invoke program fuel 1 [] memory = .ok (final, [.scalar (.i32 value)])) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        result = final ∧ returned = [.scalar (.i32 value)] := by
  cil_contract_steps [found, child]
  exact ⟨rfl, rfl⟩
#print axioms child_fixed

/-- Exact-fuel stepping reuses a matching child proof without discovering its body. -/
theorem checked_child (program : Program) (memory final : Safety.Memory) (value : W32)
    (found : program[0]? = some caller)
    (child : Safety.invoke program 2 1 [] memory = .ok (final, [.scalar (.i32 value)])) :
    Safety.run program 3 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
      .ok (final, [.scalar (.i32 value)]) := by
  cil_checked_steps [found, child]
#print axioms checked_child

/-- A proof at a larger child budget cannot justify a smaller fixed caller budget. -/
theorem insufficient_fuel (program : Program) (memory final : Safety.Memory) (value : W32)
    (child : Safety.invoke program 9 1 [] memory = .ok (final, [.scalar (.i32 value)]))
    (remaining : Safety.invoke program 2 1 [] memory =
      .ok (final, [.scalar (.i32 value)])) :
    Safety.invoke program 2 1 [] memory = .ok (final, [.scalar (.i32 value)]) := by
  fail_if_success (clear remaining; cil_checked_child [child])
  exact remaining
#print axioms insufficient_fuel

/-- Evidence for another callee cannot discharge the fetched call. -/
theorem wrong_callee (program : Program) (memory final : Safety.Memory) (value : W32)
    (found : program[0]? = some caller)
    (wrong : ∃ fuel, Safety.invoke program fuel 2 [] memory =
      .ok (final, [.scalar (.i32 value)]))
    (remaining : ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        result = final ∧ returned = [.scalar (.i32 value)]) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        result = final ∧ returned = [.scalar (.i32 value)] := by
  fail_if_success cil_contract_step [found, wrong]
  exact remaining
#print axioms wrong_callee

/-- The helper's public interface exposes only its scalar result. -/
def seven : MethodContract Unit W32 where
  args _ := []
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post _ _ _ value := value = 7

/-- A caller consumes the contract without a helper body or instruction budget. -/
theorem supplied_contract (program : Program) (memory : Safety.Memory)
    (found : program[0]? = some caller) (holds : seven.Holds program 1) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        returned = [.scalar (.i32 7)] := by
  cil_contract_steps [found, holds, seven]
  simp_all [seven]
#print axioms supplied_contract

/-- A concrete helper used only to establish its registered public contract. -/
@[cil_code] def helper : Method := {
  returnsValue := true, locals := [], code := [.const32 7, .ret] }

/-- A method binding fixes the callee index used by the registered theorem. -/
@[cil_code] def boundProgram : Program := [caller, helper]

/-- Registration retains a checked theorem, not an unchecked interface adapter. -/
@[cil_contract] theorem registered_seven : seven.Holds boundProgram 1 := by
  intro input memory _
  refine ⟨3, memory, [.scalar (.i32 7)], ?_, Confined.refl _ memory, 7, rfl, rfl⟩
  cil_checked_steps [seven]
#print axioms registered_seven

/-- Registration supplies the callee contract without an explicit holds fact. -/
theorem registered_caller (memory : Safety.Memory) :
    ∃ fuel result returned,
      Safety.run boundProgram fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)] := by
  cil_contract_steps [seven]
  simp_all [seven]
#print axioms registered_caller

/-- A caller forwards two scalar arguments to a separately contracted helper. -/
@[cil_code] def pairCaller : Method := {
  returnsValue := true, locals := [], code := [.arg 0, .arg 1, .call 1 2, .ret] }

/-- A tuple input exposes both argument inference and a nontrivial precondition. -/
def orderedPair : MethodContract (W32 × W32) W32 where
  args input := [.scalar (.i32 input.1), .scalar (.i32 input.2)]
  results value := [.scalar (.i32 value)]
  pre input _ := input.1 < input.2
  footprint _ := []
  post input _ _ value := value = input.1 + input.2

/-- Tuple fields are inferred from the actual call arguments and supplied facts prove pre. -/
theorem tuple_input (program : Program) (memory : Safety.Memory) (left right : W32)
    (found : program[0]? = some pairCaller) (holds : orderedPair.Holds program 1)
    (ordered : left < right) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [.scalar (.i32 left), .scalar (.i32 right)]
        ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        returned = [.scalar (.i32 (left + right))] := by
  cil_contract_steps [found, holds, orderedPair, ordered]
  simp_all [orderedPair]
#print axioms tuple_input

/-- A missing precondition stays an obligation before the already-prepared continuation. -/
theorem explicit_precondition (program : Program) (memory : Safety.Memory) (left right : W32)
    (found : program[0]? = some pairCaller) (holds : orderedPair.Holds program 1)
    (later : Unit → left < right) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [.scalar (.i32 left), .scalar (.i32 right)]
        ⟨0, [], [], [], 0⟩ [] memory = .ok (result, returned) ∧
        returned = [.scalar (.i32 (left + right))] := by
  cil_contract_steps [found, holds, orderedPair]
  · change left < right
    exact later ()
  · cil_contract_steps [found, orderedPair]
    simp_all [orderedPair]
#print axioms explicit_precondition

/-- A registered interface may depend on an explicitly checked method binding. -/
@[cil_contract] theorem bound_seven (program : Program)
    (found : program[1]? = some helper) : seven.Holds program 1 := by
  intro input memory _
  refine ⟨3, memory, [.scalar (.i32 7)], ?_, Confined.refl _ memory, 7, rfl, rfl⟩
  cil_checked_steps [found, seven]
#print axioms bound_seven

/-- The registry instantiates program parameters and proves the required callee binding. -/
theorem parameterized_registration (program : Program) (memory : Safety.Memory)
    (found : program[0]? = some caller) (helperFound : program[1]? = some helper) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)] := by
  cil_contract_steps [found, helperFound, seven]
  simp_all [seven]
#print axioms parameterized_registration

/-- Automatic call composition preserves an unrelated sibling obligation. -/
theorem sibling_goal (memory : Safety.Memory) :
    (∃ fuel result returned,
      Safety.run boundProgram fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)]) ∧ (7 : Nat) = 7 := by
  constructor
  cil_contract_steps [seven]
  · simp_all [seven]
  · rfl
#print axioms sibling_goal

/-- A registered theorem cannot be used without proving its callee-binding premise. -/
theorem missing_binding (program : Program) (memory : Safety.Memory)
    (found : program[0]? = some caller)
    (remaining : ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)]) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)] := by
  fail_if_success cil_contract_step [found, seven]
  exact remaining
#print axioms missing_binding

/-- Malformed evidence fails cleanly, allowing the independently proved invocation fallback. -/
theorem malformed_candidate (program : Program) (memory final : Safety.Memory) (value : W32)
    (child : Safety.invoke program 2 1 [] memory = .ok (final, [.scalar (.i32 value)])) :
    Safety.invoke program 2 1 [] memory = .ok (final, [.scalar (.i32 value)]) := by
  cil_checked_child [(by exact False.elim (by assumption)), child]
#print axioms malformed_candidate

/-- A specification-only field cannot be guessed from an empty runtime argument list. -/
structure GhostInput where
  witness : Nat

/-- The unused specification field deliberately cannot be inferred from this interface. -/
def ghostContract : MethodContract GhostInput W32 where
  args _ := []
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post _ _ _ value := value = 7

/-- Ambiguous inputs reject automatic selection without leaking an unassigned metavariable. -/
theorem ambiguous_input (program : Program) (memory : Safety.Memory)
    (found : program[0]? = some caller) (holds : ghostContract.Holds program 1)
    (remaining : ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)]) :
    ∃ fuel result returned,
      Safety.run program fuel 0 0 [] ⟨0, [], [], [], 0⟩ [] memory =
        .ok (result, returned) ∧ returned = [.scalar (.i32 7)] := by
  fail_if_success cil_contract_step [found, holds, ghostContract]
  exact remaining
#print axioms ambiguous_input
end Tests.ContractCalls
