import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.OutcomeContract

/-! A synthetic extraction with the bodies the C# fixture compiles to:
    `Percent(v) => v <= 100 ? v : throw new ArgumentOutOfRangeException(...)`, `Root(v) => Percent(v) + 1`. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Outcomes.Calls::Percent(System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .const32 1, .convI8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 (BitVec.ofInt 32 100), .convI8, .bleu 7, .nop, .nop,
    .throw "System.ArgumentOutOfRangeException", .arg 0, .ret] }
@[cil_code] def program : Program := [method0, method1]
def signatures : List String := [method0Signature, method1Signature]

end Extracted

namespace Tests.OutcomeContract

open CIL.Safety

bind_method root rootBody := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
bind_callee percent percentBody := "System.UInt64 Outcomes.Calls::Percent(System.UInt64)" from rootBody
bind_call percentSite := percent from rootBody

def percentContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 v)]
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"

def rootContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 (v + 1))]
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"

theorem percent_holds : percentContract.Holds Extracted.program percent := by
  rintro v m -
  by_cases within : v ≤ 100
  · have bound : v ≤ 100#64 := within
    simp only [percentContract, within, ite_true]
    refine ⟨10, m, _, ?_, Confined.refl _ m, rfl⟩
    cil_checked_steps [bound]
  · have bound : ¬ v ≤ 100#64 := within
    simp only [percentContract, within, ite_false]
    cil_raise_steps [bound]

/-- Both outcomes come from the callee's contract at its call site; its body is not unfolded. -/
theorem root_holds (percentHolds : percentContract.Holds Extracted.program percent) :
    rootContract.Holds Extracted.program root := by
  rintro v m -
  by_cases within : v ≤ 100
  · simp only [rootContract, within, ite_true]
    cil_contract_steps []
    cil_outcome_call percentHolds v at percentSite []
    · trivial
    · simp only [percentContract, within, ite_true]
    rintro m1 _ - confined rfl
    cil_contract_steps []
    exact ⟨confined, rfl⟩
  · simp only [rootContract, within, ite_false]
    cil_raise_steps []
    cil_outcome_raise percentHolds v at percentSite []
    · trivial
    · simp only [percentContract, within, ite_false]

theorem root_correct : rootContract.Holds Extracted.program root := root_holds percent_holds

#print axioms root_correct

/-! A raised outcome is exactly `.thrown`: no other fault satisfies it at any fuel. -/

@[cil_code] def stuck : CIL.Method := { returnsValue := false, locals := [], code := [.unsupported "fixture"] }
@[cil_code] def spin : CIL.Method := { returnsValue := false, locals := [], code := [.branch 0] }

example (m : Memory) : ¬ Raises [stuck] 0 [] m "System.Exception" := by
  rintro ⟨fuel, fault, ran, thrown⟩
  cases fuel with
  | zero =>
    rw [show invoke [stuck] 0 0 [] m = .error ⟨0, 0, .fuelExhausted⟩ from rfl] at ran
    cases ran; simp at thrown
  | succ fuel =>
    rw [show invoke [stuck] (fuel + 1) 0 [] m = .error ⟨0, 0, .unsupported "Non-memory instruction requires execution adapter"⟩ from rfl] at ran
    cases ran; simp at thrown

theorem spin_exhausts (m : Memory) (frame : Frame) (fuel : Nat) :
    run [spin] fuel 0 0 [] frame [] m = .error ⟨0, 0, .fuelExhausted⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact (show run [spin] (fuel + 1) 0 0 [] frame [] m = run [spin] fuel 0 0 [] frame [] m from rfl).trans ih

example (m : Memory) : ¬ Raises [spin] 0 [] m "System.Exception" := by
  rintro ⟨fuel, fault, ran, thrown⟩
  change run [spin] fuel 0 0 [] _ [] m = _ at ran
  rw [spin_exhausts] at ran
  cases ran
  simp at thrown

end Tests.OutcomeContract
