import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.OutcomeContract

/-! A synthetic extraction with the bodies the C# fixture compiles to:
    `Percent(v) => v <= 100 ? v : throw new ArgumentOutOfRangeException(...)`,
    `Strict(v) => Percent(v) == 0 ? throw new ArgumentException(...) : v`, `Root(v) => Strict(v) + 1`. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Outcomes.Calls::Strict(System.UInt64)"
def method2Signature : String := "System.UInt64 Outcomes.Calls::Percent(System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .const32 1, .convI8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 2 1, .brzero 5, .arg 0, .ret, .nop, .nop, .throw "System.ArgumentException"] }
@[cil_code] def method2 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 (BitVec.ofInt 32 100), .convI8, .bleu 7, .nop, .nop,
    .throw "System.ArgumentOutOfRangeException", .arg 0, .ret] }
@[cil_code] def program : Program := [method0, method1, method2]
def signatures : List String := [method0Signature, method1Signature, method2Signature]

end Extracted

namespace Tests.OutcomeContract

open CIL.Safety

bind_method root rootBody := "System.UInt64 Outcomes.Calls::Root(System.UInt64)"
bind_callee strict strictBody := "System.UInt64 Outcomes.Calls::Strict(System.UInt64)" from rootBody
bind_callee percent percentBody := "System.UInt64 Outcomes.Calls::Percent(System.UInt64)" from strictBody
bind_call strictSite := strict from rootBody
bind_call percentSite := percent from strictBody

def percentContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 v)]
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"

def strictRaises (v : CIL.W64) : Option String :=
  if v ≤ 100 then if v = 0 then some "System.ArgumentException" else none
  else some "System.ArgumentOutOfRangeException"

def strictContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 v)]
  raises v _ := strictRaises v

def rootContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 (v + 1))]
  raises v _ := strictRaises v

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

/-- All three outcomes come from `Percent`'s contract; its body is not unfolded. Zero returns
    from the callee and then raises in this caller. -/
theorem strict_holds (percentHolds : percentContract.Holds Extracted.program percent) :
    strictContract.Holds Extracted.program strict := by
  rintro v m -
  by_cases within : v ≤ 100
  · by_cases zero : v = 0
    · subst zero
      simp only [strictContract, strictRaises, within, ↓reduceIte]
      cil_raise_steps []
      cil_outcome_call percentHolds 0 at percentSite []
      · trivial
      · simp only [percentContract, within, ite_true]
      rintro m1 _ - - rfl
      have truth : CIL.truth (.i64 0#64) = some false := rfl
      cil_raise_steps [truth]
    · simp only [strictContract, strictRaises, within, zero, ite_true, ite_false]
      cil_contract_steps []
      cil_outcome_call percentHolds v at percentSite []
      · trivial
      · simp only [percentContract, within, ite_true]
      rintro m1 _ - confined rfl
      have truth : CIL.truth (.i64 v) = some true := by simp [CIL.truth]; exact zero
      cil_contract_steps [truth]
      exact ⟨confined, rfl⟩
  · simp only [strictContract, strictRaises, within, ite_false]
    cil_raise_steps []
    cil_outcome_raise percentHolds v at percentSite []
    · trivial
    · simp only [percentContract, within, ite_false]

/-- `Root` reads `Strict`'s outcome off its contract without restating when it raises. -/
theorem root_holds (strictHolds : strictContract.Holds Extracted.program strict) :
    rootContract.Holds Extracted.program root := by
  rintro v m -
  dsimp only [rootContract]
  cases raised : strictRaises v with
  | some exception =>
    cil_raise_steps []
    cil_outcome_raise strictHolds v at strictSite []
    · trivial
    · exact raised
  | none =>
    cil_contract_steps []
    cil_outcome_call strictHolds v at strictSite []
    · trivial
    · exact raised
    rintro m1 _ - confined rfl
    cil_contract_steps []
    exact ⟨confined, rfl⟩

theorem root_correct : rootContract.Holds Extracted.program root := root_holds (strict_holds percent_holds)

#print axioms root_correct

def rootFormedContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ m := m.WellFormed
  footprint _ := []
  post v _ final values := final.WellFormed ∧ values = [.scalar (.i64 (v + 1))]
  raises v _ := strictRaises v

/-- The call hands back `WellFormed`, so `post` can state it though `strictContract` does not. -/
theorem root_formed (strictHolds : strictContract.Holds Extracted.program strict) :
    rootFormedContract.Holds Extracted.program root := by
  rintro v m formed
  dsimp only [rootFormedContract]
  cases raised : strictRaises v with
  | some exception =>
    cil_raise_steps []
    cil_outcome_raise strictHolds v at strictSite []
    · trivial
    · exact raised
  | none =>
    cil_contract_steps []
    cil_formed_outcome_call strictHolds v at strictSite []
    · trivial
    · exact formed
    · exact raised
    rintro m1 _ - formed1 - confined rfl
    cil_contract_steps []
    exact ⟨confined, formed1, rfl⟩

/-- The raising-after form: zero returns from `Percent` and then raises here. -/
example (percentHolds : percentContract.Holds Extracted.program percent) (m : Memory) (formed : m.WellFormed) :
    Raises Extracted.program strict [.scalar (.i64 0)] m "System.ArgumentException" := by
  cil_raise_steps []
  cil_formed_outcome_call percentHolds 0 at percentSite []
  · trivial
  · exact formed
  · simp only [percentContract]; decide
  rintro m1 _ - - - - rfl
  have truth : CIL.truth (.i64 0#64) = some false := rfl
  cil_raise_steps [truth]

#print axioms root_formed

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
