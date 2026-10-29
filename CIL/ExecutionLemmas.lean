import CIL.Semantics

/-! Exact equations for the shared feature and return evaluators. -/

namespace CIL

/-- A feature test pushes the profile's answer as `1` or `0`. -/
theorem step_feature (id : Feature) (returns : Bool) (pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) (profile : FeatureProfile) :
    step (.feature id) returns pc args frame stack memory profile =
      some (.next (pc + 1) (.i32 (if profile.evaluate id then 1 else 0) :: stack) memory) :=
  rfl
#print axioms step_feature

/-- A return instruction checks the result without inspecting other instruction families. -/
theorem step_return (narrow : Option NarrowKind) (returns : Bool) (pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (profile : FeatureProfile) :
    step (.ret narrow) returns pc args frame stack memory profile =
      returnFromStack narrow returns stack memory := rfl
#print axioms step_return

end CIL
