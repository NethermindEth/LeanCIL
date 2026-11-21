import CIL.Semantics

/-! The step equation for a CIL return. -/

namespace CIL

/-- A return instruction checks the result without inspecting other instruction families. -/
theorem step_return (narrow : Option NarrowKind) (returns : Bool) (pc : Nat)
    (stack : List Value) (memory : Memory) (profile : FeatureProfile) :
    step .ret returns narrow pc stack memory profile =
      returnFromStack narrow returns stack memory := rfl
#print axioms step_return

end CIL
