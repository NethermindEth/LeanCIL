import CIL.Safety.StaticReferences
import CIL.Safety.LocalReferences

namespace CIL.Safety

theorem step_values_valid (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : step body operation pc args frame stack m = .ok action) : action.LiveValues :=
  (step_contract _ _ _ _ _ _ _ _ h).values hm valid

#print axioms step_values_valid

end CIL.Safety
