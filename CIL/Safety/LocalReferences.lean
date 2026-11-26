import CIL.Safety.ExecutionLifetime
import CIL.Safety.FrameAllocations

/-!
# Frame references are valid

Frame setup (locals and parameter homes) yields slots whose references are
valid in the resulting memory, and `Frame.ReferencesValid` survives any allocation
extension. `LiveState` uses this to keep a frame's references valid across calls.
-/

namespace CIL.Safety

theorem makeLocals_references_valid (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (slots : List LocalSlot)
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    SlotsReferencesValid result slots := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).references hm

/-- Every reference held by the frame's local slots is valid in `m`. -/
def Frame.ReferencesValid (m : Memory) (frame : Frame) : Prop :=
  SlotsReferencesValid m frame.locals

theorem enterFrame_references_valid (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (hm : m.WellFormed)
    (h : enterFrame body args m = .ok (frame, result)) : frame.ReferencesValid result := by
  exact (enterFrame_setup _ _ _ _ _ h).references hm

theorem Frame.ReferencesValid.preserve {m result : Memory} {frame : Frame}
    (valid : frame.ReferencesValid m) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    frame.ReferencesValid result :=
  fun slot member => (valid slot member).preserve hm ext

#print axioms allocateHome_reference_valid
#print axioms storeLocal_preserves_reference_validity
#print axioms loadLocal_result_valid
#print axioms makeLocals_references_valid
#print axioms enterFrame_references_valid
#print axioms Frame.ReferencesValid.preserve

end CIL.Safety
