import CIL.Safety.LiveValues
import CIL.Safety.FrameAllocations

/-!
# Frame references are valid

Frame setup (locals and parameter homes) yields slots whose references are
valid in the resulting memory, and `Frame.ReferencesValid` survives any allocation
extension. `LiveState` uses this to keep a frame's references valid across calls.
-/

namespace CIL.Safety

theorem makeLocal_reference_valid (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    slot.ReferencesValid result := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).references hm slot (by simp)

theorem makeLocals_references_valid (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (slots : List LocalSlot)
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    SlotsReferencesValid result slots := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).references hm

theorem makeParameterHomes_references_valid (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    ∀ home ∈ homes, home.2.ReferencesValid result := by
  intro home member
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).references hm home.2
    (List.mem_map.mpr ⟨home, member, rfl⟩)

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
