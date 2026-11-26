import CIL.Safety.ExecutionInvariants
import CIL.Safety.FrameOwnership

/-!
# Steps only extend the allocation table

Every successful step yields an `AllocationExtension`: no existing allocation changes its
lifetime or layout, and identities are never reused. `ExecutionLifetime` handles teardown,
which can end an allocation. The watermark predicates `OwnedAbove` record that a frame owns
only allocations made after a given identity, which `ExecutionLifetime` uses to protect a
caller's storage.
-/

namespace CIL.Safety

set_option maxHeartbeats 800000

theorem step_extends_allocations (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    AllocationExtension m action.memory := by
  exact (step_effect _ _ _ _ _ _ _ _ h).allocations

/-- Frame teardown changes lifetime flags, but never recycles an identity. -/
theorem leaveFrame_nextIdentity (frame : Frame) (m : Memory) :
    (leaveFrame frame m).nextIdentity = m.nextIdentity :=
  (expireAll_retained_fields frame.owned m).2.2.2

#print axioms step_extends_allocations

/-- Every allocation the frame owns has an identity at or above `watermark`, so none of them
    existed when the watermark was taken. -/
def Frame.OwnedAbove (frame : Frame) (watermark : Nat) : Prop :=
  ∀ id ∈ frame.owned, watermark ≤ id

/-- `Frame.OwnedAbove` for the frame an action continues in; calls and returns carry no
    frame and impose nothing. -/
def FrameAction.OwnedAbove (action : FrameAction) (watermark : Nat) : Prop :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ | .raise _ _ frame _ =>
    frame.OwnedAbove watermark
  | .call _ _ _ _ | .tailCall _ _ _ | .returned _ _ => True

/-- A step keeps the current frame above a watermark that memory has already passed: any home
    it allocates gets a fresh identity. -/
theorem step_ownedAbove (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (watermark : Nat) (old : frame.OwnedAbove watermark)
    (bound : watermark ≤ m.nextIdentity)
    (h : step body operation pc args frame stack m = .ok action) :
    action.OwnedAbove watermark := by
  have effect := step_effect _ _ _ _ _ _ _ _ h
  have above : (action.frameAfter frame).OwnedAbove watermark := by
    generalize action.frameAfter frame = final, action.memory = result at effect ⊢
    cases effect with
    | stackAllocation effect =>
      cases effect with
      | empty => exact old
      | fresh allocated _ =>
        intro id member
        rcases List.mem_cons.mp member with rfl | member
        · exact (allocateHome_fresh _ _ _ _ _ allocated).2.1 ▸ bound
        · exact old id member
    | arrayAllocation | objectAllocation | memory | store | resume => exact old
    | valueHome allocated _ | localHome allocated _ =>
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact (allocateHome_fresh _ _ _ _ _ allocated).2.1 ▸ bound
      · exact old id member
  cases action <;> first | exact above | trivial

#print axioms step_ownedAbove

end CIL.Safety
