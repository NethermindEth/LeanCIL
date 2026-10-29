import CIL.Safety.LoopScaffold
import Examples.Support

/-! Kernel-checked frame and cutpoint generation, including rejected ambiguous scaffolds. -/

namespace Tests.LoopScaffold
open CIL.Safety

/-- A numeric local with a single conditional loop edge. -/
def body : CIL.Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true
  code := [.local 0, .brnonzero 0, .ret] }

bind_entry entry := body with [] from Examples.empty
bind_cutpoint header := body matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with entry.frame

/-- Generated homes come from checked allocation and the cutpoint follows compiled instructions. -/
theorem generated_state :
    entry.frame.locals = [.bytes .word32 entry.home0] ∧
    (header [] entry.memory).pc = 1 := by exact ⟨rfl, rfl⟩
#print axioms generated_state

/-- error: Cutpoint must match exactly one instruction -/
#guard_msgs in
bind_cutpoint absent := body matching (fun _ => false) with entry.frame

/-- error: Cutpoint must match exactly one instruction -/
#guard_msgs in
bind_cutpoint ambiguous := body matching (fun _ => true) with entry.frame

/-- Missing vector arguments cannot supply a frame witness. -/
def missingArgument : CIL.Method := { code := [.ret], locals := [], returnsValue := false, vectorArgs := [0] }

/-- error: Frame entry must reduce to a successful checked allocation -/
#guard_msgs in
bind_entry invalid := missingArgument with [] from Examples.empty

end Tests.LoopScaffold
