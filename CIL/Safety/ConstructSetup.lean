import CIL.Safety.AggregateHomeValues
import CIL.Safety.Execution

/-!
# Constructor storage setup

The exact checked `step` for `newobj` on an unmanaged struct: it allocates
fresh zeroed, writable, caller-owned storage and passes its address as the constructor's first
argument, leaving all older memory unchanged.
-/

namespace CIL.Safety

/-- Proves that no constructor argument carries unspecified vector bits, the `known` side
    condition of the construct steps, when the arguments are concrete. -/
macro "cil_known_arguments" : tactic =>
  `(tactic| simp [CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified])

/-- Unmanaged constructors receive fresh initialized aggregate storage of any
    positive representable width. -/
theorem step_newAggregate {body : CIL.Method} {pc callee : Nat}
    (size : Fin (2^64)) (positive : 0 < size.val)
    (args arguments rest : List Value) (frame : Frame) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (checked : arguments.mapM (checkedValue memory) = .ok arguments)
    (known : arguments.any Value.hasUnspecified = false := by cil_known_arguments) :
    ∃ temporary updated,
      step body (.newAggregate callee arguments.length size) pc args frame
          (arguments.reverse ++ rest) memory =
        .ok (.construct callee (.reference (.address temporary) :: arguments) rest
          { frame with owned := temporary.allocation :: frame.owned } temporary (.aggregate size)
          updated) ∧
      read updated temporary size 1 = .ok (List.replicate size 0) ∧
      access updated temporary size 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory updated ∧
      temporary.allocation = memory.nextIdentity := by
  obtain ⟨temporary, allocated, updated, home, stored, loaded, writable, preserved, fresh⟩ :=
    allocate_initialized_aggregate memory frame.activation size (List.replicate size 0)
      (by simp) wellFormed
  refine ⟨temporary, updated, ?_, loaded, writable, preserved, fresh⟩
  have nonzero : size ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp [step, observerCount, unspecifiedOperands, known, nonzero, checked, home,
    Nat.not_lt_of_ge (Nat.le_add_right arguments.length rest.length), Bind.bind, Except.bind,
    Pure.pure, Except.pure]

  simp only [Nat.reducePow, BitVec.ofNat_eq_ofNat] at stored
  rw [stored]

#print axioms step_newAggregate

end CIL.Safety
