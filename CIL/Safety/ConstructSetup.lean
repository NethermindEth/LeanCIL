import CIL.Safety.ArgumentHomeValues
import CIL.Safety.AggregateHomeValues
import CIL.Safety.Execution

namespace CIL.Safety

/-- The actual new-value step allocates initialized caller-owned storage and
    passes its checked address to the constructor. -/
theorem step_newVector256 {body : CIL.Method} {pc callee : Nat}
    (args arguments rest : List Value) (frame : Frame) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (checked : arguments.mapM (checkedValue memory) = .ok arguments)
    (known : arguments.any Value.hasUnspecified = false := by simp [CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]) :
    ∃ temporary updated,
      step body (.newVector256 callee arguments.length) pc args frame (arguments.reverse ++ rest) memory =
        .ok (.construct callee (.reference (.address temporary) :: arguments) rest
          { frame with owned := temporary.allocation :: frame.owned } temporary .vector256 updated) ∧
      read updated temporary 32 1 = .ok (numberBytes 0 32) ∧
      access updated temporary 32 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory updated ∧
      temporary.allocation = memory.nextIdentity := by
  obtain ⟨temporary, allocated, updated, home, stored, _, loaded, writable, preserved⟩ :=
    allocate_initialized256 memory frame.activation (BitVec.ofNat 256 0) wellFormed
  refine ⟨temporary, updated, ?_, loaded, writable, preserved,
    (allocateHome_fresh _ _ _ _ _ home).2.1⟩
  simp [step, observerCount, unspecifiedOperands, known, checked, localWidth, home, stored,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_newVector256

/-- Unmanaged constructors receive fresh initialized aggregate storage of any
    positive representable width, without requiring a vector representation. -/
theorem step_newAggregate {body : CIL.Method} {pc callee : Nat}
    (size : Fin (2^64)) (positive : 0 < size.val)
    (args arguments rest : List Value) (frame : Frame) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (checked : arguments.mapM (checkedValue memory) = .ok arguments)
    (known : arguments.any Value.hasUnspecified = false := by simp [CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]) :
    ∃ temporary updated,
      step body (.newAggregate callee arguments.length size) pc args frame (arguments.reverse ++ rest) memory =
        .ok (.construct callee (.reference (.address temporary) :: arguments) rest
          { frame with owned := temporary.allocation :: frame.owned } temporary (.aggregate size) updated) ∧
      read updated temporary size 1 = .ok (List.replicate size 0) ∧
      access updated temporary size 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory updated ∧
      temporary.allocation = memory.nextIdentity := by
  obtain ⟨temporary, allocated, updated, home, stored, loaded, writable, preserved, fresh⟩ :=
    allocate_initialized_aggregate memory frame.activation size (List.replicate size 0)
      (by simp) wellFormed
  refine ⟨temporary, updated, ?_, loaded, writable, preserved, fresh⟩
  have nonzero : size ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp [step, observerCount, unspecifiedOperands, known, nonzero, checked, home, Nat.not_lt_of_ge (Nat.le_add_right arguments.length rest.length),
    Bind.bind, Except.bind, Pure.pure, Except.pure]

  simp only [Nat.reducePow, BitVec.ofNat_eq_ofNat] at stored
  rw [stored]

#print axioms step_newAggregate

end CIL.Safety
