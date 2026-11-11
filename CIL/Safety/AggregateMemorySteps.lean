import CIL.Safety.InstructionSteps

/-!
# Aggregate memory steps

Aggregate copies use the existing checked snapshots, preserving every initialization flag.
The step equations expose checked reads and writes without unfolding an instruction dispatcher.
-/

namespace CIL.Safety

/-- An aggregate load has the same result as its checked snapshot, including unknown bytes. -/
private theorem aggregate_load_snapshot (memory : Memory) (reference : Reference)
    (width : Nat) :
    (do
      if let .error .uninitialized := dereference memory (.address reference) width 1 then
        loadSnapshot memory (.address reference) (.aggregate width)
      else
        let bytes ← checkedAt (.address reference) width
          (dereference memory (.address reference) width 1)
        pure (.aggregate bytes) : ExecutionResult CIL.Value) =
      loadSnapshot memory (.address reference) (.aggregate width) := by
  unfold dereference loadSnapshot
  cases accessible : access memory reference width 1 false with
  | error fault =>
    cases fault <;> simp [read, readSnapshot, accessible, referenceAt, checkedAt,
      CIL.SnapshotShape.width, Except.mapError, Bind.bind, Except.bind]
  | ok value =>
    simp only [read, readSnapshot, accessible, referenceAt, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure, snapshotValue,
      CIL.SnapshotShape.width, List.all_map, List.map_map, Function.comp_def]
    split <;> simp_all
#print axioms aggregate_load_snapshot

section Equations
variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- Loading an aggregate copies its snapshot without requiring initialized bytes. -/
@[cil_instruction_step high]
theorem step_loadAggregate_address_eq (width : Nat) (reference : Reference)
    (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.reference (.address reference) :: rest)
      memory = do
      let value ← loadSnapshot memory (.address reference) (.aggregate width)
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  rw [step_loadAggregate_eq, ← aggregate_load_snapshot memory reference width]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> first | rfl | simp_all only [ordinaryAccessAlignment, bind_assoc, pure_bind]
#print axioms step_loadAggregate_address_eq

/-- A readonly reference permits the same aggregate snapshot without write authority. -/
@[cil_instruction_step high]
theorem step_loadAggregate_readOnlyAddress_eq (width : Nat) (reference : Reference)
    (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.readOnlyReference (.address reference) :: rest)
      memory = do
      let value ← loadSnapshot memory (.address reference) (.aggregate width)
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  rw [step_loadAggregate_eq, ← aggregate_load_snapshot memory reference width]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> first | rfl | simp_all only [ordinaryAccessAlignment, bind_assoc, pure_bind]
#print axioms step_loadAggregate_readOnlyAddress_eq

/-- A null aggregate source retains the requested width in its fault diagnostic. -/
@[cil_instruction_step high]
theorem step_loadAggregate_null_eq (width : Nat) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.reference .null :: rest) memory =
      .error (.memory .nullDereference .null width) := by
  rw [step_loadAggregate_eq]
  rfl
#print axioms step_loadAggregate_null_eq

/-- A readonly null source reports the same requested aggregate width. -/
@[cil_instruction_step high]
theorem step_loadAggregate_readOnlyNull_eq (width : Nat) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.readOnlyReference .null :: rest) memory =
      .error (.memory .nullDereference .null width) := by
  rw [step_loadAggregate_eq]
  rfl
#print axioms step_loadAggregate_readOnlyNull_eq

/-- An initialized aggregate store checks its width and writes its bytes. -/
@[cil_instruction_step high]
theorem step_storeAggregate_reference_eq (width : Nat) (bytes : List (BitVec 8))
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeAggregate width) pc args frame
      (.scalar (.aggregate bytes) :: .reference reference :: rest) memory =
      if bytes.length != width then .error .invalidState else do
        let address ← referenceAt reference
        let stored ← checkedAt reference width (write memory address bytes 1)
        return .next (pc + 1) rest frame stored := by
  rw [step_storeAggregate_eq]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> first | rfl | simp_all only [ordinaryAccessAlignment, bind_assoc, pure_bind]
#print axioms step_storeAggregate_reference_eq

/-- A snapshot store checks both widths and preserves its initialization flags. -/
@[cil_instruction_step high]
theorem step_storeAggregate_snapshot_eq (width actual : Nat) (bytes : List (BitVec 8 × Bool))
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeAggregate width) pc args frame
      (.scalar (.snapshot (.aggregate actual) bytes) :: .reference reference :: rest) memory =
      if bytes.length != width || actual != width then .error .invalidState else do
        let address ← referenceAt reference
        let stored ← checkedAt reference width (writeSnapshot memory address bytes 1)
        return .next (pc + 1) rest frame stored := by
  rw [step_storeAggregate_eq]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> first | rfl | simp_all only [ordinaryAccessAlignment, bind_assoc, pure_bind]
#print axioms step_storeAggregate_snapshot_eq
end Equations

/-- A checked snapshot read gives the aggregate value with the same initialization mask. -/
theorem loadSnapshot_aggregate_of_readSnapshot {memory : Memory} {reference : Reference}
    {width : Nat} {bytes : List (BitVec 8 × Bool)}
    (loaded : readSnapshot memory reference width 1 = .ok bytes) :
    loadSnapshot memory (.address reference) (.aggregate width) =
      .ok (snapshotValue (.aggregate width) bytes) := by
  simp [loadSnapshot, referenceAt, checkedAt, loaded, CIL.SnapshotShape.width,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms loadSnapshot_aggregate_of_readSnapshot

/-- A checked initialized read gives the plain aggregate with those exact bytes. -/
theorem loadSnapshot_aggregate_of_read {memory : Memory} {reference : Reference}
    {width : Nat} {bytes : List (BitVec 8)}
    (loaded : read memory reference width 1 = .ok bytes) :
    loadSnapshot memory (.address reference) (.aggregate width) = .ok (.aggregate bytes) := by
  rw [← aggregate_load_snapshot]
  simp [dereference, loaded, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
#print axioms loadSnapshot_aggregate_of_read

/-- A snapshot containing unknown bytes stays a snapshot, with the same flags. -/
@[cil_checked] theorem snapshotValue_unknown (shape : CIL.SnapshotShape)
    (bytes : List (BitVec 8 × Bool)) (unknown : bytes.all Prod.snd = false) :
    snapshotValue shape bytes = .snapshot shape bytes := by
  simp [snapshotValue, unknown]
#print axioms snapshotValue_unknown

end CIL.Safety
