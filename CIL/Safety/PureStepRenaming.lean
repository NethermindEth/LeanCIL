import CIL.Safety.CheckedValueRenaming
import CIL.Safety.LocalOperandRenaming

/-!
# Pure step computations under allocation renaming

Scalar decoding and arithmetic diagnostics contain no allocation identities.
Their results can therefore be reused exactly while checked references are mapped separately.
-/

namespace CIL.Safety

-- Stack lists are renamed by the local map of the frame that holds them.
variable {indices : LocalIndexMap}

/-- The empty relocation leaves every operand unchanged. -/
theorem LocalIndexMap.operation_nil (operation : CIL.Instruction) :
    LocalIndexMap.nil.operation operation = operation := by cases operation <;> rfl
#print axioms LocalIndexMap.operation_nil

/-- Arithmetic faults and scalar results are independent of allocation identities. -/
theorem ResultRenamed.arithmetic (mapping : AllocationRenaming)
    (result : Except CIL.ArithmeticFault α) :
    ResultRenamed mapping Eq (result.mapError ExecutionFault.arithmetic)
      (result.mapError ExecutionFault.arithmetic) := by
  cases result with
  | error fault => exact .error (.arithmetic fault)
  | ok value => exact .ok rfl
#print axioms ResultRenamed.arithmetic

/-- Intrinsic evaluation preserves scalar results and arithmetic or unsupported diagnostics. -/
theorem AllocationRenaming.checkedIntrinsic (mapping : AllocationRenaming)
    (operation : CIL.Intrinsic) (operands : List CIL.Value) :
    ResultRenamed mapping Eq (checkedIntrinsic operation operands)
      (checkedIntrinsic operation operands) := by
  unfold CIL.Safety.checkedIntrinsic
  repeat first
    | exact .ok rfl
    | exact .error _
    | exact ResultRenamed.arithmetic mapping _
    | split
#print axioms AllocationRenaming.checkedIntrinsic

/-- Scoped type identity has the same result or unsupported fault under every allocation map. -/
theorem AllocationRenaming.runtimeTypeEqual (mapping : AllocationRenaming)
    (left right : CIL.Extraction.TypeExpr) :
    ResultRenamed mapping Eq (CIL.Safety.runtimeTypeEqual left right)
      (CIL.Safety.runtimeTypeEqual left right) := by
  unfold CIL.Safety.runtimeTypeEqual
  split <;> first | exact .ok rfl | exact .error _

#print axioms AllocationRenaming.runtimeTypeEqual

/-- Scalar decoding has the same numeric checks and rejects the same reference shapes. -/
theorem LocalIndexMap.scalarOperands (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (values : List Value) :
    ResultRenamed mapping Eq (CIL.Safety.scalars values)
      (CIL.Safety.scalars (values.map (indices.value mapping))) := by
  rw [indices.scalars mapping]
  induction values with
  | nil => exact .ok rfl
  | cons value rest induction =>
    cases value <;> try exact .error .invalidState
    rename_i scalar
    dsimp only [CIL.Safety.scalars]
    split
    · apply induction.bind
      intro first second same
      subst second
      exact .ok rfl
    · exact .error .invalidState
#print axioms LocalIndexMap.scalarOperands

/-- A list consisting only of scalars has no allocation identities to bound. -/
theorem scalarValues_below (limit : Nat) (values : List CIL.Value) :
    ∀ value ∈ values.map Value.scalar, value.Below limit := by
  intro value member
  obtain ⟨scalar, _, rfl⟩ := List.mem_map.mp member
  trivial
#print axioms scalarValues_below

/-- Checking numeric results preserves their values without introducing allocation identities. -/
theorem Memory.Renamed.scalarChecks {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (values : List CIL.Value) :
    ResultRenamed mapping (fun left right => right = left.map mapping.value)
      ((values.map Value.scalar).mapM (CIL.Safety.checkedValue source))
      ((values.map Value.scalar).mapM (CIL.Safety.checkedValue target)) := by
  simpa only [List.map_map, Function.comp_def, AllocationRenaming.value, LocalIndexMap.value] using
    related.checkedValues (values.map Value.scalar) (scalarValues_below _ values)
#print axioms Memory.Renamed.scalarChecks

end CIL.Safety
