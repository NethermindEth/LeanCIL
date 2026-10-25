import CIL.Safety.ExecutionRenaming
import CIL.Safety.StepRenaming

/-!
# Checked contract transfer with private local allocations

These entry points instantiate the concrete checked dispatcher. Consumers supply only method
correspondence and initial-memory validity; they do not supply a step-simulation assumption.
-/

namespace CIL.Safety

/-- Numeric results remain exact and both final memories agree on the original caller prefix. -/
theorem ProgramRenaming.invoke_scalars
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial final : Memory} (formed : initial.WellFormed)
    (statics : initial.StaticBindingsBounded) {fuel method : Nat} {arguments : List Value}
    {values : List CIL.Value}
    (success : invoke sourceProgram fuel method arguments initial =
      .ok (final, values.map Value.scalar)) :
    ∃ targetFinal, invoke targetProgram fuel method arguments initial =
      .ok (targetFinal, values.map Value.scalar) ∧
      MemoryBelow initial.nextIdentity final targetFinal :=
  invoke_rename_scalars StepRenaming.stepTransport programs formed statics success
#print axioms ProgramRenaming.invoke_scalars

/-- A caller-prefix postcondition transfers with exact scalar outputs despite private target homes.
    -/
theorem ProgramRenaming.invoke_confined
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial final : Memory} (formed : initial.WellFormed)
    (statics : initial.StaticBindingsBounded) {fuel method : Nat} {arguments : List Value}
    {values : List CIL.Value}
    (success : invoke sourceProgram fuel method arguments initial =
      .ok (final, values.map Value.scalar))
    (preserved : MemoryBelow initial.nextIdentity initial final) :
    ∃ targetFinal, invoke targetProgram fuel method arguments initial =
      .ok (targetFinal, values.map Value.scalar) ∧
      MemoryBelow initial.nextIdentity initial targetFinal := by
  obtain ⟨targetFinal, finished, related⟩ := programs.invoke_scalars formed statics success
  exact ⟨targetFinal, finished, preserved.trans related⟩
#print axioms ProgramRenaming.invoke_confined

/-- Named exceptions survive actual paired execution, including nested calls and later allocation.
    -/
theorem ProgramRenaming.raises
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial : Memory} (formed : initial.WellFormed) (statics : initial.StaticBindingsBounded)
    {method : Nat} {arguments : List Value} (argumentValues : ValuesValid initial arguments)
    {exception : String} (raised : Raises sourceProgram method arguments initial exception) :
    Raises targetProgram method arguments initial exception :=
  raised.rename StepRenaming.stepTransport programs formed statics argumentValues
#print axioms ProgramRenaming.raises

/-- Scalar contracts transfer unchanged when their precondition establishes memory readiness and
    their postcondition observes only the caller prefix of the final memory. -/
theorem MethodContract.Holds.of_allocationRenaming {Input Output : Type}
    {contract : MethodContract Input Output} {sourceProgram targetProgram : CIL.Program}
    {method : Nat} (holds : contract.Holds sourceProgram method)
    (programs : ProgramRenaming sourceProgram targetProgram)
    (ready : ∀ input initial, contract.pre input initial →
      initial.WellFormed ∧ initial.StaticBindingsBounded)
    (scalarResults : ∀ output, ∃ values : List CIL.Value,
      contract.results output = values.map Value.scalar)
    (stablePost : ∀ input initial sourceFinal targetFinal output,
      contract.pre input initial → MemoryBelow initial.nextIdentity sourceFinal targetFinal →
      contract.post input initial sourceFinal output →
      contract.post input initial targetFinal output) :
    contract.Holds targetProgram method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, success, confined, output, encoded, post⟩ :=
    holds input initial permitted
  obtain ⟨scalars, scalarEncoding⟩ := scalarResults output
  rw [encoded, scalarEncoding] at success
  obtain ⟨formed, statics⟩ := ready input initial permitted
  obtain ⟨targetFinal, targetSuccess, related⟩ := programs.invoke_scalars formed statics success
  have targetGrowth :=
    (invoke_preserves_caller_allocations _ _ _ _ _ _ _ targetSuccess).next
  refine ⟨fuel, targetFinal, scalars.map Value.scalar, targetSuccess, ?_,
    output, scalarEncoding.symm, stablePost _ _ _ _ _ permitted related post⟩
  exact ⟨targetGrowth,
    fun identity bound => (related.allocations identity bound).trans
      (confined.allocations identity bound),
    fun identity bound offset outside => (related.cells identity bound offset).trans
      (confined.cells identity bound offset outside),
    fun identity bound offset => (related.permissions identity bound offset true).trans
      (confined.writable identity bound offset),
    fun identity bound offset outside => (related.permissions identity bound offset false).trans
      (confined.readable identity bound offset outside)⟩
#print axioms MethodContract.Holds.of_allocationRenaming

end CIL.Safety
