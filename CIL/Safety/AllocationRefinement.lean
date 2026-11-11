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
    (statics : initial.StaticBindingsBounded) (literals : initial.LiteralsBounded)
    {fuel method : Nat} {arguments : List Value} {values : List CIL.Value}
    (success : invoke sourceProgram fuel method arguments initial =
      .ok (final, values.map Value.scalar)) :
    ∃ targetFinal, invoke targetProgram fuel method arguments initial =
      .ok (targetFinal, values.map Value.scalar) ∧
      BytesBelow initial.nextIdentity final targetFinal ∧
      SlotsAgreeBelow initial.nextIdentity final targetFinal :=
  invoke_rename_scalars StepRenaming.stepTransport programs formed statics literals success
#print axioms ProgramRenaming.invoke_scalars

/-- A caller-prefix postcondition transfers with exact scalar outputs despite private target homes.
    -/
theorem ProgramRenaming.invoke_confined
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial final : Memory} (formed : initial.WellFormed)
    (statics : initial.StaticBindingsBounded) (literals : initial.LiteralsBounded)
    {fuel method : Nat} {arguments : List Value} {values : List CIL.Value}
    (success : invoke sourceProgram fuel method arguments initial =
      .ok (final, values.map Value.scalar))
    (preserved : MemoryBelow initial.nextIdentity initial final) :
    ∃ targetFinal, invoke targetProgram fuel method arguments initial =
      .ok (targetFinal, values.map Value.scalar) ∧
      MemoryBelow initial.nextIdentity initial targetFinal := by
  obtain ⟨targetFinal, finished, bytes, agree⟩ :=
    programs.invoke_scalars formed statics literals success
  exact ⟨targetFinal, finished, agree.confined bytes formed (Nat.le_refl _) preserved⟩
#print axioms ProgramRenaming.invoke_confined

/-- Named exceptions survive actual paired execution, including nested calls and later allocation.
    -/
theorem ProgramRenaming.raises
    {sourceProgram targetProgram : CIL.Program}
    (programs : ProgramRenaming sourceProgram targetProgram)
    {initial : Memory} (formed : initial.WellFormed) (statics : initial.StaticBindingsBounded)
    (literals : initial.LiteralsBounded) {method : Nat} {arguments : List Value}
    (argumentValues : ValuesValid initial arguments)
    {exception : String} (raised : Raises sourceProgram method arguments initial exception) :
    Raises targetProgram method arguments initial exception :=
  raised.rename StepRenaming.stepTransport programs formed statics literals argumentValues
#print axioms ProgramRenaming.raises

/-- Scalar contracts transfer unchanged when their precondition establishes memory readiness and
    their postcondition observes only the caller prefix of the final memory. -/
theorem MethodContract.Holds.of_allocationRenaming {Input Output : Type}
    {contract : MethodContract Input Output} {sourceProgram targetProgram : CIL.Program}
    {method : Nat} (holds : contract.Holds sourceProgram method)
    (programs : ProgramRenaming sourceProgram targetProgram)
    (ready : ∀ input initial, contract.pre input initial →
      initial.WellFormed ∧ initial.StaticBindingsBounded ∧ initial.LiteralsBounded)
    (scalarResults : ∀ input initial final output, contract.pre input initial →
      contract.post input initial final output →
      ∃ values : List CIL.Value, contract.results output = values.map Value.scalar)
    (stablePost : ∀ input initial sourceFinal targetFinal output,
      contract.pre input initial → BytesBelow initial.nextIdentity sourceFinal targetFinal →
      SlotsAgreeBelow initial.nextIdentity sourceFinal targetFinal →
      initial.nextIdentity ≤ targetFinal.nextIdentity →
      contract.post input initial sourceFinal output →
      contract.post input initial targetFinal output) :
    contract.Holds targetProgram method := by
  intro input initial permitted
  obtain ⟨fuel, ⟨final, values⟩, success, confined, output, encoded, post⟩ :=
    holds input initial permitted
  obtain ⟨scalars, scalarEncoding⟩ := scalarResults input initial final output permitted post
  rw [encoded, scalarEncoding] at success
  obtain ⟨formed, statics, literals⟩ := ready input initial permitted
  obtain ⟨targetFinal, targetSuccess, related, agree⟩ :=
    programs.invoke_scalars formed statics literals success
  have targetGrowth :=
    (invoke_preserves_caller_allocations _ _ _ _ _ _ _ targetSuccess).next
  refine ⟨fuel, (targetFinal, scalars.map Value.scalar), targetSuccess, ?_,
    output, scalarEncoding.symm, stablePost _ _ _ _ _ permitted related agree targetGrowth post⟩
  exact ⟨targetGrowth,
    fun identity bound => (related.allocations identity bound).trans
      (confined.allocations identity bound),
    fun identity bound offset outside => (related.cells identity bound offset).trans
      (confined.cells identity bound offset outside),
    fun identity bound offset => (related.permissions identity bound offset true).trans
      (confined.writable identity bound offset),
    fun identity bound offset outside => (related.permissions identity bound offset false).trans
      (confined.readable identity bound offset outside),
    fun identity bound offset outside => by
      have kept := confined.slots identity bound offset outside
      refine (agree identity bound offset fun reference held => ?_).trans kept
      rw [kept] at held
      exact formed.slots _ _ _ held⟩
#print axioms MethodContract.Holds.of_allocationRenaming

/-- `contract` from the initial memory every caller holds: well-formed, with each static binding
    and string literal naming an issued allocation. `of_allocationRenaming` transfers it whatever
    `contract.pre` says about memory as a whole. -/
def MethodContract.fromReadyMemory {Input Output : Type} (contract : MethodContract Input Output) :
    MethodContract Input Output :=
  { contract with
    pre := fun input initial =>
      initial.WellFormed ∧ initial.StaticBindingsBounded ∧ initial.LiteralsBounded ∧
        contract.pre input initial }

/-- A contract holds from ready memory, since ready memory meets its own precondition. -/
theorem MethodContract.Holds.fromReadyMemory {Input Output : Type}
    {contract : MethodContract Input Output} {program : CIL.Program} {method : Nat}
    (holds : contract.Holds program method) : contract.fromReadyMemory.Holds program method :=
  fun input initial ready => holds input initial ready.2.2.2
#print axioms MethodContract.Holds.fromReadyMemory

end CIL.Safety
