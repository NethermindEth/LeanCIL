import CIL.Runtime.ProgramEntry
import CIL.Safety.RuntimeExceptions

/-! CLR contracts over methods of a checked package after ordinary image initialization. -/

namespace CIL.Safety.OutcomeContract
open CIL.Extraction

/-- Restrict the contract's precondition to the memory prepared by the image loader. -/
def atStartup {Input Output} (c : OutcomeContract Input Output) (loaded : Memory) :
    OutcomeContract Input Output :=
  { c with pre := fun input initial => initial = loaded ∧ c.pre input initial }

/-- Every completion of the declared methods satisfies the CLR contract from package startup. -/
def HoldsAtEntryCLR {Input Output} (c : OutcomeContract Input Output)
    (program : Program) (method : Nat) {rawLayouts layouts pins platform evidence imports}
    (certificate : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (target : RuntimeTarget) : Prop :=
  ∃ image loaded, certificate.entry target = some image ∧ image.initialMemory = .ok loaded ∧
    method < program.length ∧ ∀ tail : Program,
      (c.atStartup loaded).HoldsCLR (image.methods ++ tail) method

/-- Every completion admits a concrete counterexample from the same ordinary startup state. -/
def RefutedAtEntryCLR {Input Output} (c : OutcomeContract Input Output)
    (program : Program) (method : Nat) {rawLayouts layouts pins platform evidence imports}
    (certificate : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (target : RuntimeTarget) : Prop :=
  ∃ image loaded, certificate.entry target = some image ∧ image.initialMemory = .ok loaded ∧
    method < program.length ∧ ∀ tail : Program,
      (c.atStartup loaded).RefutedCLR (image.methods ++ tail) method

/-- The image and its startup state are uniquely determined by the package and target. -/
theorem RefutedAtEntryCLR.not_holds {c : OutcomeContract Input Output} {program method}
    {certificate : TranslationValid rawLayouts layouts pins platform evidence imports program}
    {target} (refuted : c.RefutedAtEntryCLR program method certificate target) :
    ¬ c.HoldsAtEntryCLR program method certificate target := by
  rintro ⟨image, loaded, selected, initialized, _, holds⟩
  obtain ⟨other, memory, bound, ready, _, counterexample⟩ := refuted
  cases Option.some.inj (selected.symm.trans bound)
  cases Except.ok.inj (initialized.symm.trans ready)
  exact (counterexample []).not_holds (holds [])

#print axioms RefutedAtEntryCLR.not_holds

/-- Missing runtime definitions supply no witness against a CLR contract. -/
theorem not_refuted_of_unbound {c : OutcomeContract Input Output} {program method}
    {certificate : TranslationValid rawLayouts layouts pins platform evidence imports program}
    {target} (missing : certificate.entry target = none) :
    ¬ c.RefutedAtEntryCLR program method certificate target := by
  rintro ⟨_, _, bound, _⟩
  simp [missing] at bound

#print axioms not_refuted_of_unbound
end CIL.Safety.OutcomeContract
