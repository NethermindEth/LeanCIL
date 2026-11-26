import CIL.Safety.InstructionMemoryLemmas

/-!
# Span constructor results

A span constructor builds a checked view without changing memory, so running it in place on a
home changes only the slot the home names.
-/

namespace CIL.Safety

/-- A successful span constructor returns a validated view without changing memory. -/
theorem spanConstructor_result (constructor : CIL.SpanConstructor)
    (memory after : Memory) (stack : List Value) (value : Value) (rest : List Value)
    (constructed : memoryInstruction constructor.operation stack memory =
      .ok (after, value :: rest)) :
    after = memory ∧ value.Valid memory := by
  cases constructor <;> simp only [CIL.SpanConstructor.operation] at constructed
  all_goals unfold memoryInstruction at constructed
  all_goals simp only [singleSpanInstruction, otherMemoryInstruction, staticSpanInstruction]
    at constructed
  all_goals split at constructed
  all_goals repeat' first
    | contradiction
    | solve | cases constructed; exact ⟨rfl, checkedAt_ok (by assumption)⟩
    | solve |
        cases constructed
        exact ⟨rfl, SpanView.slice_valid _ _ _ _ _ (checkedAt_ok (by assumption))⟩
    | solve | cases constructed; exact ⟨rfl, trivial⟩
    | solve | cases constructed; exact ⟨rfl, formValue_reference_valid _ _ _ (by assumption)⟩
    | cases constructed
    | split at constructed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at constructed

#print axioms spanConstructor_result

end CIL.Safety
