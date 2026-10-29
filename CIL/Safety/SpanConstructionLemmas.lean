import CIL.Safety.InstructionMemoryLemmas

/-!
# Span constructor results

Local span initialization reuses checked view construction without changing backing memory.
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
  all_goals simp only [singleSpanInstruction, otherMemoryInstruction] at constructed
  all_goals split at constructed
  all_goals repeat' first
    | contradiction
    | solve | cases constructed; exact ⟨rfl, checkedAt_ok (by assumption)⟩
    | solve |
        cases constructed
        exact ⟨rfl, SpanView.slice_valid _ _ _ _ _ (checkedAt_ok (by assumption))⟩
    | cases constructed
    | split at constructed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at constructed

#print axioms spanConstructor_result

end CIL.Safety
