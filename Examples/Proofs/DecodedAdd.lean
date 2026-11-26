import Extracted
import CIL.Safety.DecodedSegment

/-!
# Addition over the decoded program

`correctness_decoded` states the addition contract of `Examples.Arithmetic::Add` for the program
that `Extraction.decodedProgram?` reads from the extraction's body bytes. The proof checks the
feature certificate and evaluates the method decoded from the pinned bytes.
-/

open CIL
namespace ExampleProof

/-- The program the Add body bytes denote returns the sum of its two 64-bit arguments modulo
    2^64, in the specified empty initial memory. -/
theorem correctness_decoded : ∃ program : CIL.Program,
    Extraction.decodedProgram? Extracted.profile Extracted.environment
      Extracted.methodEvidence = some program ∧ ∀ x y : W64, ∃ result : W64,
      (CIL.Safety.invoke program 4 0 [.scalar (.i64 x), .scalar (.i64 y)]
        Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 result)] ∧
      result.toNat = (x.toNat + y.toNat) % 2^64 := by
  simp only [Extraction.decodedProgram?, Extracted.methodEvidence, List.mapM_cons,
    List.mapM_nil, Method.ofBody?_of_decodes Extracted.method0_body_validated,
    Option.filter_eq_some_iff]
  exact ⟨_, ⟨rfl, by decide +kernel⟩, fun x y => ⟨x + y, rfl, BitVec.toNat_add x y⟩⟩

#print axioms correctness_decoded
/-- At the add instruction, the stack contains the right and left operands. The continuation
    keeps the frame and memory and replaces the operands with their sum. -/
def arithmeticStep (left right : W64) : Safety.SegmentContract :=
  .continuing 3 (fun _ before => before.stack = [.scalar (.i64 right), .scalar (.i64 left)])
    (fun _ before after => after = { before with stack := [.scalar (.i64 (left + right))] })
    (fun _ _ => [])

/-- The arithmetic step at pc 2 is bound to the selected Add method and its certified body. -/
theorem arithmetic_region (left right : W64) :
    Safety.DecodedSegmentSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 0 2 Extracted.methodEvidence[0].assembly
      Extracted.methodEvidence[0].original.token Extracted.methodEvidence[0].arguments
      .add [] [] (arithmeticStep left right) := by
  refine ⟨Safety.DecodedAt.of_translation Extracted.translation_valid ⟨0, by decide⟩
    Extracted.program_method0, ⟨_, Extracted.program_method0, rfl⟩, fun _ => ?_,
    .of_sites [0] (by decide) (by decide) rfl⟩
  rintro args ⟨frame, stack, memory⟩ permitted
  change stack = _ at permitted
  subst stack
  let after : Safety.SegmentState := ⟨frame, [.scalar (.i64 (left + right))], memory⟩
  refine ⟨.reaches 3 after, ⟨1, by decide, Safety.SegmentRun.reaches ?_⟩,
    Safety.Confined.refl _ _, rfl, rfl⟩
  intro fuel
  rfl

#print axioms arithmetic_region
end ExampleProof
