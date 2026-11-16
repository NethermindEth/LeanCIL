import Extracted
import CIL.Extraction.DecodedMethod

/-!
# Addition over the decoded program

`correctness_decoded` states the addition contract of `Examples.Arithmetic::Add` for the program
that `Extraction.decodedProgram?` reads from the extraction's body bytes. The proof rewrites each
method of the evidence with `Method.ofBody?_of_decodes` and the generated body check, then runs
the decoded method by evaluation; it names neither `Extracted.method0` nor `Extracted.program`,
so no instruction the translator emitted enters the statement or the proof.
-/

open CIL
namespace ExampleProof

/-- The program the Add body bytes denote returns the sum of its two 64-bit arguments modulo
    2^64, in the specified empty initial memory. -/
theorem correctness_decoded : ∃ program : CIL.Program,
    Extraction.decodedProgram? Extracted.profile Extracted.environment
      Extracted.methodEvidence (fun _ => []) = some program ∧ ∀ x y : W64, ∃ result : W64,
      (CIL.Safety.invoke program 4 0 [.scalar (.i64 x), .scalar (.i64 y)]
        Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 result)] ∧
      result.toNat = (x.toNat + y.toNat) % 2^64 := by
  simp only [Extraction.decodedProgram?, Extracted.methodEvidence, List.mapM_cons,
    List.mapM_nil, Method.ofBody?_of_decodes Extracted.method0_body_validated]
  exact ⟨_, rfl, fun x y => ⟨x + y, rfl, BitVec.toNat_add x y⟩⟩

#print axioms correctness_decoded
end ExampleProof
