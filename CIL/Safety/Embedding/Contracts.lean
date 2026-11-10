import CIL.Safety.Embedding.Simulation
import CIL.Safety.MethodContract

/-!
# Contracts of embedded code

Checked embedding transports an existing method contract without changing its inputs, memory
footprint or postcondition. The underlying simulation checks instruction and metadata agreement.
-/

namespace CIL.Safety

/-- A suffix precondition transfers through checked embedding without exposing its fuel. -/
theorem WP.of_embedded_run {program : CIL.Program} {index pc : Nat}
    {expected target : CIL.Method} {map : List Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {post : Memory → List Value → Prop}
    (proof : WP (fun fuel => run (program.set index expected) fuel index pc
      args frame stack memory) post)
    (found : program[index]? = some target) (embedded : CIL.Embeds expected target map) :
    WP (fun fuel => run program fuel index (CIL.Embedding.rename map target.code.length pc)
      args frame stack memory) post := by
  obtain ⟨fuel, final, values, ran, satisfied⟩ := proof
  exact ⟨fuel, final, values, embedded.run found ran, satisfied⟩

#print axioms WP.of_embedded_run

/-- A contract proved with a canonical embedded body also holds for the actual program. -/
theorem MethodContract.Holds.of_embeds {Input Output : Type}
    {contract : MethodContract Input Output} {program : CIL.Program} {index method : Nat}
    {expected : CIL.Method} (holds : contract.Holds (program.set index expected) method)
    (embedded : CIL.MethodEmbeds program index expected) : contract.Holds program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, result⟩ := holds input initial permitted
  exact ⟨fuel, final, values, embedded.invoke invoked, result⟩

#print axioms MethodContract.Holds.of_embeds

end CIL.Safety
