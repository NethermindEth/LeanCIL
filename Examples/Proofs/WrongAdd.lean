import Extracted
import CIL.ExecutionLemmas
import CIL.Safety.FuelLemmas
import Examples.Support
open CIL
namespace ExampleProof

theorem correctness (fuel : Nat) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke Extracted.program fuel 0 [.scalar (.i64 1), .scalar (.i64 1)] Examples.empty ≠
      .ok (memory, [.scalar (.i64 2)]) := by
  intro alleged
  have observed : CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i64 1), .scalar (.i64 1)] Examples.empty =
      .ok (Examples.empty, [.scalar (.i64 0)]) := rfl
  have first := CIL.Safety.invoke_mono _ 4 fuel _ _ _ (.ok _) trivial observed
  have second := CIL.Safety.invoke_mono _ fuel 4 _ _ _ (.ok _) trivial alleged
  rw [Nat.add_comm] at second
  rw [first] at second
  simp at second

#print axioms correctness
end ExampleProof
