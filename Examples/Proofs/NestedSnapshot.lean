import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- Reading the nested value copies exactly its bytes, including padding. -/
theorem correctness (bytes : List (BitVec 8)) (size : bytes.length = 32) :
    (invoke Extracted.program 3 0 [.scalar (.aggregate bytes)] Memory.empty).map Prod.snd =
      .ok [.scalar (.aggregate ((bytes.drop 8).take 16))] := by
  have ran : invoke Extracted.program 3 0 [.scalar (.aggregate bytes)] Memory.empty =
      .ok (Memory.empty, [.scalar (.aggregate ((bytes.drop 8).take 16))]) := by
    cil_checked_steps [size]
  rw [ran]
  rfl

#print axioms correctness
end ExampleProof
