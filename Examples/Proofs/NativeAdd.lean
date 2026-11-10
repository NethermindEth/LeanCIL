import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- Native addition on the admitted 64-bit target is modular word addition. -/
theorem correctness (x y : W64) :
    (CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 x), .scalar (.i64 y)]
      Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x + y))] := by
  have ran : CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 x), .scalar (.i64 y)]
      Memory.empty = .ok (Memory.empty, [.scalar (.i64 (x + y))]) := by
    cil_checked_steps
  rw [ran]
  rfl

#print axioms correctness
end ExampleProof
