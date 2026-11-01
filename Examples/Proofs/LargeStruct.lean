import Extracted
open CIL.Safety
namespace ExampleProof

theorem correctness :
    (invoke Extracted.program 32 0 [.scalar (.i64 42)] Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 42)] := by rfl
#print axioms correctness
end ExampleProof
