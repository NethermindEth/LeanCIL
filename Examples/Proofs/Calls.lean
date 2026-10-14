import Extracted
import Examples.Support
open CIL.Safety
namespace ExampleProof

theorem correctness :
    (invoke Extracted.program 32 0 [.scalar (.i64 40)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 43)] := by rfl
#print axioms correctness
end ExampleProof
