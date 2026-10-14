import Extracted
import Examples.Support
open CIL.Safety
namespace ExampleProof

theorem correctness :
    (invoke Extracted.program 32 0 [Examples.reference, Examples.reference] Examples.caller).map Prod.snd =
      .ok [.scalar (.i64 9)] := by rfl
#print axioms correctness
end ExampleProof
