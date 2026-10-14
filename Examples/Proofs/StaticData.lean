import Extracted
import Examples.Support
open CIL.Safety
namespace ExampleProof

theorem correctness :
    (invoke Extracted.program 4 0 [.scalar (.i64 0), .scalar (.i64 0)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 42)] := rfl
#print axioms correctness
end ExampleProof
