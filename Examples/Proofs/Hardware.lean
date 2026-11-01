import Extracted
open CIL.Safety
namespace ExampleProof

theorem correctness :
    (invoke Extracted.program 4 0 [] Memory.empty).map Prod.snd = .ok [.scalar (.i32 0)] := rfl
#print axioms correctness
end ExampleProof
