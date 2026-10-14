import Extracted
import Examples.Support
open CIL
namespace ExampleProof

theorem correctness (x y : W64) :
    invoke Extracted.program 8 0 [.i32 1, .i64 x, .i64 y] (fun _ => none) =
      some ((fun _ => none), [.i64 x]) := by
  rfl
#print axioms correctness
end ExampleProof
