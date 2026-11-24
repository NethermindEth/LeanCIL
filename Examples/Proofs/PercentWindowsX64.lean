import Extracted

namespace ExampleProof
open CIL CIL.Safety

/-- The packaged Windows x64 runtime loads the original literals from empty caller storage
and executes the managed constructor at the first out-of-range input. -/
theorem managedException :
    (Extracted.method0RangeImage5.map (fun image => image.invoke 66 [.scalar (.i32 101)])) =
      some (.ok (.error ⟨0, 6, .thrown .argumentOutOfRange⟩)) := by
  cil_kernel_rfl
#print axioms managedException

end ExampleProof
