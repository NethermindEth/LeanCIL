import Extracted

/-! Direct call from the selected assembly into a pinned referenced assembly's static method. -/

open CIL
namespace MultiAssemblyProof

/-- `Direct x` returns `Step x + 1` for every input, with `Step` extracted from the reference. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x * 3 + 1 + 1))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
