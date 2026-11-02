import Extracted

/-! A referenced method that calls another method of its own pinned assembly. -/

open CIL
namespace MultiAssemblyProof

/-- `Nested x` applies the referenced `Step` twice for every input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 ((x * 3 + 1) * 3 + 1))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
