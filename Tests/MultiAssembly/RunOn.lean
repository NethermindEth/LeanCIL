import Extracted

/-! Constrained static dispatch to a flag struct from a pinned reference, folded to true. -/

open CIL
namespace MultiAssemblyProof

/-- `Run<On>` applies the referenced `Step` for every input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x * 3 + 1))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
