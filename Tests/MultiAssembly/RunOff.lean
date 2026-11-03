import Extracted

/-! Constrained static dispatch to a flag struct of either assembly, folded to false. -/

open CIL
namespace MultiAssemblyProof

/-- `Run<T>` returns its input: the getter is constant false, so `Step` is never reached. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
