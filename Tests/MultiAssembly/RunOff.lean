import Extracted

/-! Constrained static dispatch to a flag struct from a pinned reference, folded to false. -/

open CIL
namespace MultiAssemblyProof

/-- `Run<Off>` returns its input: the Lib getter is constant false, so `Step` is never reached. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
