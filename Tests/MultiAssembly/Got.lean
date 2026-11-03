import Extracted

/-! An instance interface slot dispatched to a struct declared in a pinned reference. -/

open CIL
namespace MultiAssemblyProof

/-- `Got 5` reads a local `Holder` through the Lib `IGet.Get` slot: `5 + 1 = 6`. -/
theorem correctness :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 5)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 6)] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
