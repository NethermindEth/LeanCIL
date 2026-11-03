import Extracted

/-! The most specific interface body of a pinned reference's static virtual slot. -/

open CIL
namespace MultiAssemblyProof

/-- `Scaled<T>` runs a derived interface's `IScale.Scale`, not the default, quadrupling every
    input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x * 4))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
