import Extracted

/-! The static virtual default body of an interface declared in a pinned reference. -/

open CIL
namespace MultiAssemblyProof

/-- `Scaled<Plain>` runs the Lib interface's default `Scale`, doubling every input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x * 2))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
