import Extracted

/-! A struct of the selected assembly implementing a pinned reference's static abstract slot. -/

open CIL
namespace MultiAssemblyProof

/-- `Scaled<AppScale>` runs App's own `Scale`, adding nine to every input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 x)] Safety.Memory.empty).map
      Prod.snd =
      .ok [.scalar (.i64 (x + 9))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
