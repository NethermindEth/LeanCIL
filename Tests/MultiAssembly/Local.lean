import Extracted

/-! A local of a referenced struct type, laid out from the pinned DLL and updated by reference. -/

open CIL
namespace MultiAssemblyProof

/-- The referenced `Bump` rewrites the local `Cell` in place: `5 * 3 + 1 = 16`. -/
theorem correctness :
    (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 5)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 16)] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
