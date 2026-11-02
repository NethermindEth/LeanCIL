import Extracted

/-! An entry type argument naming a struct from a pinned reference, sized from its metadata. -/

open CIL
namespace MultiAssemblyProof

/-- `Size<Cell> x` adds the eight-byte size of the referenced `Cell` for every input. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x + 8))] := by
  rfl

#print axioms correctness
end MultiAssemblyProof
