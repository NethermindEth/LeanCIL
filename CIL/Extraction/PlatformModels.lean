import CIL.Extraction.ModelTable

/-! Runtime models for hardware feature getters and the 64-bit platform constants. -/

namespace CIL.Extraction

/-- A parameterless getter reads a feature of the profile or a fixed platform word. -/
private inductive Getter where
  | supported (owner : String) (feature : Feature)
  | accelerated (owner : String) (feature : Feature)
  | size (owner : PrimitiveType)
  | processWidth

/-- The platform declaration, raw member and exact external identity agree on one getter. -/
private def getterEntry (scope : String) (owner : TypeExpr) (ownerName : String)
    (key : MetadataName) (name : String) (result : PrimitiveType) (model : RuntimeModel) :
    ModelEntry :=
  let resultType := TypeExpr.primitive result
  let declared : OpenSignature := { convention := 0, returnType := resultType }
  let target := s!"{scope}::{result.display} {ownerName}::{name}()"
  let accepts (method : MethodRef) := !method.hasThis && method.genericArity == 0 &&
    method.methodArguments.isEmpty && method.parameters.isEmpty && method.returnType == resultType
  let row : ModelOverload :=
    { operand := .external (fun _ => declared) name (fun _ => some target)
      accepts
      resolve := fun _ _ => some model }
  { opcode := .call, owner, name := key, ownsName := true, overloads := [row] }

/-- The exact member that returns the profile value or target width. -/
private def Getter.entry : Getter → ModelEntry
  | .supported owner feature =>
    let ownerName := "System.Runtime.Intrinsics." ++ owner
    getterEntry intrinsicsScope (.atom intrinsicsScope ownerName .classType) ownerName
      name!"get_IsSupported" "get_IsSupported" .boolean (.feature feature)
  | .accelerated owner feature =>
    let ownerName := "System.Runtime.Intrinsics." ++ owner
    getterEntry intrinsicsScope (.atom intrinsicsScope ownerName .classType) ownerName
      name!"get_IsHardwareAccelerated" "get_IsHardwareAccelerated" .boolean (.feature feature)
  | .size owner =>
    getterEntry runtimeScope (.primitive owner) owner.display name!"get_Size" "get_Size" .int32
      (.constant 8)
  | .processWidth =>
    let ownerName := "System.Environment"
    getterEntry runtimeScope (.atom runtimeScope ownerName .classType) ownerName
      name!"get_Is64BitProcess" "get_Is64BitProcess" .boolean (.constant 1)

/-- Each nested hardware owner names its own external target even when two return one flag. -/
private def getters : List Getter := [
  .supported "Arm.AdvSimd" .advSimd,
  .supported "Arm.AdvSimd/Arm64" .advSimd,
  .supported "Arm.ArmBase/Arm64" .armBase64,
  .supported "X86.Sse2" .sse2,
  .supported "X86.Ssse3" .ssse3,
  .supported "X86.Sse41" .sse41,
  .supported "X86.Sse42" .sse42,
  .supported "X86.Avx" .avx,
  .supported "X86.Avx2" .avx2,
  .supported "X86.Avx512F" .avx512F,
  .supported "X86.Avx512F/VL" .avx512FVL,
  .supported "X86.Avx512DQ" .avx512DQ,
  .supported "X86.Avx512DQ/VL" .avx512DQVL,
  .supported "X86.Avx512Vbmi" .avx512Vbmi,
  .supported "X86.Avx512Vbmi/VL" .avx512Vbmi,
  .supported "X86.Aes" .aes,
  .supported "X86.Aes/X64" .aes,
  .supported "Arm.Aes" .armAes,
  .supported "Arm.Aes/Arm64" .armAes,
  .supported "X86.Bmi1" .bmi1,
  .supported "X86.Bmi2/X64" .bmi2,
  .supported "X86.X86Base/X64" .x86Base64,
  .accelerated "Vector128" .vector128Accelerated,
  .accelerated "Vector256" .vector256Accelerated,
  .size .intPtr, .size .uintPtr, .processWidth]

/-- All hardware and platform getter slots of the runtime catalog. -/
def platformEntries := getters.map Getter.entry

/-- A getter row can only yield its specified model. -/
private theorem getterEntry_yields {scope owner ownerName key name result model}
    {property : RuntimeModel → Prop} (holds : property model) :
    (getterEntry scope owner ownerName key name result model).Yields property := by
  intro reader method actual found
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  simp only [getterEntry, ModelEntry.select?, ModelEntry.select?.select] at selected
  split at selected
  · cases selected
    cases resolved
    exact holds
  · cases selected

#print axioms getterEntry_yields

/-- Getter entries return only feature or constant models. -/
theorem platformEntries_yields {property : RuntimeModel → Prop}
    (feature : ∀ id, property (.feature id)) (constant : ∀ value, property (.constant value)) :
    ∀ entry ∈ platformEntries, entry.Yields property := by
  intro entry listed
  obtain ⟨getter, _, rfl⟩ := List.mem_map.mp listed
  cases getter <;> unfold Getter.entry <;> apply getterEntry_yields <;>
    first | apply feature | apply constant

#print axioms platformEntries_yields

end CIL.Extraction
