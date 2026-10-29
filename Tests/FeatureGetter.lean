import CIL.Extraction.Features

/-!
# Exact feature getter identities

The byte-table lookup must retain assembly, namespace, class and member identity,
including malformed signatures which share the admitted prefix.
-/

namespace Tests.FeatureGetter

open CIL CIL.Extraction

/-- A static feature getter with independently constructed raw metadata. -/
def getter (owner member : String) : CallSite := {
  declaringType := .atom intrinsicsScope ("System.Runtime.Intrinsics." ++ owner)
  name := member
  target := .external (intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics." ++
    owner ++ "::" ++ member ++ "()")
  parameterCount := 0, hasThis := false, returnsValue := true, typeArguments := []
  returnType := .atom runtimeScope "System.Boolean", parameterTypes := [] }

/-- Hardware acceleration, nested class and ordinary supported getters retain their flags. -/
theorem supported :
    featureGetter (getter "Vector256" "get_IsHardwareAccelerated") = some .vector256Accelerated ∧
    featureGetter (getter "X86.Sse41" "get_IsSupported") = some .sse41 ∧
    featureGetter (getter "Arm.ArmBase/Arm64" "get_IsSupported") = some .armBase64 := by
  decide +kernel
#print axioms supported

/-- A syntactically similar identity cannot change the exact admitted feature class or member. -/
theorem wrong_names :
    featureGetter (getter "Vector256" "get_IsSupported") = none ∧
    featureGetter (getter "X86.Sse41X" "get_IsSupported") = none ∧
    featureGetter (getter "X86.Sse41" "get_IsSupportedX") = none ∧
    featureGetter (getter "X86.Ssé41" "get_IsSupported") = none := by decide +kernel
#print axioms wrong_names

/-- Truncation, an incorrect assembly and trailing signature bytes all fail exact matching. -/
theorem wrong_prefix_or_tail :
    (List.all ["", intrinsicsScope, intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.",
      "Other::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()",
      intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()X"]
      (fun identity =>
        (featureGetter { getter "X86.Sse41" "get_IsSupported" with
          target := .external identity }).isNone)) = true := by decide +kernel
#print axioms wrong_prefix_or_tail

/-- Signature acceleration leaves the existing call-shape checks intact. -/
theorem wrong_call_shape :
    featureGetter { getter "X86.Sse41" "get_IsSupported" with parameterCount := 1 } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with hasThis := true } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with returnsValue := false } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with
      typeArguments := [.atom runtimeScope "System.Int32"] } = none := by decide +kernel
#print axioms wrong_call_shape

/-- Raw process-width calls retain their exact owner, result and external identity. -/
def platform (owner member result : String) : CallSite := {
  declaringType := .atom runtimeScope owner, name := member
  target := .external (runtimeScope ++ "::" ++ result ++ " " ++ owner ++ "::" ++ member ++ "()")
  parameterCount := 0, hasThis := false, returnsValue := true, typeArguments := []
  returnType := .atom runtimeScope result, parameterTypes := [] }

/-- Both native-size getters and the process query use the admitted 64-bit platform. -/
theorem platform_values :
    platformConstant (platform "System.IntPtr" "get_Size" "System.Int32") = some 8 ∧
    platformConstant (platform "System.UIntPtr" "get_Size" "System.Int32") = some 8 ∧
    platformConstant (platform "System.Environment" "get_Is64BitProcess" "System.Boolean") =
      some 1 := by decide +kernel
#print axioms platform_values

/-- A platform constant is checked even when its forged instruction has the same stack effect. -/
theorem platform_encoding (raw : RawMethod) :
    let site := platform "System.IntPtr" "get_Size" "System.Int32"
    featureOpMatches raw ⟨0, 40, .call site⟩ (.const32 8) = true ∧
    featureOpMatches raw ⟨0, 40, .call site⟩ (.const32 4) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with
      declaringType := .atom "forged" "System.IntPtr" }⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with
      target := .external "forged" }⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with
      returnType := .atom runtimeScope "System.UInt32" }⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 111, .call site⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with hasThis := true }⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with parameterCount := 1 }⟩ (.const32 8) = false ∧
    featureOpMatches raw ⟨0, 40, .call { site with
      typeArguments := [.atom runtimeScope "System.Int32"] }⟩ (.const32 8) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms platform_encoding

end Tests.FeatureGetter
