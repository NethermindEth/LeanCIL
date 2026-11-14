import CIL.Extraction.UnsafeCalls

open CIL CIL.Extraction

namespace Tests.UnsafeCallEvidence

private def scope :=
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def unsafeType : TypeExpr := .atom scope "System.Runtime.CompilerServices.Unsafe"
private def word : TypeExpr := .atom scope "System.UInt64"
private def call : CallSite := {
  declaringType := unsafeType, name := "SkipInit"
  target := .external (scope ++ "::System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(!!0&)")
  typeArguments := [word], parameterCount := 1, hasThis := false, returnsValue := false }
private def nullCall : CallSite := {
  declaringType := unsafeType, name := "NullRef"
  target := .external (scope ++ "::!!0& System.Runtime.CompilerServices.Unsafe::NullRef()")
  typeArguments := [word], parameterCount := 0, hasThis := false, returnsValue := true }
private def testCall : CallSite := {
  declaringType := unsafeType, name := "IsNullRef"
  target := .external (scope ++ "::System.Boolean System.Runtime.CompilerServices.Unsafe::IsNullRef(!!0&)")
  typeArguments := [word], parameterCount := 1, hasThis := false, returnsValue := true }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 1, genericParameters := [], code := [⟨0, 0x28, .call site⟩] }
private def nonCall : RawMethod := { raw call with code := [⟨0, 0x26, .none⟩] }

example : UnsafeCallsValid [] (raw call) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [true] [.pop] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with name := "Other" }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with target := .external "forged" }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with declaringType := .atom "forged" "System.Runtime.CompilerServices.Unsafe" }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with hasThis := true }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with parameterCount := 2 }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with returnsValue := true }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with typeArguments := [.byref word] }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { call with typeArguments := [] }) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [true] [] := by decide +kernel

-- `NullRef` must push the null reference: no other operation with its stack effect.
example : UnsafeCallsValid [] (raw nullCall) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true] [.ldc_i4 0] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true] [.memory (.staticAddress [])] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with target := .external "forged" }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with parameterCount := 1 }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with returnsValue := false }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with hasThis := true }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with typeArguments := [.byref word] }) [true] [.memory .nullRef] := by decide +kernel

-- `IsNullRef` must test for null: a constant or a reinterpretation cannot stand in for it.
example : UnsafeCallsValid [] (raw testCall) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw testCall) [true] [.memory .asRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw testCall) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with name := "NullRef" }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with target := .external "forged" }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with parameterCount := 2 }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with returnsValue := false }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with typeArguments := [word, word] }) [true] [.memory .isNullRef] := by decide +kernel

-- A helper operation cannot replace an unrelated instruction.
example : ¬ UnsafeCallsValid [] nonCall [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] nonCall [true] [.memory .isNullRef] := by decide +kernel
example : UnsafeCallsValid [] nonCall [true] [.pop] := by decide +kernel
-- Unreachable sites are emitted as unsupported placeholders and are not bound.
example : UnsafeCallsValid [] (raw nullCall) [false] [.unsupported "excluded"] := by decide +kernel

end Tests.UnsafeCallEvidence

namespace Tests.UnsafeCallEvidence

/-- A genuine managed call to a local lookalike is not reserved as a lowered runtime helper. -/
theorem local_reference_helper_name :
    UnsafeCallsValid [] (raw { call with
      declaringType := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe",
      name := "AreSame", parameterCount := 2, returnsValue := true }) [true] [.call 1 2] := by
  decide +kernel
#print axioms local_reference_helper_name

/-- The `System.Object` constructor a class constructor calls on its receiver. -/
private def objectConstructor : CallSite := {
  declaringType := .atom scope "System.Object", name := ".ctor"
  target := .external (scope ++ "::System.Void System.Object::.ctor()")
  typeArguments := [], parameterCount := 0, hasThis := true, returnsValue := false }

-- Only the exact `System.Object` constructor may emit `pop`, and it must.
theorem object_constructor_pop :
    UnsafeCallsValid [] (raw objectConstructor) [true] [.pop] := by decide +kernel
#print axioms object_constructor_pop
theorem object_constructor_elsewhere_rejected :
    ¬ UnsafeCallsValid [] (raw { objectConstructor with
      declaringType := .atom "forged" "System.Object" }) [true] [.pop] ∧
    ¬ UnsafeCallsValid [] (raw { objectConstructor with
      target := .external "forged" }) [true] [.pop] ∧
    ¬ UnsafeCallsValid [] (raw { objectConstructor with parameterCount := 1 }) [true] [.pop] ∧
    ¬ UnsafeCallsValid [] (raw { objectConstructor with hasThis := false }) [true] [.pop] ∧
    ¬ UnsafeCallsValid [] (raw objectConstructor) [true] [.nop] ∧
    ¬ UnsafeCallsValid [] (raw call) [true] [.pop] := by decide +kernel
#print axioms object_constructor_elsewhere_rejected

end Tests.UnsafeCallEvidence
