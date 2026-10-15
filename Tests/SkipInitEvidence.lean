import CIL.Extraction.SkipInit

open CIL CIL.Extraction

namespace Tests.SkipInitEvidence

private def scope := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def call : CallSite := {
  declaringType := .atom scope "System.Runtime.CompilerServices.Unsafe", name := "SkipInit"
  target := .external (scope ++ "::System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(!!0&)")
  typeArguments := [.atom scope "System.UInt64"], parameterCount := 1, hasThis := false, returnsValue := false }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 1, genericParameters := [], code := [⟨0, 0x28, .call site⟩] }

example : SkipInitValid [] (raw call) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw call) [true] [.pop] := by decide
example : ¬ SkipInitValid [] (raw { call with name := "Other" }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with target := .external "forged" }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with declaringType := .atom "forged" "System.Runtime.CompilerServices.Unsafe" }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with hasThis := true }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with parameterCount := 2 }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with returnsValue := true }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with typeArguments := [.byref (.atom scope "System.UInt64")] }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw { call with typeArguments := [] }) [true] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw call) [] [.skipInit] := by decide
example : ¬ SkipInitValid [] (raw call) [true] [] := by decide

end Tests.SkipInitEvidence
