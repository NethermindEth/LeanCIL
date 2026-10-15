import CIL.Extraction.Generics

namespace Tests.ExtractionGenerics
open CIL CIL.Extraction

def word : TypeExpr := .atom "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64"
def raw : RawMethod := {
  token := 1, owner := "Test", hasThis := false, explicitThis := false,
  callingConvention := 16, attributes := 0, implementation := 0,
  returnType := .parameter 0, parameters := [.byref (.parameter 0)],
  locals := [.parameter 0], initLocals := true, maxStack := 2,
  genericParameters := [⟨24, []⟩],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type (.parameter 0)⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
def closed : RawMethod := { raw with
  callingConvention := 0, returnType := word, parameters := [.byref word],
  locals := [word], genericParameters := [],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
example : instantiateMethod [] raw [word] = some closed := by decide
example : instantiateMethod [] raw [] = none := by decide
example : instantiateMethod [] raw [.byref word] = none := by decide
example : instantiateMethod [] { raw with genericParameters := [⟨4, []⟩] } [word] = none := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with locals := [] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with returnType := .void } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with code := [⟨0, 42, .none⟩] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with
    code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 1⟩, ⟨9, 42, .none⟩] } := by decide
example : typeStorage [] (.atom "attacker" "System.UInt64") = none := by decide
example : typeStorage [⟨"A", false, 0, 0, []⟩] (.aggregate "B" 0) = none := by decide
example : substituteType [word] (.apply (.constructor "scope" "Box`1") (.parameter 0)) =
    some (.apply (.constructor "scope" "Box`1") word) := by decide
end Tests.ExtractionGenerics
