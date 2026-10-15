import CIL.Extraction.LayoutCoverage

namespace Tests.LayoutCoverage
open CIL CIL.Extraction

private def layouts : List RawLayout :=
  [⟨"Packet", false, 0, 0, [⟨.unsigned64, none⟩]⟩]
private def packet : TypeExpr := .aggregate "Packet" 0
private def word : TypeExpr := .atom
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64"
private def body : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := word, parameters := [packet], locals := [packet],
  initLocals := true, maxStack := 8, genericParameters := [],
  code := [⟨0, 0x7b, .field packet 0 word false⟩,
    ⟨5, 0xfe15, .type packet⟩, ⟨11, 0x0f, .argument 0⟩] }
private def arguments : RawArguments :=
  ⟨[.field (.aggregate 0)], [.field (.aggregate 0)], [.other, .other, .address 0]⟩
private def uses : List LayoutUse :=
  [.field 0 0 0 .load, .size 1 0 .initialize, .local 0 0, .parameter 0 0]

example : LayoutUsesComplete layouts body arguments [true, true, true] uses := by decide
-- Omitting any instruction, local or parameter site cannot evade validation.
example : ∀ index ∈ List.range uses.length,
    ¬ LayoutUsesComplete layouts body arguments [true, true, true] (uses.eraseIdx index) := by decide
example : ¬ LayoutUsesComplete layouts body arguments [true] uses := by decide
example : ¬ LayoutUsesComplete layouts body arguments [true, true, true] uses.reverse := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field packet 1 word false⟩ = none := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field packet 0 packet false⟩ = none := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x73, .call { target := .managed 1, declaringType := packet, name := ".ctor", typeArguments := [], parameterCount := 0, hasThis := true, returnsValue := false }⟩ =
      some [.size 0 0 .construct] := by decide

end Tests.LayoutCoverage
