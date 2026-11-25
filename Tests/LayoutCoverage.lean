import CIL.Extraction.LayoutCoverage

/-! Layout coverage for struct fields, span resets, locals and parameters. -/

namespace Tests.LayoutCoverage
open CIL CIL.Extraction

private def layouts : List RawLayout :=
  [{ identity := "Packet"
     explicit := false
     packing := 0
     declaredSize := 0
     fields := [⟨.unsigned64, none⟩] }]
private def packet : TypeExpr := .aggregate "Packet" 0
private def word : TypeExpr := .primitive .uint64
private def body : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := word, parameters := [packet], locals := [packet],
  initLocals := true, maxStack := 8, genericParameters := [],
  code := [⟨0, 0x7b, .field packet 0 word name!"first" false⟩,
    ⟨5, 0xfe15, .type (.apply (.constructor runtimeScope "System.Span`1") packet)⟩,
    ⟨11, 0x0f, .argument 0⟩] }
private def arguments : RawArguments :=
  ⟨[.field (.aggregate 0)], [.field (.aggregate 0)], [.other, .other, .address 0]⟩
private def uses : List LayoutUse :=
  [.local 0 0, .parameter 0 0]

example : LayoutUsesComplete layouts body arguments [true, true, true] uses := by decide
-- Omitting any instruction, local or parameter site cannot evade validation.
example : ∀ index ∈ List.range uses.length,
    ¬ LayoutUsesComplete layouts body arguments [true, true, true] (uses.eraseIdx index) := by decide
example : ¬ LayoutUsesComplete layouts body arguments [true] uses := by decide
example : ¬ LayoutUsesComplete layouts body arguments [true, true, true] uses.reverse := by decide
/-- Typed object operations obtain their width from the closed operand. -/
theorem object_sites : [0x70, 0x71, 0x81, 0xfe15, 0xfe1c].all (fun opcode =>
    instructionLayoutUses layouts 0 ⟨0, opcode, .type packet⟩ == some []) = true := by decide
#print axioms object_sites

-- A struct field access needs no use: the step reads its entry from the checked layouts.
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field packet 0 word name!"first" false⟩ = some [] := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field packet 1 word name!"first" false⟩ = none := by decide
-- An owner naming another identity at Packet's layout index has no checked layout.
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field (.aggregate "Counter" 0) 0 word name!"first" false⟩ = none := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x7b, .field packet 0 packet name!"first" false⟩ = none := by decide
example : instructionLayoutUses layouts 0
    ⟨0, 0x73, .call {
      declared := { convention := 0x20 },
      method := {
        owner := packet, name := name!".ctor", hasThis := true, genericArity := 0,
        returnType := .void, parameters := [] },
      target := .managed 1, name := ".ctor", typeArguments := [],
      parameterCount := 0, returnsValue := false }⟩ =
      some [.size 0 0] := by decide

end Tests.LayoutCoverage
