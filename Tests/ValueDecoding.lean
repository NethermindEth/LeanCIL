import CIL.Extraction.Scalars
import CIL.Extraction.DecodedDefinition

/-!
# Value decoding coverage

Every `CIL.Instruction` constructor is produced by `Instruction.ofRaw?` for a named opcode or is
listed as one that no opcode decodes to, `ofRaw?` decodes exactly the named opcodes, and an
emitted instruction that differs from the decoded one in constructor, operand or operand range
does not match.
-/

namespace Tests.ValueDecoding

open CIL CIL.Extraction Lean Meta

/-- An `int32` instance field of a class, at raw index 1. -/
def classOperand : RawOperand :=
  .field (.object "T" "T.Account") 1 (.atom runtimeScope "System.Int32") name!"balance" false

/-- The field `classOperand` names. -/
def classField : FieldRef :=
  { owner := .object "T" "T.Account", index := 1, type := .atom runtimeScope "System.Int32",
    name := name!"balance" }

/-- An `int32` instance field of a struct, at raw index 1. -/
def structOperand : RawOperand :=
  .field (.aggregate "T::Pair" 0) 1 (.atom runtimeScope "System.Int32") name!"balance" false

/-- The field `structOperand` names. -/
def structField : FieldRef := { classField with owner := .aggregate "T::Pair" 0 }

/-- The class the type test rows name. -/
private def dog : TypeExpr := .object "Fixture" "Fixture.Dog"

/-- The element type `System.Int32`. -/
private def int32 : TypeExpr := .atom runtimeScope "System.Int32"

/-- A one-field generic layout whose owner is the runtime span named by `name`. -/
private def spanLayout (name : String) : RawLayout :=
  let owner := TypeExpr.constructor runtimeScope name
  { identity := (genericOwnerIdentity owner [int32]).getD ""
    explicit := false, packing := 0, declaredSize := 0, byRefLike := true
    fields := [⟨.signed32, none⟩]
    generic := some ⟨owner, 1, [int32], [.parameter 0], [(0, [])]⟩ }

/-- The span reset fixture has a valid four-byte layout row and decodes to `initobj`. -/
theorem span_reset_inputs :
    ["System.Span`1", "System.ReadOnlySpan`1"].all (fun name =>
      let span := TypeExpr.apply (.constructor runtimeScope name) int32
      decide (LayoutsValid [spanLayout name] #[⟨⟨4, [⟨0, 4, false⟩]⟩, 4⟩]) &&
        Instruction.ofRaw? none ⟨0, 0xfe15, .type span⟩ == some (.initobj span)) = true := by
  decide +kernel
#print axioms span_reset_inputs

/-- Specializing a span reset over a matching generic layout preserves its operand and decoding. -/
theorem span_reset_substitution :
    ["System.Span`1", "System.ReadOnlySpan`1"].all (fun name =>
      let span := TypeExpr.apply (.constructor runtimeScope name) int32
      let closed := substituteOperand [] [spanLayout name] 0 (.type span)
      closed == some (.type span) &&
        (closed.bind fun operand => Instruction.ofRaw? none ⟨0, 0xfe15, operand⟩) ==
          some (.initobj span)) = true := by decide +kernel
#print axioms span_reset_substitution

/-- A static call site of `T.Account::Deposit(int32)`. -/
private def callSite : CallSite := {
  declared := { convention := 0, parameters := [.atom runtimeScope "System.Int32"] },
  method := {
    owner := .object "T" "T.Account", name := name!"Deposit", hasThis := false,
    genericArity := 0, returnType := .void, parameters := [.atom runtimeScope "System.Int32"] },
  name := "Deposit", target := .managed 0x06000001, typeArguments := [], parameterCount := 1,
  returnsValue := false }

/-- A managed site of the `int32` constructor of `T.Account`. -/
private def accountConstruction : CallSite := {
  declared := { convention := 0x20, parameters := [.atom runtimeScope "System.Int32"] },
  method := {
    owner := .object "T" "T.Account", name := name!".ctor", hasThis := true, genericArity := 0,
    returnType := .void, parameters := [.atom runtimeScope "System.Int32"] },
  name := ".ctor", target := .managed 1, typeArguments := [], parameterCount := 1,
  returnsValue := false }

/-- An instance slot callable with or without a constrained prefix. -/
private def instanceSite : CallSite := { callSite with method.hasThis := true }

/-- The prefix carried by a named decode-table row: a constrained receiver before the call at
    offset 6, and `unaligned. 2` before the block operations at offset 2. -/
private def predecessor (raw : RawInstruction) : Option RawInstruction :=
  if raw.opcode == 111 && raw.offset == 6 then some ⟨0, 0xFE16, .type int32⟩
  else if (raw.opcode == 65047 || raw.opcode == 65048) && raw.offset == 2 then
    some ⟨0, 0xFE12, .integer 2⟩
  else none

/-- One raw instruction per value opcode, every short, long and macro form, with the instruction
    ECMA-335 assigns it; constants include the extremes of each form's range and locals the largest
    index each width encodes. -/
def named : List (RawInstruction × Instruction) := [
  -- Stack shuffling and return.
  (⟨0, 0, .none⟩, .nop), (⟨0, 37, .none⟩, .dup), (⟨0, 38, .none⟩, .pop), (⟨0, 42, .none⟩, .ret),
  -- Constants.
  (⟨0, 114, .text "literal"⟩, .memory (.stringLiteral "literal")),
  (⟨0, 20, .none⟩, .ldnull), (⟨0, 21, .none⟩, .ldc_i4 (-1)), (⟨0, 22, .none⟩, .ldc_i4 0),
  (⟨0, 23, .none⟩, .ldc_i4 1),
  (⟨0, 24, .none⟩, .ldc_i4 2), (⟨0, 25, .none⟩, .ldc_i4 3), (⟨0, 26, .none⟩, .ldc_i4 4),
  (⟨0, 27, .none⟩, .ldc_i4 5), (⟨0, 28, .none⟩, .ldc_i4 6), (⟨0, 29, .none⟩, .ldc_i4 7),
  (⟨0, 30, .none⟩, .ldc_i4 8), (⟨0, 31, .integer (-5)⟩, .ldc_i4 (-5)),
  (⟨0, 31, .integer (-128)⟩, .ldc_i4 (-128)), (⟨0, 31, .integer 127⟩, .ldc_i4 127),
  (⟨0, 32, .integer 70000⟩, .ldc_i4 70000),
  (⟨0, 32, .integer (-2147483648)⟩, .ldc_i4 (-2147483648)),
  (⟨0, 32, .integer 2147483647⟩, .ldc_i4 2147483647),
  (⟨0, 33, .integer (-1)⟩, .ldc_i8 (-1)),
  (⟨0, 33, .integer (-9223372036854775808)⟩, .ldc_i8 (-9223372036854775808)),
  (⟨0, 33, .integer 9223372036854775807⟩, .ldc_i8 9223372036854775807),
  -- Arguments.
  (⟨0, 2, .none⟩, .ldarg 0), (⟨0, 3, .none⟩, .ldarg 1), (⟨0, 4, .none⟩, .ldarg 2),
  (⟨0, 5, .none⟩, .ldarg 3), (⟨0, 14, .argument 5⟩, .ldarg 5),
  (⟨0, 14, .argument 255⟩, .ldarg 255), (⟨0, 65033, .argument 300⟩, .ldarg 300),
  (⟨0, 15, .argument 5⟩, .ldarga 5), (⟨0, 15, .argument 255⟩, .ldarga 255),
  (⟨0, 65034, .argument 65535⟩, .ldarga 65535), (⟨0, 16, .argument 5⟩, .starg 5),
  (⟨0, 16, .argument 255⟩, .starg 255), (⟨0, 65035, .argument 65535⟩, .starg 65535),
  -- Locals.
  (⟨0, 6, .none⟩, .ldloc 0), (⟨0, 7, .none⟩, .ldloc 1), (⟨0, 8, .none⟩, .ldloc 2),
  (⟨0, 9, .none⟩, .ldloc 3), (⟨0, 17, .local 4⟩, .ldloc 4), (⟨0, 17, .local 255⟩, .ldloc 255),
  (⟨0, 65036, .local 300⟩, .ldloc 300), (⟨0, 65036, .local 65535⟩, .ldloc 65535),
  (⟨0, 10, .none⟩, .stloc 0), (⟨0, 11, .none⟩, .stloc 1), (⟨0, 12, .none⟩, .stloc 2),
  (⟨0, 13, .none⟩, .stloc 3), (⟨0, 19, .local 4⟩, .stloc 4), (⟨0, 65038, .local 300⟩, .stloc 300),
  (⟨0, 18, .local 4⟩, .ldloca 4), (⟨0, 65037, .local 300⟩, .ldloca 300),
  -- Branches, short forms then long forms, each to a target named after its opcode.
  (⟨0, 43, .target 43⟩, .br 43), (⟨0, 44, .target 44⟩, .brfalse 44),
  (⟨0, 45, .target 45⟩, .brtrue 45), (⟨0, 46, .target 46⟩, .beq 46),
  (⟨0, 47, .target 47⟩, .bge 47), (⟨0, 48, .target 48⟩, .bgt 48),
  (⟨0, 49, .target 49⟩, .ble 49), (⟨0, 50, .target 50⟩, .blt 50),
  (⟨0, 51, .target 51⟩, .bne_un 51), (⟨0, 52, .target 52⟩, .bge_un 52),
  (⟨0, 53, .target 53⟩, .bgt_un 53), (⟨0, 54, .target 54⟩, .ble_un 54),
  (⟨0, 55, .target 55⟩, .blt_un 55),
  (⟨0, 56, .target 56⟩, .br 56), (⟨0, 57, .target 57⟩, .brfalse 57),
  (⟨0, 58, .target 58⟩, .brtrue 58), (⟨0, 59, .target 59⟩, .beq 59),
  (⟨0, 60, .target 60⟩, .bge 60), (⟨0, 61, .target 61⟩, .bgt 61),
  (⟨0, 62, .target 62⟩, .ble 62), (⟨0, 63, .target 63⟩, .blt 63),
  (⟨0, 64, .target 64⟩, .bne_un 64), (⟨0, 65, .target 65⟩, .bge_un 65),
  (⟨0, 66, .target 66⟩, .bgt_un 66), (⟨0, 67, .target 67⟩, .ble_un 67),
  (⟨0, 68, .target 68⟩, .blt_un 68), (⟨0, 69, .targets [1, 2]⟩, .switch [1, 2]),
  -- Integer indirect loads and stores.
  (⟨0, 70, .none⟩, .ldind .i1), (⟨0, 71, .none⟩, .ldind .u1), (⟨0, 72, .none⟩, .ldind .i2),
  (⟨0, 73, .none⟩, .ldind .u2), (⟨0, 74, .none⟩, .ldind .i4), (⟨0, 75, .none⟩, .ldind .u4),
  (⟨0, 76, .none⟩, .ldind .i8), (⟨0, 77, .none⟩, .ldind .i), (⟨0, 82, .none⟩, .stind .i1),
  (⟨0, 83, .none⟩, .stind .i2), (⟨0, 84, .none⟩, .stind .i4), (⟨0, 85, .none⟩, .stind .i8),
  (⟨0, 223, .none⟩, .stind .i),
  -- Array lengths and integer and class reference element loads and stores.
  (⟨0, 142, .none⟩, .ldlen), (⟨0, 144, .none⟩, .ldelem .i1), (⟨0, 145, .none⟩, .ldelem .u1),
  (⟨0, 146, .none⟩, .ldelem .i2), (⟨0, 147, .none⟩, .ldelem .u2), (⟨0, 148, .none⟩, .ldelem .i4),
  (⟨0, 149, .none⟩, .ldelem .u4), (⟨0, 150, .none⟩, .ldelem .i8), (⟨0, 151, .none⟩, .ldelem .i),
  (⟨0, 154, .none⟩, .ldelem_ref), (⟨0, 155, .none⟩, .stelem .i), (⟨0, 156, .none⟩, .stelem .i1),
  (⟨0, 157, .none⟩, .stelem .i2), (⟨0, 158, .none⟩, .stelem .i4), (⟨0, 159, .none⟩, .stelem .i8),
  (⟨0, 162, .none⟩, .stelem_ref),
  -- Arithmetic, bitwise operations and shifts.
  (⟨0, 88, .none⟩, .add), (⟨0, 89, .none⟩, .sub), (⟨0, 90, .none⟩, .mul), (⟨0, 91, .none⟩, .div),
  (⟨0, 92, .none⟩, .div_un), (⟨0, 93, .none⟩, .rem), (⟨0, 94, .none⟩, .rem_un),
  (⟨0, 95, .none⟩, .and), (⟨0, 96, .none⟩, .or), (⟨0, 97, .none⟩, .xor), (⟨0, 98, .none⟩, .shl),
  (⟨0, 99, .none⟩, .shr), (⟨0, 100, .none⟩, .shr_un), (⟨0, 101, .none⟩, .neg),
  (⟨0, 102, .none⟩, .not),
  -- Conversions.
  (⟨0, 103, .none⟩, .conv_i1), (⟨0, 104, .none⟩, .conv_i2), (⟨0, 105, .none⟩, .conv_i4),
  (⟨0, 106, .none⟩, .conv_i8), (⟨0, 109, .none⟩, .conv_u4), (⟨0, 110, .none⟩, .conv_u8),
  (⟨0, 209, .none⟩, .conv_u2), (⟨0, 210, .none⟩, .conv_u1), (⟨0, 211, .none⟩, .conv_i),
  (⟨0, 224, .none⟩, .conv_u),
  -- Overflow-checked conversions from an unsigned source.
  (⟨0, 130, .none⟩, .conv_ovf_un .i1), (⟨0, 131, .none⟩, .conv_ovf_un .i2),
  (⟨0, 132, .none⟩, .conv_ovf_un .i4), (⟨0, 133, .none⟩, .conv_ovf_un .i8),
  (⟨0, 134, .none⟩, .conv_ovf_un .u1), (⟨0, 135, .none⟩, .conv_ovf_un .u2),
  (⟨0, 136, .none⟩, .conv_ovf_un .u4), (⟨0, 137, .none⟩, .conv_ovf_un .u8),
  (⟨0, 138, .none⟩, .conv_ovf_un .i), (⟨0, 139, .none⟩, .conv_ovf_un .u),
  -- Overflow-checked conversions from a signed source.
  (⟨0, 179, .none⟩, .conv_ovf .i1), (⟨0, 180, .none⟩, .conv_ovf .u1),
  (⟨0, 181, .none⟩, .conv_ovf .i2), (⟨0, 182, .none⟩, .conv_ovf .u2),
  (⟨0, 183, .none⟩, .conv_ovf .i4), (⟨0, 184, .none⟩, .conv_ovf .u4),
  (⟨0, 185, .none⟩, .conv_ovf .i8), (⟨0, 186, .none⟩, .conv_ovf .u8),
  (⟨0, 212, .none⟩, .conv_ovf .i), (⟨0, 213, .none⟩, .conv_ovf .u),
  -- Overflow-checked arithmetic and comparisons.
  (⟨0, 214, .none⟩, .add_ovf), (⟨0, 215, .none⟩, .add_ovf_un), (⟨0, 216, .none⟩, .mul_ovf),
  (⟨0, 217, .none⟩, .mul_ovf_un), (⟨0, 218, .none⟩, .sub_ovf), (⟨0, 219, .none⟩, .sub_ovf_un),
  (⟨0, 65025, .none⟩, .ceq), (⟨0, 65026, .none⟩, .cgt), (⟨0, 65027, .none⟩, .cgt_un),
  (⟨0, 65028, .none⟩, .clt), (⟨0, 65029, .none⟩, .clt_un),
  -- Instance field accesses of a class and of a struct.
  (⟨0, 123, classOperand⟩, .ldfld classField), (⟨0, 124, classOperand⟩, .ldflda classField),
  (⟨0, 125, classOperand⟩, .stfld classField),
  (⟨0, 123, structOperand⟩, .ldfld structField), (⟨0, 124, structOperand⟩, .ldflda structField),
  (⟨0, 125, structOperand⟩, .stfld structField),
  -- Typed object operations.
  (⟨0, 0x70, .type int32⟩, .cpobj int32), (⟨0, 0x71, .type int32⟩, .ldobj int32),
  (⟨0, 0x81, .type int32⟩, .stobj int32), (⟨0, 0xfe15, .type int32⟩, .initobj int32),
  (⟨0, 0xfe1c, .type int32⟩, .sizeof int32),
  -- Dynamic frame storage.
  (⟨0, 65039, .none⟩, .localloc),
  -- Block copies and fills, at the default alignment and after `unaligned. 2`.
  (⟨0, 65047, .none⟩, .memory (.copyBlock 8)), (⟨0, 65048, .none⟩, .memory (.initBlock 8)),
  (⟨2, 65047, .none⟩, .memory (.copyBlock 2)), (⟨2, 65048, .none⟩, .memory (.initBlock 2)),
  -- Class type tests.
  (⟨0, 116, .type dog⟩, .castclass dog), (⟨0, 117, .type dog⟩, .isinst dog),
  -- Array allocations and element accesses that name their element type.
  (⟨0, 141, .type int32⟩, .newarr int32), (⟨0, 163, .type int32⟩, .ldelem_any int32),
  (⟨0, 164, .type int32⟩, .stelem_any int32), (⟨0, 143, .type int32⟩, .ldelema int32 false),
  -- Prefixes recorded by the following access, address or call.
  (⟨0, 65054, .none⟩, .nop), (⟨0, 65042, .integer 1⟩, .nop), (⟨0, 65042, .integer 2⟩, .nop),
  (⟨0, 65042, .integer 4⟩, .nop),
  (⟨0, 0xFE16, .type int32⟩, .nop),
  -- Calls and constructions, whose target the link at their pc gives.
  (⟨0, 40, .call callSite⟩, .call callSite.method),
  (⟨0, 111, .call instanceSite⟩, .callvirt instanceSite.method),
  (⟨0, 65030, .call { callSite with typeArguments := [int32], method.genericArity := 1 }⟩,
    .managed (.address ⟨"T::T.Account", 0x06000001, [callableType int32]⟩
      ⟨.void, [callableType int32]⟩)),
  (⟨0, 41, .indirectCall .void [int32] false false 0⟩,
    .managed (.call ⟨.void, [callableType int32]⟩ false)),
  (⟨6, 111, .call instanceSite⟩, .call instanceSite.method { constrained := some int32 }),
  (⟨0, 115, .call accountConstruction⟩, .newobj accountConstruction.method)]

/-- Constructors no opcode decodes to: the families outside the value opcodes. -/
def undecoded : List Name := [
  ``Instruction.throw,
  ``Instruction.unadmitted, ``Instruction.ldsfld, ``Instruction.ldsflda, ``Instruction.stsfld,
  ``Instruction.ldtoken]

/-- What each named opcode decodes to after its predecessor. -/
def decodedNamed : List (Option Instruction) :=
  named.map fun (raw, _) => Instruction.ofRaw? (predecessor raw) raw

/-- A string load binds its text and a metadata token needs a separate decoding rule. -/
theorem literal_operands :
    let literal : RawInstruction := ⟨0, 114, .text "original"⟩
    valueEncodingMatches none literal (.memory (.stringLiteral "original")) = true ∧
    valueEncodingMatches none literal (.memory (.stringLiteral "changed")) = false ∧
    valueEncodingMatches none literal .nop = false ∧
    scalarEmissionMatches none none literal [] (.memory (.stringLiteral "changed")) = false ∧
    scalarEmissionMatches none none literal [] .nop = false ∧
    Instruction.ofRaw? none ⟨0, 114, .none⟩ = none ∧
    Instruction.ofRaw? none ⟨0, 208, .type dog⟩ = none ∧
    Instruction.ofRaw? none ⟨0, 208, classOperand⟩ = none := by decide +kernel
#print axioms literal_operands

/-- Bare string loads accept ordinary escapes and BMP text, and reject unsupported characters
    anywhere in the literal. -/
theorem literal_characters :
    let decode := fun text => Instruction.ofRaw? none ⟨0, 114, .text text⟩
    let supported := "a\t\n\r\uFFFF"
    decode supported = some (.memory (.stringLiteral supported)) ∧
      decode "a\x08b" = none ∧ decode "a\x0cb" = none ∧
      decode (String.singleton (Char.ofNat 0x10000)) = none := by decide +kernel
#print axioms literal_characters

/-- Fold results bind their Boolean, branch target or exception. Direct and indirect tail calls
    carry the prefix at the previous pc. -/
theorem role_decodings :
    let tailPrefix : RawInstruction := ⟨0, 65044, .none⟩
    let branch : RawInstruction := ⟨1, 46, .target 9⟩
    let call : RawInstruction := ⟨2, 40, .call callSite⟩
    let indirect : RawInstruction := ⟨2, 41, .indirectCall .void [] false false 0⟩
    let decoded := fun role raw => Instruction.ofRole? role none raw
    decoded .head call = some .nop ∧ decoded .interior call = some .nop ∧
      decoded .head ⟨0, 20, .none⟩ = some .ldnull ∧
      decoded .interior ⟨0, 20, .none⟩ = some .ldnull ∧
      decoded .head ⟨0, 20, .integer 0⟩ = none ∧
      decoded .blocked call = none ∧ decoded (.result true) call = some (.ldc_i4 1) ∧
      decoded (.result false) call = some (.ldc_i4 0) ∧
      decoded (.typeBranch true) branch = some (.br 9) ∧
      decoded (.typeBranch true) branch ≠ some (.br 8) ∧
      decoded (.typeBranch false) branch = some .nop ∧
      decoded (.raise .argument) ⟨0, 122, .none⟩ = some (.throw .argument) ∧
      decoded (.raise .argument) ⟨0, 122, .none⟩ ≠ some (.throw .overflow) ∧
      decoded .argument ⟨0, 2, .none⟩ = some (.ldarg 0) ∧
      Instruction.ofRole? .tailCall (some tailPrefix) call =
        some (.call callSite.method { tail := true }) ∧
      Instruction.ofRole? .tailCall (some tailPrefix) indirect =
        some (.managed (.call ⟨.void, []⟩ true)) := by
  repeat' first | apply And.intro | rfl | (intro impossible; cases impossible)
#print axioms role_decodings

/-- Closing a generic owner supplies the identity at ldftn and the parameter type at calli. -/
theorem callable_substitution :
    let site := { callSite with method.owner := .parameter 0 }
    let indirect := RawOperand.indirectCall .void [.parameter 0] false false 0
    let closed := TypeExpr.object "T" "C"
    Instruction.ofRaw? none ⟨0, 65030, .call site⟩ = none ∧
      ((substituteOperand [closed] [] 0 (.call site)).bind fun operand =>
        Instruction.ofRaw? none ⟨0, 65030, operand⟩) =
          some (.managed (.address ⟨"T::C", 0x06000001, []⟩ ⟨.void, [callableType int32]⟩)) ∧
      ((substituteOperand [closed] [] 0 indirect).bind fun operand =>
        Instruction.ofRaw? none ⟨0, 41, operand⟩) =
          some (.managed (.call ⟨.void, [callableType closed]⟩ false)) ∧
      Instruction.ofRaw? none ⟨0, 41, .indirectCall .void [] false false 1⟩ = none := by
  decide +kernel
#print axioms callable_substitution

/-- Taking an instance method's address cannot produce a static parameterless pointer. -/
theorem instance_address_refused :
    let site := { callSite with
      declared := { convention := 0x20 },
      method := { callSite.method with name := name!"M", hasThis := true, parameters := [] },
      name := "M", parameterCount := 0 }
    Instruction.ofRaw? none ⟨0, 0xfe06, .call site⟩ = none := by decide +kernel
#print axioms instance_address_refused

/-- A reachable folded argument load names a declared argument and emits its encoded index. -/
theorem folded_argument_index (localCount index : Nat) (argumentAt : Nat → Option StorageType)
    (homeAt : Nat → Option Nat) (emitted : Instruction) :
    validateArgumentOpAt localCount argumentAt homeAt (.load index) true emitted = true ↔
      (argumentAt index).isSome = true ∧ emitted = .ldarg index := by
  cases found : argumentAt index <;> cases emitted <;> simp [validateArgumentOpAt, found]
#print axioms folded_argument_index

/-- Raw instructions over every one-byte and two-byte opcode with each operand kind the value
    family reads, plus text, a type, a class field and a call site; `ofRaw?` must give `none`
    for every opcode outside `Instruction.valueOpcode`. -/
def probes : List RawInstruction :=
  ((List.range 256 ++ (List.range 32).map (65024 + ·)).flatMap fun opcode =>
    ([.none, .integer 1, .argument 1, .local 1, .target 1, .targets [1], .text "",
      .type (.atom runtimeScope
        "System.Int32"), classOperand, .call callSite] : List RawOperand).map
      fun operand => { offset := 0, opcode, operand })

/-- `ofRaw?` decodes only value opcodes, every value opcode is named, and every named form
    decodes to exactly the instruction ECMA-335 assigns it. -/
theorem ofRaw?_exact :
    probes.all (fun raw =>
      (Instruction.ofRaw? none raw).isNone || Instruction.valueOpcode raw.opcode) = true ∧
    probes.all (fun raw => !Instruction.valueOpcode raw.opcode ||
      named.any (·.1.opcode == raw.opcode)) = true ∧
    named.all (fun (raw, expected) => valueEncodingMatches (predecessor raw) raw expected) =
      true := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.ofRaw?_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofRaw?_exact

/-- The alignments an `unaligned.` prefix states. -/
private def alignments : List Int := [1, 2, 4]

/-- Every indirect load and store opcode the decoder admits, with the instruction it gives. -/
private def indirectAccesses : List (RawInstruction × Instruction) := [
  (⟨1, 70, .none⟩, .ldind .i1), (⟨1, 71, .none⟩, .ldind .u1), (⟨1, 72, .none⟩, .ldind .i2),
  (⟨1, 73, .none⟩, .ldind .u2), (⟨1, 74, .none⟩, .ldind .i4), (⟨1, 75, .none⟩, .ldind .u4),
  (⟨1, 76, .none⟩, .ldind .i8), (⟨1, 77, .none⟩, .ldind .i), (⟨1, 82, .none⟩, .stind .i1),
  (⟨1, 83, .none⟩, .stind .i2), (⟨1, 84, .none⟩, .stind .i4), (⟨1, 85, .none⟩, .stind .i8),
  (⟨1, 223, .none⟩, .stind .i)]

/-- After `unaligned.` of each alignment, every indirect load and store decodes to the
    instruction it decodes to alone, so the instruction carries no alignment. -/
theorem unaligned_indirect_unchanged :
    indirectAccesses.all (fun (raw, decoded) => alignments.all fun alignment =>
      Instruction.ofRaw? (some ⟨0, 65042, .integer alignment⟩) raw == some decoded) = true := by
  decide +kernel
#print axioms unaligned_indirect_unchanged

/-- `cpblk` and `initblk` decode at alignment 8 with nothing before them, at the operand of an
    `unaligned.` 1, 2 or 4 before them, and at 8 after an instruction that is not a prefix,
    whatever integer operand it carries. -/
theorem block_alignments :
    let copy : RawInstruction := ⟨2, 65047, .none⟩
    let fill : RawInstruction := ⟨2, 65048, .none⟩
    let aligned (alignment : Int) : Option RawInstruction := some ⟨0, 0xfe12, .integer alignment⟩
    let constant (value : Int) : Option RawInstruction := some ⟨0, 0x1f, .integer value⟩
    (Instruction.ofRaw? none copy == some (.memory (.copyBlock 8)) &&
      Instruction.ofRaw? none fill == some (.memory (.initBlock 8)) &&
      Instruction.ofRaw? (aligned 1) copy == some (.memory (.copyBlock 1)) &&
      Instruction.ofRaw? (aligned 2) copy == some (.memory (.copyBlock 2)) &&
      Instruction.ofRaw? (aligned 4) copy == some (.memory (.copyBlock 4)) &&
      Instruction.ofRaw? (aligned 1) fill == some (.memory (.initBlock 1)) &&
      Instruction.ofRaw? (aligned 2) fill == some (.memory (.initBlock 2)) &&
      Instruction.ofRaw? (aligned 4) fill == some (.memory (.initBlock 4)) &&
      Instruction.ofRaw? (constant 1) copy == some (.memory (.copyBlock 8)) &&
      Instruction.ofRaw? (constant 2) copy == some (.memory (.copyBlock 8)) &&
      Instruction.ofRaw? (constant 4) copy == some (.memory (.copyBlock 8)) &&
      Instruction.ofRaw? (constant 1) fill == some (.memory (.initBlock 8)) &&
      Instruction.ofRaw? (constant 2) fill == some (.memory (.initBlock 8)) &&
      Instruction.ofRaw? (constant 4) fill == some (.memory (.initBlock 8))) = true := by
  decide +kernel
#print axioms block_alignments

/-- Only a valid unaligned prefix before an object load or store preserves its decoding. -/
theorem object_prefixes :
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1") int32
    let pair := TypeExpr.aggregate "Pair" 0
    let types := [int32, .enum "Signed8" (.atom runtimeScope "System.SByte"), pair, span] ++
      [128, 256, 512].map (fun bits =>
        .apply (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{bits}`1") int32)
    let check := fun (operand : RawOperand) (type : TypeExpr) =>
      let rows : List (Nat × Option Instruction) := [(0x70, some (.cpobj type)),
        (0x71, some (.ldobj type)), (0x81, some (.stobj type)),
        (0xfe15, some (.initobj type)),
        (0xfe1c, some (.sizeof type))]
      rows.all fun (opcode, expected) =>
      let raw : RawInstruction := ⟨3, opcode, operand⟩
      Instruction.ofRaw? none raw == expected && alignments.all (fun alignment =>
        Instruction.ofRaw? (some ⟨0, 0xfe12, .integer alignment⟩) raw ==
          (if opcode ∈ [0x71, 0x81] then expected else none)) &&
        ([⟨0, 0xfe12, .integer 8⟩, ⟨0, 0xfe13, .none⟩, ⟨0, 0xfe14, .none⟩,
          ⟨0, 0xfe16, .type type⟩, ⟨0, 0xfe19, .integer 1⟩, ⟨0, 0xfe1e, .none⟩]
          : List RawInstruction).all (fun modifier =>
            (Instruction.ofRaw? (some modifier) raw).isNone)
    types.all (fun type => check (.type type) type) &&
      (substituteOperand [pair] [] 1 (.type (.parameter 0))).any (check · pair) := by decide +kernel
#print axioms object_prefixes

/-- A direct call retains the tail transfer or the static dispatch receiver named by its prefix. -/
theorem direct_call_prefixes :
    let raw : RawInstruction := ⟨3, 40, .call callSite⟩
    let slot := { callSite with staticVirtualInterfaceSlot := true }
    valueEncodingMatches (some ⟨0, 0xFE14, .none⟩) raw (.call callSite.method { tail := true }) &&
    valueEncodingMatches (some ⟨0, 0xFE16, .type int32⟩) { raw with operand := .call slot }
      (.call callSite.method { constrained := some int32 }) := by
  decide +kernel
#print axioms direct_call_prefixes

/-- Both constrained call forms decode to the prefix pc and the slot with its receiver. -/
theorem constrained_call_windows :
    let modifier : RawInstruction := ⟨0, 0xFE16, .type int32⟩
    let staticSite := { callSite with staticVirtualInterfaceSlot := true }
    Instruction.ofRawCode none [modifier, ⟨6, 111, .call instanceSite⟩] =
      [.nop, .call instanceSite.method { constrained := some int32 }] ∧
    Instruction.ofRawCode none [modifier, ⟨6, 40, .call staticSite⟩] =
      [.nop, .call callSite.method { constrained := some int32 }] := by
  exact ⟨rfl, rfl⟩
#print axioms constrained_call_windows

/-- Invalid constrained windows fail the method prefix check, including at the end of a body. -/
theorem invalid_constrained_windows :
    let modifier : RawInstruction := ⟨0, 0xFE16, .type int32⟩
    let instanceCall : RawInstruction := ⟨6, 111, .call instanceSite⟩
    let staticSite := { callSite with staticVirtualInterfaceSlot := true }
    let windows := [[modifier, ⟨6, 111, .call staticSite⟩],
      [modifier, ⟨6, 40, .call instanceSite⟩],
      [modifier, ⟨6, 0, .none⟩], [⟨0, 0xFE1E, .none⟩, modifier, instanceCall], [modifier],
      [{ modifier with operand := .integer 1 }, instanceCall],
      [⟨0, 0xFE14, .none⟩, modifier, instanceCall, ⟨11, 42, .none⟩]]
    windows.all (fun code => !rawPrefixesValid .void code) &&
      (Instruction.ofRaw? (some ⟨0, 0xFE14, .none⟩) instanceCall).isNone := by
  decide +kernel
#print axioms invalid_constrained_windows

/-- Suppressed checks have no scalar emission for any byte operand. -/
theorem no_prefix_refused :
    (List.range 256).all (fun flags =>
      !scalarEmissionMatches none none ⟨0, 0xFE19, .integer flags⟩ [] .nop) = true := by
  decide +kernel
#print axioms no_prefix_refused

/-- Reserved check flags cannot authorize an ordinary instance field load. -/
theorem malformed_field_prefix_refused :
    let previous := some (⟨0, 0xFE19, .integer 255⟩ : RawInstruction)
    [(classOperand, classField, ScalarKind.object), (structOperand, structField, .reference)].all
      (fun (operand, field, receiver) =>
        let raw : RawInstruction := ⟨3, 123, operand⟩
        (Instruction.ofRaw? previous raw).isNone &&
          !scalarEmissionMatches none previous raw [receiver] (.ldfld field)) := by
  decide +kernel
#print axioms malformed_field_prefix_refused

/-- A typed indirect load or store binds both its type token and its preceding alignment. -/
theorem indirect_object_binding :
    let other := TypeExpr.atom runtimeScope "System.UInt64"
    let unaligned := fun (n : Int) => some (RawInstruction.mk 0 0xfe12 (.integer n))
    [(0x71, Instruction.ldobj), (0x81, Instruction.stobj)].all fun (opcode, operation) =>
      let raw := RawInstruction.mk 3 opcode (.type int32)
      indirectAccessMatches none raw (operation int32) &&
        [1, 2, 4].all (fun n => indirectAccessMatches (unaligned n) raw (operation int32)) &&
        !indirectAccessMatches none raw (operation other) &&
        !indirectAccessMatches none ⟨3, 0, .none⟩ (operation int32) &&
        !indirectAccessMatches (unaligned 8) raw (operation int32) := by decide +kernel
#print axioms indirect_object_binding

/-- A forged operand on a block copy cannot emit the aligned copy at its taker. -/
theorem malformed_block_operand_refused :
    !indirectAccessMatches (some ⟨0, 0xFE12, .integer 1⟩)
      ⟨3, 0xFE17, .integer 1⟩ (.memory (.copyBlock 1)) := by
  decide +kernel
#print axioms malformed_block_operand_refused

/-- Supported memory and call prefixes pass whole-body validation with their takers. -/
theorem valid_prefix_sequences :
    let ret : RawInstruction := ⟨8, 42, .none⟩
    let call : RawInstruction := ⟨3, 40, .call callSite⟩
    let instanceSite := { callSite with method := { callSite.method with hasThis := true } }
    let tailCall : RawInstruction := ⟨0, 0xFE14, .none⟩
    let constrainedCall : RawInstruction := ⟨0, 0xFE16, .type int32⟩
    alignments.all (fun alignment => indirectAccesses.all fun (raw, _) =>
      prefixSequenceValid .void [⟨0, 0xFE12, .integer alignment⟩, raw]) &&
    prefixSequenceValid .void [⟨0, 0xFE12, .integer 2⟩, ⟨3, 123, classOperand⟩] &&
    prefixSequenceValid .void [⟨0, 0xFE1E, .none⟩, ⟨2, 143, .type int32⟩] &&
    prefixSequenceValid .void [tailCall, call, ret] &&
    prefixSequenceValid .void [tailCall, ⟨2, 41, .indirectCall .void [] false false 0⟩, ret] &&
    prefixSequenceValid .void [constrainedCall,
      { call with operand := .call { callSite with staticVirtualInterfaceSlot := true } }] &&
    prefixSequenceValid .void [constrainedCall, ⟨6, 111, .call instanceSite⟩] := by
  decide +kernel
#print axioms valid_prefix_sequences

/-- A class field and a struct field, each with the reference it decodes to. -/
private def fieldOperands : List (RawOperand × FieldRef) :=
  [(classOperand, classField), (structOperand, structField)]

/-- After `unaligned.` of each alignment, `ldfld` and `stfld` of a class or a struct field decode
    to the instruction they decode to alone, so a field access carries no alignment. -/
theorem unaligned_fields_unchanged :
    fieldOperands.all (fun (operand, field) => alignments.all fun alignment =>
      Instruction.ofRaw? (some ⟨0, 65042, .integer alignment⟩) ⟨1, 123, operand⟩ ==
          some (.ldfld field) &&
        Instruction.ofRaw? (some ⟨0, 65042, .integer alignment⟩) ⟨1, 125, operand⟩ ==
          some (.stfld field)) = true := by
  decide +kernel
#print axioms unaligned_fields_unchanged

/-- `ldflda` after `unaligned.`, which ECMA-335 does not let that prefix precede, and `ldfld`,
    `ldflda` and `stfld` after `volatile.` do not decode, on a class or a struct field. -/
theorem prefixed_fields_refused :
    fieldOperands.all (fun (operand, _) =>
      alignments.all (fun alignment =>
        (Instruction.ofRaw? (some ⟨0, 65042, .integer alignment⟩) ⟨1, 124, operand⟩).isNone) &&
      [123, 124, 125].all fun opcode =>
        (Instruction.ofRaw? (some ⟨0, 65043, .none⟩) ⟨1, opcode, operand⟩).isNone) = true := by
  decide +kernel
#print axioms prefixed_fields_refused

/-- The `readonly.` prefix with no operand, the form it takes. -/
private def readOnlyPrefix : RawInstruction := ⟨0, 65054, .none⟩

/-- Each prefix other than `readonly.`, with an operand of the form it takes. -/
private def otherPrefixes : List RawInstruction :=
  [⟨0, 65042, .integer 1⟩, ⟨0, 65043, .none⟩, ⟨0, 65044, .none⟩, ⟨0, 65046, .type int32⟩,
    ⟨0, 65049, .integer 1⟩]

/-- `ldelema` records whether `readonly.` precedes it and decodes after no other prefix, and
    `readonly.` decodes to `nop` after no prefix at all. -/
theorem prefixed_address :
    (Instruction.ofRaw? (some readOnlyPrefix) ⟨1, 143, .type int32⟩ ==
        some (.ldelema int32 true) &&
      otherPrefixes.all (fun before =>
        (Instruction.ofRaw? (some before) ⟨1, 143, .type int32⟩).isNone) &&
      (readOnlyPrefix :: otherPrefixes).all (fun before =>
        (Instruction.ofRaw? (some before) ⟨1, 65054, .none⟩).isNone)) = true := by
  decide +kernel
#print axioms prefixed_address

/-- After `readonly.`, no probe decodes except `ldelema`, whatever its operand. -/
theorem readOnly_only_address :
    probes.all (fun raw => raw.opcode == 143 ||
      (Instruction.ofRaw? (some readOnlyPrefix) raw).isNone) = true := by
  decide +kernel
#print axioms readOnly_only_address

/-- Emitted instructions that differ from what the raw instruction decodes to: a constant out of
    its form's range, another operand, or another constructor with the same stack effect. -/
def mutations : List (RawInstruction × Instruction) := [
  -- Constants just past the range of their form, far past it, or of another width.
  (⟨0, 31, .integer 128⟩, .ldc_i4 128),
  (⟨0, 32, .integer (-(2^31) - 1)⟩, .ldc_i4 (BitVec.ofInt 32 (-(2^31) - 1))),
  (⟨0, 33, .integer (-(2^63) - 1)⟩, .ldc_i8 (BitVec.ofInt 64 (-(2^63) - 1))),
  (⟨0, 31, .integer (-129)⟩, .ldc_i4 (BitVec.ofInt 32 (-129))),
  (⟨0, 32, .integer (2^31)⟩, .ldc_i4 (BitVec.ofInt 32 (2^31))),
  (⟨0, 33, .integer (2^63)⟩, .ldc_i8 (BitVec.ofInt 64 (2^63))),
  (⟨0, 33, .integer (-1)⟩, .ldc_i4 (BitVec.ofInt 32 (-1))),
  -- Another constant, argument, local or target than the operand names.
  (⟨0, 25, .none⟩, .ldc_i4 2), (⟨0, 31, .integer (-5)⟩, .ldc_i4 5),
  (⟨0, 16, .argument 1⟩, .starg 2), (⟨0, 65034, .argument 300⟩, .ldarga 299),
  (⟨0, 6, .none⟩, .ldloc 1), (⟨0, 65036, .local 300⟩, .ldloc 299),
  (⟨0, 43, .target 1⟩, .br 2), (⟨0, 69, .targets [1, 2]⟩, .switch [2, 1]),
  (⟨0, 69, .targets [1, 2]⟩, .switch [1, 2, 3]),
  -- Another constructor with the same stack effect.
  (⟨0, 88, .none⟩, .sub), (⟨0, 38, .none⟩, .stloc 0), (⟨0, 19, .local 4⟩, .ldloc 4),
  (⟨0, 18, .local 4⟩, .ldloc 4), (⟨0, 16, .argument 4⟩, .stloc 4),
  (⟨0, 15, .argument 4⟩, .ldloca 4), (⟨0, 58, .target 1⟩, .brfalse 1),
  (⟨0, 138, .none⟩, .conv_ovf_un .i8), (⟨0, 211, .none⟩, .conv_i8),
  (⟨0, 130, .none⟩, .conv_ovf .i1), (⟨0, 215, .none⟩, .add_ovf), (⟨0, 65027, .none⟩, .cgt),
  (⟨0, 144, .none⟩, .ldelem .u1), (⟨0, 144, .none⟩, .ldelem .i2),
  (⟨0, 148, .none⟩, .ldelem .u4), (⟨0, 151, .none⟩, .ldelem .i8), (⟨0, 155, .none⟩, .stelem .i8),
  (⟨0, 154, .none⟩, .ldelem .i), (⟨0, 162, .none⟩, .stelem .i), (⟨0, 74, .none⟩, .ldelem .i4),
  (⟨0, 84, .none⟩, .stelem .i4), (⟨0, 148, .none⟩, .ldind .i4), (⟨0, 142, .none⟩, .ldind .i),
  -- A local or argument index wider than its form encodes.
  (⟨0, 17, .local 256⟩, .ldloc 256), (⟨0, 65036, .local 65536⟩, .ldloc 65536),
  (⟨0, 14, .argument 256⟩, .ldarg 256), (⟨0, 65033, .argument 65536⟩, .ldarg 65536),
  (⟨0, 15, .argument 256⟩, .ldarga 256), (⟨0, 65034, .argument 65536⟩, .ldarga 65536),
  (⟨0, 16, .argument 256⟩, .starg 256), (⟨0, 65035, .argument 65536⟩, .starg 65536),
  -- A malformed operand, another argument, an argument address, or an opcode outside the family.
  (⟨0, 42, .integer 0⟩, .ret), (⟨0, 17, .argument 4⟩, .ldloc 4), (⟨0, 6, .local 0⟩, .ldloc 0),
  (⟨0, 43, .targets [1]⟩, .br 1), (⟨0, 2, .none⟩, .ldarg 1), (⟨0, 15, .argument 1⟩, .ldarg 1),
  (⟨0, 107, .none⟩, .conv_i4), (⟨0, 65039, .integer 0⟩, .localloc),
  (⟨0, 116, .none⟩, .castclass dog), (⟨0, 20, .type dog⟩, .ldnull), (⟨0, 20, .none⟩, .ldc_i4 0),
  (⟨0, 142, .integer 0⟩, .ldlen), (⟨0, 154, .type dog⟩, .ldelem_ref),
  -- Another element type than the token names, the other direction, or a missing token.
  (⟨0, 141, .type int32⟩, .newarr dog), (⟨0, 163, .type int32⟩, .ldelem_any dog),
  (⟨0, 163, .type int32⟩, .stelem_any int32), (⟨0, 164, .type int32⟩, .ldelem_any int32),
  (⟨0, 143, .type int32⟩, .ldelema dog false), (⟨0, 143, .type int32⟩, .ldelema int32 true),
  (⟨0, 143, .none⟩, .ldelema int32 false), (⟨0, 65054, .integer 0⟩, .nop),
  (⟨0, 163, .none⟩, .ldelem_any int32), (⟨0, 148, .none⟩, .ldelem_any int32),
  (⟨0, 158, .none⟩, .stelem_any int32), (⟨0, 141, .none⟩, .newarr int32),
  -- Another field, another access to the field, a static field or another owner.
  (⟨0, 123, classOperand⟩, .ldfld { classField with index := 2 }),
  (⟨0, 123, classOperand⟩, .ldfld { classField with name := name!"limit" }),
  (⟨0, 123, classOperand⟩, .ldflda classField), (⟨0, 125, classOperand⟩, .ldfld classField),
  (⟨0, 123, .field (.object "T" "T.Account") 1 (.atom runtimeScope "System.Int32")
    name!"balance" true⟩, .ldfld classField),
  (⟨0, 123, structOperand⟩, .ldfld classField), (⟨0, 123, classOperand⟩, .ldfld structField),
  (⟨0, 125, structOperand⟩,
    .stfld { structField with type := .atom runtimeScope "System.UInt32" }),
  -- Another method or constructor than the site names, a prefix the bytes do not hold, or a call
  -- operand under another opcode.
  (⟨0, 40, .call callSite⟩, .call { callSite.method with name := name!"Withdraw" }),
  (⟨0, 40, .call callSite⟩, .call callSite.method { tail := true }),
  (⟨0, 40, .call callSite⟩, .call callSite.method { constrained := some dog }),
  (⟨0, 40, .none⟩, .call callSite.method),
  (⟨0, 111, .call callSite⟩, .call callSite.method),
  (⟨0, 115, .call accountConstruction⟩,
    .newobj { accountConstruction.method with parameters := [] }),
  (⟨0, 115, .call accountConstruction⟩,
    .newobj { accountConstruction.method with owner := .object "T" "T.Other" }),
  (⟨0, 40, .call accountConstruction⟩, .newobj accountConstruction.method)]

/-- No mutation matches its raw instruction. -/
theorem mutations_rejected :
    mutations.all (fun (raw, emitted) => !valueEncodingMatches none raw emitted) = true := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.mutations_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mutations_rejected

/-- An int32 array of the extraction's stack kinds. -/
private def words : ScalarKind := .array .signed32

/-- An array opcode the decoder reads emits only its decoding: the managed table length is
    refused, an opcode of a kind emits no typed form, and a typed opcode emits its token's element
    type rather than a kind. -/
theorem element_emission_exact :
    scalarEmissionMatches none none ⟨0, 148, .none⟩ [.word32, words] (.ldelem .i4) = true ∧
    scalarEmissionMatches none none ⟨0, 158, .none⟩ [.word32, .word32, words] (.stelem .i4) =
      true ∧
    scalarEmissionMatches none none ⟨0, 142, .none⟩ [words] .ldlen = true ∧
    scalarEmissionMatches none none ⟨0, 163, .type int32⟩ [.word32, words]
      (.ldelem_any int32) =
      true ∧
    scalarEmissionMatches none none ⟨0, 164, .type int32⟩ [.word32, .word32, words]
      (.stelem_any int32) = true ∧
    scalarEmissionMatches none none ⟨0, 148, .none⟩ [.word32, words]
      (.ldelem_any int32) = false ∧
    scalarEmissionMatches none none ⟨0, 158, .none⟩ [.word32, .word32, words]
      (.stelem_any int32) = false ∧
    scalarEmissionMatches none none ⟨0, 148, .none⟩ [.word32, words] (.ldelem .u4) = false ∧
    scalarEmissionMatches none none ⟨0, 142, .none⟩ [words] (.ldind .i) = false ∧
    scalarEmissionMatches none none ⟨0, 163, .type int32⟩ [.word32, words]
      (.ldelem .i4) = false ∧
    scalarEmissionMatches none none ⟨0, 164, .type int32⟩ [.word32, .word32, words]
      (.stelem .i4) = false := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.element_emission_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms element_emission_exact

/-- A decided match gives the decoded instruction, sign extension of a short constant included. -/
theorem short_constant_decoded :
    Instruction.ofRaw? none ⟨0, 31, .integer (-5)⟩ = some (.ldc_i4 (BitVec.ofInt 32 (-5))) :=
  valueEncodingMatches_sound (by decide +kernel)

/-- info: 'Tests.ValueDecoding.short_constant_decoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms short_constant_decoded

/-- info: 'CIL.Instruction.valueOpcode_of_ofRaw?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Instruction.valueOpcode_of_ofRaw?

/-- info: 'CIL.Instruction.sameValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Instruction.sameValue_eq

/-- info: 'CIL.Extraction.valueEncodingMatches_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valueEncodingMatches_sound

/--
info: 'CIL.Instruction.ofRaw?_substitute' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Instruction.ofRaw?_substitute

/-- Instantiating the type operand of a refused isinst preserves its refusal. -/
theorem substitute_refused_type :
    let previous := some (⟨0, 0xFE1E, .none⟩ : RawInstruction)
    let raw : RawInstruction := ⟨2, 117, .type (.parameter 0)⟩
    Instruction.ofRaw? previous raw = none ∧
      Instruction.ofRaw? previous { raw with operand := .type int32 } = none := by
  intro previous raw
  constructor
  · rfl
  · exact Instruction.ofRaw?_substitute (previous := previous) (raw := raw)
      (operand := .type int32) (arguments := [int32]) (layouts := []) (arity := 1) rfl rfl
#print axioms substitute_refused_type

/-- `classOperand` holding the first generic argument instead of `int32`. -/
private def genericOperand : RawOperand :=
  .field (.object "T" "T.Account") 1 (.parameter 0) name!"balance" false

-- Instantiating a class field with `int32` decodes to the access of `classField`.
example : ((substituteOperand [.atom runtimeScope "System.Int32"] [] 0 genericOperand).bind
    (fun operand => Instruction.ofRaw? none ⟨0, 123, operand⟩)).any
      (·.sameValue (.ldfld classField)) = true := by
  decide +kernel

/-- `structOperand` holding the first generic argument instead of `int32`. -/
private def genericStructOperand : RawOperand :=
  .field (.aggregate "T::Pair" 0) 1 (.parameter 0) name!"balance" false

-- Instantiating a struct field with `int32` decodes to the access of `structField`.
example : ((substituteOperand [.atom runtimeScope "System.Int32"] [] 0 genericStructOperand).bind
    (fun operand => Instruction.ofRaw? none ⟨0, 125, operand⟩)).any
      (·.sameValue (.stfld structField)) = true := by
  decide +kernel

/--
info: 'CIL.Instruction.ofRaw?_substitute_instance_field' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Instruction.ofRaw?_substitute_instance_field

/-- The constructor at the head of each decoded named opcode, failing on any `none`. -/
private def decodedHeads : MetaM (List Name) := do
  let mut list ← whnf (mkConst ``decodedNamed)
  let mut heads := []
  while list.isAppOfArity ``List.cons 3 do
    let value ← whnf (list.getArg! 1)
    unless value.isAppOfArity ``Option.some 2 do
      throwError "a named opcode does not decode: {value}"
    let some name := (← whnf (value.getArg! 1)).getAppFn.constName?
      | throwError "decoded value has no constructor head"
    heads := name :: heads
    list ← whnf (list.getArg! 2)
  return heads

/-- info: decoded 92, undecoded 6 of 98 constructors -/
#guard_msgs in
run_meta do
  let constructors := (← getConstInfoInduct ``Instruction).ctors
  let decoded := (← decodedHeads).eraseDups
  let missing := constructors.filter fun name => !decoded.contains name && !undecoded.contains name
  let overlap := undecoded.filter decoded.contains
  let stale := undecoded.filter fun name => !constructors.contains name
  unless missing.isEmpty && overlap.isEmpty && stale.isEmpty do
    throwError "unplaced constructors {missing}; listed but decoded {overlap}; \
      listed but absent {stale}"
  unless decoded.length + undecoded.length == constructors.length do
    throwError "decoded {decoded.length} + listed {undecoded.length} != {constructors.length}"
  logInfo m!"decoded {decoded.length}, undecoded {undecoded.length} of \
    {constructors.length} constructors"

end Tests.ValueDecoding
