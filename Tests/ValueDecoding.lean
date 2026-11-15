import CIL

/-!
# Value decoding coverage

Every `CIL.Instruction` constructor is produced by `Instruction.ofRaw?` for a named opcode or is
listed as one that no opcode decodes to, `ofRaw?` decodes exactly the named opcodes, and an
emitted instruction that differs from the decoded one in constructor, operand or operand range
does not match.
-/

namespace Tests.ValueDecoding

open CIL CIL.Extraction Lean Meta

/-- The class the type test rows name. -/
private def dog : TypeExpr := .object "Fixture" "Fixture.Dog"

/-- One raw instruction per value opcode, every short, long and macro form, with the instruction
    ECMA-335 assigns it; constants include the extremes of each form's range and locals the largest
    index each width encodes. -/
def named : List (RawInstruction × Instruction) := [
  -- Stack shuffling and return.
  (⟨0, 0, .none⟩, .nop), (⟨0, 37, .none⟩, .dup), (⟨0, 38, .none⟩, .pop), (⟨0, 42, .none⟩, .ret),
  -- Constants.
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
  -- Dynamic frame storage.
  (⟨0, 65039, .none⟩, .localloc),
  -- Class type tests.
  (⟨0, 116, .type dog⟩, .castclass dog), (⟨0, 117, .type dog⟩, .isinst dog)]

/-- Constructors no opcode decodes to: the families outside the value opcodes. -/
def undecoded : List Name := [
  ``Instruction.newarr, ``Instruction.loadAggregate,
  ``Instruction.copyObject, ``Instruction.storeAggregate,
  ``Instruction.initAggregate, ``Instruction.loadScalar, ``Instruction.storeScalar,
  ``Instruction.fieldAt, ``Instruction.fieldAddress, ``Instruction.setFieldAt,
  ``Instruction.aggregateFieldAt, ``Instruction.setAggregateFieldAt,
  ``Instruction.initializeSpanLocal, ``Instruction.tailCall, ``Instruction.managed,
  ``Instruction.call, ``Instruction.callInstance,
  ``Instruction.callVirtual, ``Instruction.newAggregate, ``Instruction.newObject,
  ``Instruction.skipInit, ``Instruction.feature,
  ``Instruction.intrinsic, ``Instruction.memory, ``Instruction.throw,
  ``Instruction.unadmitted]

/-- What each named opcode decodes to. -/
def decodedNamed : List (Option Instruction) := named.map (Instruction.ofRaw? ·.1)

/-- Raw instructions over every one-byte and two-byte opcode with each operand kind the value
    family reads, plus text and a type; `ofRaw?` must give `none` for every opcode outside
    `Instruction.valueOpcode`. -/
def probes : List RawInstruction :=
  ((List.range 256 ++ (List.range 32).map (65024 + ·)).flatMap fun opcode =>
    ([.none, .integer 1, .argument 1, .local 1, .target 1, .targets [1], .text "",
      .type (.atom runtimeScope "System.Int32")] : List RawOperand).map
      fun operand => { offset := 0, opcode, operand })

/-- `ofRaw?` decodes only value opcodes, every value opcode is named, and every named form
    decodes to exactly the instruction ECMA-335 assigns it. -/
theorem ofRaw?_exact :
    probes.all (fun raw =>
      (Instruction.ofRaw? raw).isNone || Instruction.valueOpcode raw.opcode) = true ∧
    probes.all (fun raw => !Instruction.valueOpcode raw.opcode ||
      named.any (·.1.opcode == raw.opcode)) = true ∧
    named.all (fun (raw, expected) => valueEncodingMatches raw expected) = true := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.ofRaw?_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofRaw?_exact

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
  (⟨0, 88, .none⟩, .sub), (⟨0, 38, .none⟩, .skipInit), (⟨0, 19, .local 4⟩, .ldloc 4),
  (⟨0, 18, .local 4⟩, .ldloc 4), (⟨0, 16, .argument 4⟩, .stloc 4),
  (⟨0, 15, .argument 4⟩, .ldloca 4), (⟨0, 58, .target 1⟩, .brfalse 1),
  (⟨0, 138, .none⟩, .conv_ovf_un .i8), (⟨0, 211, .none⟩, .conv_i8),
  (⟨0, 130, .none⟩, .conv_ovf .i1), (⟨0, 215, .none⟩, .add_ovf), (⟨0, 65027, .none⟩, .cgt),
  -- A local or argument index wider than its form encodes.
  (⟨0, 17, .local 256⟩, .ldloc 256), (⟨0, 65036, .local 65536⟩, .ldloc 65536),
  (⟨0, 14, .argument 256⟩, .ldarg 256), (⟨0, 65033, .argument 65536⟩, .ldarg 65536),
  (⟨0, 15, .argument 256⟩, .ldarga 256), (⟨0, 65034, .argument 65536⟩, .ldarga 65536),
  (⟨0, 16, .argument 256⟩, .starg 256), (⟨0, 65035, .argument 65536⟩, .starg 65536),
  -- A malformed operand, another argument, an argument address, or an opcode outside the family.
  (⟨0, 42, .integer 0⟩, .ret), (⟨0, 17, .argument 4⟩, .ldloc 4), (⟨0, 6, .local 0⟩, .ldloc 0),
  (⟨0, 43, .targets [1]⟩, .br 1), (⟨0, 2, .none⟩, .ldarg 1), (⟨0, 15, .argument 1⟩, .ldarg 1),
  (⟨0, 107, .none⟩, .conv_i4), (⟨0, 65039, .integer 0⟩, .localloc),
  (⟨0, 116, .none⟩, .castclass dog), (⟨0, 20, .type dog⟩, .ldnull), (⟨0, 20, .none⟩, .ldc_i4 0)]

/-- No mutation matches its raw instruction. -/
theorem mutations_rejected :
    mutations.all (fun (raw, emitted) => !valueEncodingMatches raw emitted) = true := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.mutations_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mutations_rejected

/-- A decided match gives the decoded instruction, sign extension of a short constant included. -/
theorem short_constant_decoded :
    Instruction.ofRaw? ⟨0, 31, .integer (-5)⟩ = some (.ldc_i4 (BitVec.ofInt 32 (-5))) :=
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

/-- info: decoded 70, undecoded 26 of 96 constructors -/
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
