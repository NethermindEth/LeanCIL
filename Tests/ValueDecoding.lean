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

/-- One raw instruction per value opcode, every short, long and macro form. -/
def namedOpcodes : List RawInstruction := [
  ⟨0, 0, .none⟩, ⟨0, 37, .none⟩, ⟨0, 38, .none⟩, ⟨0, 42, .none⟩,
  ⟨0, 21, .none⟩, ⟨0, 22, .none⟩, ⟨0, 23, .none⟩, ⟨0, 24, .none⟩, ⟨0, 25, .none⟩,
  ⟨0, 26, .none⟩, ⟨0, 27, .none⟩, ⟨0, 28, .none⟩, ⟨0, 29, .none⟩, ⟨0, 30, .none⟩,
  ⟨0, 31, .integer (-5)⟩, ⟨0, 32, .integer 70000⟩, ⟨0, 33, .integer (-1)⟩,
  ⟨0, 6, .none⟩, ⟨0, 7, .none⟩, ⟨0, 8, .none⟩, ⟨0, 9, .none⟩, ⟨0, 17, .local 4⟩,
  ⟨0, 65036, .local 300⟩,
  ⟨0, 10, .none⟩, ⟨0, 11, .none⟩, ⟨0, 12, .none⟩, ⟨0, 13, .none⟩, ⟨0, 19, .local 4⟩,
  ⟨0, 65038, .local 300⟩, ⟨0, 18, .local 4⟩, ⟨0, 65037, .local 300⟩,
  ⟨0, 43, .target 1⟩, ⟨0, 44, .target 1⟩, ⟨0, 45, .target 1⟩, ⟨0, 46, .target 1⟩,
  ⟨0, 47, .target 1⟩, ⟨0, 48, .target 1⟩, ⟨0, 49, .target 1⟩, ⟨0, 50, .target 1⟩,
  ⟨0, 51, .target 1⟩, ⟨0, 52, .target 1⟩, ⟨0, 53, .target 1⟩, ⟨0, 54, .target 1⟩,
  ⟨0, 55, .target 1⟩, ⟨0, 56, .target 1⟩, ⟨0, 57, .target 1⟩, ⟨0, 58, .target 1⟩,
  ⟨0, 59, .target 1⟩, ⟨0, 60, .target 1⟩, ⟨0, 61, .target 1⟩, ⟨0, 62, .target 1⟩,
  ⟨0, 63, .target 1⟩, ⟨0, 64, .target 1⟩, ⟨0, 65, .target 1⟩, ⟨0, 66, .target 1⟩,
  ⟨0, 67, .target 1⟩, ⟨0, 68, .target 1⟩, ⟨0, 69, .targets [1, 2]⟩,
  ⟨0, 88, .none⟩, ⟨0, 89, .none⟩, ⟨0, 90, .none⟩, ⟨0, 91, .none⟩, ⟨0, 92, .none⟩,
  ⟨0, 93, .none⟩, ⟨0, 94, .none⟩, ⟨0, 95, .none⟩, ⟨0, 96, .none⟩, ⟨0, 97, .none⟩,
  ⟨0, 98, .none⟩, ⟨0, 99, .none⟩, ⟨0, 100, .none⟩, ⟨0, 101, .none⟩, ⟨0, 102, .none⟩,
  ⟨0, 103, .none⟩, ⟨0, 104, .none⟩, ⟨0, 105, .none⟩, ⟨0, 106, .none⟩, ⟨0, 109, .none⟩,
  ⟨0, 110, .none⟩, ⟨0, 209, .none⟩, ⟨0, 210, .none⟩, ⟨0, 211, .none⟩, ⟨0, 224, .none⟩,
  ⟨0, 130, .none⟩, ⟨0, 131, .none⟩, ⟨0, 132, .none⟩, ⟨0, 133, .none⟩, ⟨0, 134, .none⟩,
  ⟨0, 135, .none⟩, ⟨0, 136, .none⟩, ⟨0, 137, .none⟩, ⟨0, 138, .none⟩, ⟨0, 139, .none⟩,
  ⟨0, 179, .none⟩, ⟨0, 180, .none⟩, ⟨0, 181, .none⟩, ⟨0, 182, .none⟩, ⟨0, 183, .none⟩,
  ⟨0, 184, .none⟩, ⟨0, 185, .none⟩, ⟨0, 186, .none⟩, ⟨0, 212, .none⟩, ⟨0, 213, .none⟩,
  ⟨0, 214, .none⟩, ⟨0, 215, .none⟩, ⟨0, 216, .none⟩, ⟨0, 217, .none⟩, ⟨0, 218, .none⟩,
  ⟨0, 219, .none⟩,
  ⟨0, 65025, .none⟩, ⟨0, 65026, .none⟩, ⟨0, 65027, .none⟩, ⟨0, 65028, .none⟩,
  ⟨0, 65029, .none⟩]

/-- Constructors no opcode decodes to: the families outside the value opcodes, and `arg`, whose
    narrowing the raw instruction does not determine. -/
def undecoded : List Name := [
  ``Instruction.stackAlloc, ``Instruction.newArray, ``Instruction.newReferenceArray,
  ``Instruction.loadAggregate, ``Instruction.copyObject, ``Instruction.storeAggregate,
  ``Instruction.initAggregate, ``Instruction.loadScalar, ``Instruction.storeScalar,
  ``Instruction.fieldAt, ``Instruction.fieldAddress, ``Instruction.setFieldAt,
  ``Instruction.aggregateFieldAt, ``Instruction.setAggregateFieldAt, ``Instruction.arg,
  ``Instruction.initializeSpanLocal, ``Instruction.tailCall, ``Instruction.managed,
  ``Instruction.load64, ``Instruction.store64, ``Instruction.call, ``Instruction.callInstance,
  ``Instruction.callVirtual, ``Instruction.newAggregate, ``Instruction.newObject,
  ``Instruction.objectTest, ``Instruction.skipInit, ``Instruction.feature,
  ``Instruction.intrinsic, ``Instruction.memory, ``Instruction.throw,
  ``Instruction.unsupported]

/-- What each named opcode decodes to. -/
def decodedNamed : List (Option Instruction) := namedOpcodes.map Instruction.ofRaw?

/-- Raw instructions over every one-byte and two-byte opcode with each operand kind the value
    family reads; `ofRaw?` must give `none` for every opcode outside `Instruction.valueOpcode`. -/
def probes : List RawInstruction :=
  ((List.range 256 ++ (List.range 32).map (65024 + ·)).flatMap fun opcode =>
    ([.none, .integer 1, .argument 1, .local 1, .target 1, .targets [1]] : List RawOperand).map
      fun operand => { offset := 0, opcode, operand })

/-- `ofRaw?` decodes only value opcodes, every value opcode is named, and every named opcode
    decodes to an instruction that `valueEncodingMatches` accepts against itself. -/
theorem ofRaw?_exact :
    probes.all (fun raw =>
      (Instruction.ofRaw? raw).isNone || Instruction.valueOpcode raw.opcode) = true ∧
    probes.all (fun raw => !Instruction.valueOpcode raw.opcode ||
      namedOpcodes.any (·.opcode == raw.opcode)) = true ∧
    namedOpcodes.all (fun raw => match Instruction.ofRaw? raw with
      | some decoded => valueEncodingMatches raw decoded
      | none => false) = true := by
  decide +kernel

/-- info: 'Tests.ValueDecoding.ofRaw?_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofRaw?_exact

/-- Emitted instructions that differ from what the raw instruction decodes to: a constant out of
    its form's range, another operand, or another constructor with the same stack effect. -/
def mutations : List (RawInstruction × Instruction) := [
  -- Constants outside the range of their form, or of another width.
  (⟨0, 31, .integer 300⟩, .ldc_i4 300),
  (⟨0, 31, .integer (-129)⟩, .ldc_i4 (BitVec.ofInt 32 (-129))),
  (⟨0, 32, .integer (2^31)⟩, .ldc_i4 (BitVec.ofInt 32 (2^31))),
  (⟨0, 33, .integer (2^63)⟩, .ldc_i8 (BitVec.ofInt 64 (2^63))),
  (⟨0, 33, .integer (-1)⟩, .ldc_i4 (BitVec.ofInt 32 (-1))),
  -- Another constant, local or target than the operand names.
  (⟨0, 25, .none⟩, .ldc_i4 2), (⟨0, 31, .integer (-5)⟩, .ldc_i4 5),
  (⟨0, 6, .none⟩, .ldloc 1), (⟨0, 65036, .local 300⟩, .ldloc 299),
  (⟨0, 43, .target 1⟩, .br 2), (⟨0, 69, .targets [1, 2]⟩, .switch [2, 1]),
  (⟨0, 69, .targets [1, 2]⟩, .switch [1, 2, 3]),
  -- Another constructor with the same stack effect.
  (⟨0, 88, .none⟩, .sub), (⟨0, 38, .none⟩, .skipInit), (⟨0, 19, .local 4⟩, .ldloc 4),
  (⟨0, 18, .local 4⟩, .ldloc 4), (⟨0, 58, .target 1⟩, .brfalse 1),
  (⟨0, 138, .none⟩, .conv_ovf_un .i8), (⟨0, 211, .none⟩, .conv_i8),
  (⟨0, 130, .none⟩, .conv_ovf .i1), (⟨0, 215, .none⟩, .add_ovf), (⟨0, 65027, .none⟩, .cgt),
  -- A malformed operand, an argument opcode, or an opcode outside the value family.
  (⟨0, 42, .integer 0⟩, .ret), (⟨0, 17, .argument 4⟩, .ldloc 4), (⟨0, 6, .local 0⟩, .ldloc 0),
  (⟨0, 43, .targets [1]⟩, .br 1), (⟨0, 2, .none⟩, .arg 0), (⟨0, 14, .argument 1⟩, .arg 1),
  (⟨0, 107, .none⟩, .conv_i4)]

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

/-- info: decoded 61, undecoded 32 of 93 constructors -/
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
