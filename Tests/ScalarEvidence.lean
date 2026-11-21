import CIL.Extraction.Translation
import CIL.Safety.Frames
import Tests.BodyEncoding
import Tests.Support.ModelOperands
import Tests.Support.RawDecoding

/-!
Certificate regression fixtures, evaluated against the checked CIL extraction model.
Related scalar cases share one kernel decision so repeated metadata reductions can be reused.
Each conjunction retains its positive and negative obligations.
-/

namespace Tests.ScalarEvidence
open CIL CIL.Extraction Tests.BodyEncoding
open Tests.MetadataBuilder (objectPlatform)

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def word : TypeExpr := .atom runtime "System.UInt64"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def nativeType : TypeExpr := .atom runtime "System.IntPtr"
private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
/-- The pinned assembly owning `Scope::Fixture`; every certificate attributes its bodies to it. -/
private def scope : AssemblyPin :=
  { identity := "Scope, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" }
private def raw (code : List RawInstruction) (parameters : List TypeExpr := [word, word]) : RawMethod := {
  token := 0x06000001, owner := scope.identity ++ "::Fixture", hasThis := false,
  explicitThis := false, callingConvention := 0, attributes := 0, implementation := 0,
  returnType := word, parameters, locals := [], initLocals := true, maxStack := 2,
  genericParameters := [], code }
/-- The declared signature of the two-word-parameter, word-returning methods `raw` builds. -/
private def wordPair : DeclaredSignature := { parameters := [word, word], returnType := word }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩
private def unknown (count : Nat) := state (List.replicate count none)

/-- All native-count shifts retain their value kind and reject ordinary int64 counts. -/
private theorem nativeShiftKinds :
    ([98, 99, 100].all fun opcode =>
      [ScalarKind.word32, .word64, .native].all fun kind =>
        scalarTransfer (raw []) (i opcode) [.native, kind] == some [kind] &&
        scalarTransfer (raw []) (i opcode) [.word64, kind] == none) = true := by decide +kernel
#print axioms nativeShiftKinds

/-- Native-count certificates bind both the exact shift operation and the count's metadata. -/
private theorem nativeShiftCertificates :
    ([(98, Instruction.shl), (99, Instruction.shr), (100, Instruction.shr_un)].all
      fun (opcode, operation) =>
      let method := raw [i 2, i 3, i opcode, i 42] [word, nativeType]
      let features := [unknown 0, unknown 1, unknown 2, unknown 1]
      let states := [some [], some [ScalarKind.word64], some [.native, .word64], some [.word64]]
      let code := [.ldarg 0, .ldarg 1, operation, .ret]
      decide (ScalarFlowValid method features states code) &&
      !decide (ScalarFlowValid { method with parameters := [word, word] } features states code) &&
      !decide (ScalarFlowValid method features states (code.set 2 .add))) = true := by
  decide +kernel
#print axioms nativeShiftCertificates

private def arithmetic : List (Nat × Instruction) := [
  (88, .add), (89, .sub), (90, .mul), (91, .div), (92, .div_un), (93, .rem), (94, .rem_un),
  (95, .and), (96, .or), (97, .xor), (98, .shl), (99, .shr), (100, .shr_un), (214, .add_ovf),
  (215, .add_ovf_un), (216, .mul_ovf), (217, .mul_ovf_un), (218, .sub_ovf),
  (219, .sub_ovf_un), (65025, .ceq), (65026, .cgt), (65027, .cgt_un),
  (65028, .clt), (65029, .clt_un)]
example : arithmetic.all (fun (opcode, operation) =>
    scalarOpMatches none (i opcode) [.word32, .word32] operation) = true := by decide
example : arithmetic.all (fun (opcode, _operation) =>
    !scalarOpMatches none (i opcode) [.word32, .word32] (if opcode == 88 then .sub else .add)) =
      true := by decide
example : scalarOpMatches none (i 101) [.word64] .neg = true := by decide
example : scalarOpMatches none (i 102) [.word64] .not = true := by decide
example : scalarOpMatches none (i 101) [.word64] .not = false := by decide
example : scalarOpMatches none (i 88 (.integer 0)) [.word64, .word64] .add = false := by decide
example : scalarOpMatches none (i 88) [.other, .other] .add = false := by decide
example : scalarOpMatches none (i 88) [.reference, .word32] .add = true := by decide
example : scalarOpMatches none (i 88) [.native, .word64] .add = false := by decide
example : scalarOpMatches none (i 88) [.word32, .native] .add = true := by decide
example : scalarOpMatches none (i 88) [.word64, .word64] .sub = false := by decide
example : scalarOpMatches none (i 88) [.word32, .native] .sub = false := by decide

private def arithmeticFlagMutations : List (Nat × Instruction) := [
  (91, .div_un), (91, .rem), (91, .rem_un), (92, .div), (92, .rem_un), (92, .rem),
  (93, .rem_un), (93, .div), (93, .div_un), (94, .rem), (94, .div_un), (94, .div),
  (214, .add_ovf_un), (215, .add_ovf), (216, .mul_ovf_un), (217, .mul_ovf),
  (218, .sub_ovf_un), (219, .sub_ovf)]
example : arithmeticFlagMutations.all (fun (opcode, operation) =>
    !scalarOpMatches none (i opcode) [.word64, .word64] operation) = true := by decide

private def conversions : List (Nat × Instruction) := [
  (103, .conv_i1), (104, .conv_i2), (105, .conv_i4), (106, .conv_i8), (109, .conv_u4),
  (110, .conv_u8),
  (130, .conv_ovf_un .i1), (131, .conv_ovf_un .i2), (132, .conv_ovf_un .i4),
  (133, .conv_ovf_un .i8), (134, .conv_ovf_un .u1), (135, .conv_ovf_un .u2),
  (136, .conv_ovf_un .u4), (137, .conv_ovf_un .u8), (138, .conv_ovf_un .i),
  (139, .conv_ovf_un .u),
  (179, .conv_ovf .i1), (180, .conv_ovf .u1), (181, .conv_ovf .i2), (182, .conv_ovf .u2),
  (183, .conv_ovf .i4), (184, .conv_ovf .u4), (185, .conv_ovf .i8), (186, .conv_ovf .u8),
  (209, .conv_u2), (210, .conv_u1), (211, .conv_i), (212, .conv_ovf .i), (213, .conv_ovf .u),
  (224, .conv_u)]
example : conversions.all (fun (opcode, operation) =>
    scalarOpMatches none (i opcode) [.word64] operation) = true := by decide
example : scalarOpMatches none (i 106) [.word32] .conv_u8 = false := by decide
example : scalarOpMatches none (i 133) [.word32] (.conv_ovf .i8) = false := by decide
example : scalarOpMatches none (i 133) [.word32] (.conv_ovf_un .u8) = false := by decide
example : scalarOpMatches none (i 133) [.word32] .conv_i8 = false := by decide
example : scalarOpMatches none (i 106) [.word32] (.conv_ovf .i8) = false := by decide
example : scalarOpMatches none (i 183) [.word64] (.conv_ovf .i2) = false := by decide
-- A native-sized opcode and its 64-bit sibling have the same semantics but distinct constructors,
-- so the decoded opcode is recoverable from the emitted instruction.
private def nativeSiblings : List (Nat × Instruction) := [
  (133, .conv_ovf_un .i), (138, .conv_ovf_un .i8), (137, .conv_ovf_un .u),
  (139, .conv_ovf_un .u8), (185, .conv_ovf .i), (212, .conv_ovf .i8), (186, .conv_ovf .u),
  (213, .conv_ovf .u8), (106, .conv_i), (211, .conv_i8)]
example : nativeSiblings.all (fun (opcode, operation) =>
    !scalarOpMatches none (i opcode) [.word64] operation) = true := by decide +kernel

/-- The ECMA-335 III constructor of each division, overflow-checked, wrapping arithmetic and
    integer conversion opcode with two stack operands. -/
private def binaryTable : List (Nat × Instruction) := [
  (88, .add), (89, .sub), (90, .mul), (91, .div), (92, .div_un), (93, .rem), (94, .rem_un),
  (214, .add_ovf), (215, .add_ovf_un), (216, .mul_ovf), (217, .mul_ovf_un), (218, .sub_ovf),
  (219, .sub_ovf_un)]
/-- The same for the conversion opcodes, which take one stack operand. -/
private def unaryTable : List (Nat × Instruction) := [
  (103, .conv_i1), (104, .conv_i2), (105, .conv_i4), (106, .conv_i8), (109, .conv_u4),
  (110, .conv_u8), (209, .conv_u2), (210, .conv_u1), (211, .conv_i), (224, .conv_u),
  (130, .conv_ovf_un .i1), (131, .conv_ovf_un .i2), (132, .conv_ovf_un .i4),
  (133, .conv_ovf_un .i8), (134, .conv_ovf_un .u1), (135, .conv_ovf_un .u2),
  (136, .conv_ovf_un .u4), (137, .conv_ovf_un .u8), (138, .conv_ovf_un .i),
  (139, .conv_ovf_un .u),
  (179, .conv_ovf .i1), (180, .conv_ovf .u1), (181, .conv_ovf .i2), (182, .conv_ovf .u2),
  (183, .conv_ovf .i4), (184, .conv_ovf .u4), (185, .conv_ovf .i8), (186, .conv_ovf .u8),
  (212, .conv_ovf .i), (213, .conv_ovf .u)]
/-- The opcode and emitted constructor pairs, over every opcode of both tables and every
    constructor they name, where acceptance at `kind` operands differs from the table. The
    tables name each constructor once, so a row's own position identifies its constructor. -/
private def tableMismatches (kind : ScalarKind) : List (Nat × Instruction) :=
  let table := binaryTable ++ unaryTable
  let stacks := binaryTable.map (fun _ => [kind, kind]) ++ unaryTable.map fun _ => [kind]
  (table.zip stacks).zipIdx.flatMap fun (((opcode, _), stack), row) =>
    table.zipIdx.filterMap fun ((_, candidate), column) =>
      if scalarOpMatches none (i opcode) stack candidate == (row == column) then none
      else some (opcode, candidate)
/-- Each opcode accepts exactly its own constructor among all 43, at both word widths, so every
    constructor has its opcode and rejects every sibling. -/
private theorem scalarTableExact :
    tableMismatches .word64 = [] ∧ tableMismatches .word32 = [] := by decide +kernel
#print axioms scalarTableExact

example : scalarOpMatches none (i 21) [] (.ldc_i4 (BitVec.ofInt 32 (-1))) = true := by decide
example : scalarOpMatches none (i 30) [] (.ldc_i4 8) = true := by decide
example : scalarOpMatches none (i 31 (.integer (-128))) []
    (.ldc_i4 (BitVec.ofInt 32 (-128))) = true := by decide
example : scalarOpMatches none (i 31 (.integer 128)) [] (.ldc_i4 128) = false := by decide
example : scalarOpMatches none (i 32 (.integer (-2147483648))) []
    (.ldc_i4 2147483648) = true := by decide
example : scalarOpMatches none (i 32 (.integer 2147483648)) []
    (.ldc_i4 2147483648) = false := by decide
example : scalarOpMatches none (i 33 (.integer (-9223372036854775808))) []
    (.ldc_i8 9223372036854775808) = true := by decide
example : scalarOpMatches none (i 33 (.integer 9223372036854775807)) []
    (.ldc_i8 9223372036854775807) = true := by decide
example : scalarOpMatches none (i 33 (.integer (-1))) []
    (.ldc_i8 18446744073709551615) = true := by decide
example : scalarOpMatches none (i 33 (.integer (-9223372036854775808))) []
    (.ldc_i8 0) = false := by decide
example : scalarOpMatches none (i 33 (.integer (-9223372036854775808))) []
    (.ldc_i8 9223372036854775809) = false := by decide
example : scalarOpMatches none (i 33 (.integer 9223372036854775808)) []
    (.ldc_i8 9223372036854775808) = false := by decide
example : scalarOpMatches none (i 33) [] (.ldc_i8 0) = false := by decide

private def addRaw := raw [i 2, i 3, i 88, i 42]
private def addFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 1]
private def addStates : ScalarCertificate := [some [], some [.word64], some [.word64, .word64], some [.word64]]
private def addCode : List Instruction := [.ldarg 0, .ldarg 1, .add, .ret]
private def addEvidence : MethodEvidence := withBody {
  body := noBody, original := addRaw, arguments := [], closed := addRaw,
  parameterInput := { arguments := [.field .unsigned64, .field .unsigned64], locals := [], code := [.load 0, .load 1, .other, .other] },
  reachable := List.replicate 4 true, featureStates := addFeatures, scalarStates := addStates, layoutUses := [], assembly := scope }
private def addMethod : Method :=
  { locals := [], returnsValue := true, declared := wordPair, code := addCode }

example : TranslationValid [] #[] [] objectPlatform [addEvidence] [] [addMethod] := by
  decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [addEvidence] []
    [{ addMethod with code := addCode.set 2 .sub }] := by decide +kernel
/-- A method with the adder’s code and an extra home cannot be the result of its body decode. -/
theorem addition_rejects_extra_home :
    ¬ MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence
      { addMethod with parameterHomes := [(0, .word64)] } := by
  intro valid
  have body := valid.ofBody?
  have original : Method.ofBody? addMethod.profile addMethod.environment addEvidence.links
      addEvidence.reachable addEvidence.body addEvidence.original addEvidence.arguments =
      some addMethod := by decide +kernel
  rw [original] at body
  cases body

#print axioms addition_rejects_extra_home

-- The declared signature and the layout environment are conjuncts of their own.
example : ¬ DeclaredValid addRaw { addMethod with declared := {} } := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [addEvidence] []
    [{ addMethod with declared := {} }] := by
  decide +kernel
example : ¬ MethodEnvironmentValid [] #[]
    { addMethod with environment := { layouts := #[⟨⟨4, []⟩, 4⟩] } } := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [addEvidence] []
    [{ addMethod with environment := { layouts := #[⟨⟨4, []⟩, 4⟩] } }] := by decide +kernel

/-- `addMethod` declaring `signature` instead of the `wordPair` its metadata implies. -/
private def declaring (signature : DeclaredSignature) : Method :=
  { addMethod with declared := signature }
/-- A changed declaration passes the shape check and fails the signature and evidence checks. -/
private def wrongDeclarationRejected (signature : DeclaredSignature) : Prop :=
  MethodShapeValid addRaw (declaring signature) ∧ ¬ DeclaredValid addRaw (declaring signature) ∧
    ¬ MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence (declaring signature)
instance (signature : DeclaredSignature) : Decidable (wrongDeclarationRejected signature) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- One component of the signature differs in each case.
example : wrongDeclarationRejected { wordPair with returnType := intType } := by decide +kernel
example : wrongDeclarationRejected { wordPair with parameters := [word, intType] } := by
  decide +kernel
example : wrongDeclarationRejected { wordPair with receiver := some .reference } := by decide +kernel
example : wrongDeclarationRejected { wordPair with parameters := [word] } := by decide +kernel

example : ¬ TranslationValid [] #[] [] objectPlatform
    [{ addEvidence with scalarStates := addStates.set 2 (some [.native, .word32]) }] []
    [addMethod] := by decide +kernel
example : ¬ ScalarFlowValid { addRaw with maxStack := 1 } addFeatures addStates addCode := by decide
example : ¬ ScalarFlowValid addRaw addFeatures (addStates.set 0 (some [.word64])) addCode := by
  decide
example : ¬ ScalarFlowValid addRaw addFeatures (addStates.drop 1) addCode := by decide
example : ¬ ScalarFlowValid addRaw addFeatures addStates (addCode.drop 1) := by decide
example : ¬ ScalarFlowValid addRaw (addFeatures.drop 1) addStates addCode := by decide

private def binaryEvidence (opcode : Nat) : MethodEvidence :=
  withBody { addEvidence with original := { addRaw with code := addRaw.code.set 2 (i opcode) }, closed := { addRaw with code := addRaw.code.set 2 (i opcode) } }
private def binaryMethod (operation : Instruction) : Method :=
  { addMethod with code := addCode.set 2 operation }
private def arithmeticFlagCases : List (Nat × Instruction) := [
  (91, .div), (92, .div_un), (93, .rem), (94, .rem_un), (214, .add_ovf), (215, .add_ovf_un),
  (216, .mul_ovf), (217, .mul_ovf_un), (218, .sub_ovf), (219, .sub_ovf_un)]
example : arithmeticFlagCases.all (fun (opcode, operation) =>
    decide (TranslationValid [] #[] [] objectPlatform [binaryEvidence opcode] []
      [binaryMethod operation])) = true := by decide +kernel
example : arithmeticFlagMutations.all (fun (opcode, operation) =>
    decide (¬ TranslationValid [] #[] [] objectPlatform [binaryEvidence opcode] []
      [binaryMethod operation])) = true := by decide +kernel

private def literalRaw := raw [i 33 (.integer (-9223372036854775808)), i 42] []
private def literalFeatures : FeatureCertificate := [unknown 0, unknown 1]
private def literalStates : ScalarCertificate := [some [], some [.word64]]
private def literalEvidence : MethodEvidence := withBody {
  body := noBody, original := literalRaw, arguments := [], closed := literalRaw,
  parameterInput := { arguments := [], locals := [], code := [.other, .other] },
  reachable := [true, true], featureStates := literalFeatures, scalarStates := literalStates, layoutUses := [], assembly := scope }
private def literalMethod : Method := {
  locals := [], returnsValue := true, declared := { returnType := word },
  code := [.ldc_i8 9223372036854775808, .ret] }
example : TranslationValid [] #[] [] objectPlatform [literalEvidence] [] [literalMethod] := by
  decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [literalEvidence] []
    [{ literalMethod with code := [.ldc_i8 9223372036854775809, .ret] }] := by decide +kernel

private def convertRaw := raw [i 2, i 133, i 42] [word]
private def convertFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1]
private def convertStates : ScalarCertificate := [some [], some [.word64], some [.word64]]
private def convertEvidence : MethodEvidence := withBody {
  body := noBody, original := convertRaw, arguments := [], closed := convertRaw,
  parameterInput := { arguments := [.field .unsigned64], locals := [], code := [.load 0, .other, .other] },
  reachable := [true, true, true], featureStates := convertFeatures, scalarStates := convertStates, layoutUses := [], assembly := scope }
private def convertMethod : Method := {
  locals := [], returnsValue := true, declared := { parameters := [word], returnType := word },
  code := [.ldarg 0, .conv_ovf_un .i8, .ret] }
example : TranslationValid [] #[] [] objectPlatform [convertEvidence] [] [convertMethod] := by
  decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [convertEvidence] []
    [{ convertMethod with code := [.ldarg 0, .conv_ovf_un .u8, .ret] }] := by decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [convertEvidence] []
    [{ convertMethod with code := [.ldarg 0, .conv_ovf .i8, .ret] }] := by decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [convertEvidence] []
    [{ convertMethod with code := [.ldarg 0, .conv_ovf_un .i, .ret] }] := by decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [convertEvidence] []
    [{ convertMethod with code := [.ldarg 0, .conv_i8, .ret] }] := by decide +kernel

private def floatRaw (opcode : Nat) := raw [i 23, i opcode, i 106, i 42] []
private def floatFeatures : FeatureCertificate := [unknown 0, state [some 1], unknown 1, unknown 1]
private def floatStates : ScalarCertificate := [some [], some [.word32], some [.word32], some [.word64]]
private def floatEvidence (opcode : Nat) : MethodEvidence := withBody {
  body := noBody, original := floatRaw opcode, arguments := [], closed := floatRaw opcode,
  parameterInput := { arguments := [], locals := [], code := List.replicate 4 .other },
  reachable := List.replicate 4 true, featureStates := floatFeatures, scalarStates := floatStates, layoutUses := [], assembly := scope }
private def floatMethod : Method := {
  locals := [], returnsValue := true, declared := { returnType := word },
  code := [.ldc_i4 1, .neg, .conv_i8, .ret] }
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (floatRaw 107) .scalar floatFeatures
    (List.replicate 4 true) floatMethod.code := by decide
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (floatRaw 108) .scalar floatFeatures
    (List.replicate 4 true) floatMethod.code := by decide
example : scalarTransfer (floatRaw 107) (i 107) [.word32] = some [.other] := by decide
example : scalarTransfer (floatRaw 108) (i 108) [.word32] = some [.other] := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [floatEvidence 107] [] [floatMethod] := by
  decide +kernel
example : ¬ TranslationValid [] #[] [] objectPlatform [floatEvidence 108] [] [floatMethod] := by
  decide +kernel
-- The scalar flow itself rejects them, since the declared signature is right.
example : ¬ ScalarFlowValid (floatRaw 107) floatFeatures floatStates floatMethod.code := by
  decide
example : ¬ ScalarFlowValid (floatRaw 108) floatFeatures floatStates floatMethod.code := by
  decide
example : MethodShapeValid (floatRaw 107) floatMethod := by decide
example : ¬ ScalarFlowValid (floatRaw 107) floatFeatures (floatStates.set 2 (some [.other]))
    floatMethod.code := by decide
example : ¬ ScalarFlowValid (floatRaw 108) floatFeatures (floatStates.set 2 (some [.other]))
    floatMethod.code := by decide
example : scalarTransfer addRaw (i 80) [.reference] = some [.other] := by decide
example : scalarTransfer addRaw (i 150) [.word32, .reference] = none := by decide
-- `ldelem.ref` and `stelem.ref` are covered: only an object or null array of class references.
example : scalarTransfer addRaw (i 154) [.word32, .reference] = none := by decide
example : scalarTransfer addRaw (i 154) [.word32, .object] = some [.object] := by decide
example : scalarTransfer addRaw (i 162) [.nullObject, .native, .object] = some [] := by decide
example : scalarTransfer addRaw (i 162) [.word32, .word32, .object] = none := by decide

example : scalarTransfer { addRaw with locals := [intType] } (i 10) [.other] = none := by decide
example : scalarTransfer { addRaw with locals := [intType] } (i 10) [.word64] = none := by decide
example : scalarTransfer { addRaw with locals := [intType] } (i 10) [.word32] = some [] := by decide
example : scalarTransfer { addRaw with parameters := [intType] } (i 16 (.argument 0)) [.other] = none := by decide
example : scalarTransfer { addRaw with parameters := [intType] } (i 16 (.argument 0)) [.word32] = some [] := by decide
example : scalarTransfer addRaw (i 42) [.other] = none := by decide
example : scalarTransfer addRaw (i 42) [.word32] = none := by decide
example : scalarTransfer addRaw (i 42) [.word64, .word64] = none := by decide
example : scalarTransfer addRaw (i 42) [.word64] = some [] := by decide

private def localRaw := { raw [i 23, i 107, i 10, i 6, i 106, i 42] [] with locals := [intType] }
private def localFeatures : FeatureCertificate :=
  ([[], [some 1], [none], [], [none], [none]] : List (List (Option W32))).map fun stack =>
    some ⟨stack, []⟩
private def localStates : ScalarCertificate := [some [], some [.word32], some [.other], some [], some [.word32], some [.word64]]
private def localEvidence : MethodEvidence := withBody {
  body := noBody, original := localRaw, arguments := [], closed := localRaw,
  parameterInput := { arguments := [], locals := [.field .signed32], code := List.replicate 6 .other },
  reachable := List.replicate 6 true, featureStates := localFeatures, scalarStates := localStates, layoutUses := [], assembly := scope }
private def localMethod : Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true,
  declared := { returnType := word },
  code := [.ldc_i4 1, .neg, .stloc 0, .ldloc 0, .conv_i8, .ret] }
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) localRaw .scalar localFeatures
    (List.replicate 6 true) localMethod.code := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [localEvidence] [] [localMethod] := by decide +kernel
example : ¬ ScalarFlowValid localRaw localFeatures localStates localMethod.code := by decide
example : MethodShapeValid localRaw localMethod := by decide

private def argumentRaw := raw [i 23, i 108, i 16 (.argument 0), i 2, i 106, i 42] [intType]
private def argumentFeatures : FeatureCertificate := [unknown 0, state [some 1], unknown 1, unknown 0, unknown 1, unknown 1]
private def argumentEvidence : MethodEvidence := withBody {
  body := noBody, original := argumentRaw, arguments := [], closed := argumentRaw,
  parameterInput := { arguments := [.field .signed32], locals := [], code := [.other, .other, .store 0, .load 0, .other, .other] },
  reachable := List.replicate 6 true, featureStates := argumentFeatures, scalarStates := localStates, layoutUses := [], assembly := scope }
private def argumentMethod : Method := {
  locals := [], parameterHomes := [(0, .word32)], returnsValue := true,
  declared := { parameters := [intType], returnType := word },
  code := [.ldc_i4 1, .neg, .starg 0, .ldarg 0, .conv_i8, .ret] }
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) argumentRaw .scalar argumentFeatures
    (List.replicate 6 true) argumentMethod.code := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [argumentEvidence] [] [argumentMethod] := by decide +kernel
example : ¬ ScalarFlowValid argumentRaw argumentFeatures localStates argumentMethod.code := by
  decide
example : MethodShapeValid argumentRaw argumentMethod := by decide

private def mixedRaw := { raw [i 2, i 3, i 88, i 42] [nativeType, intType] with returnType := nativeType }
private def mixedStates : ScalarCertificate := [some [], some [.native], some [.word32, .native], some [.native]]
private def mixedCode : List Instruction := [.ldarg 0, .ldarg 1, .add, .ret]
example : ScalarFlowValid mixedRaw addFeatures mixedStates mixedCode := by decide
example : ¬ ScalarFlowValid mixedRaw addFeatures mixedStates (mixedCode.set 2 .sub) := by decide
example : ¬ ScalarFlowValid addRaw addFeatures addStates (addCode.set 2 .sub) := by decide
example : ¬ ScalarFlowValid { mixedRaw with parameters := [nativeType, word] } addFeatures
    mixedStates mixedCode := by decide

private def site : CallSite := {
  declared := { convention := 0, returnType := word, parameters := [word, word] },
  method := {
    owner := .atom scope.identity "Fixture", name := name!"", hasThis := false, genericArity := 0,
    returnType := word, parameters := [word, word] },
  target := .managed 0x06000001, typeArguments := [], parameterCount := 2, returnsValue := true }
/-- The call linked to method 0 that names `site`'s method, as the extractor emits it. -/
private def emittedCall (site : CallSite) : Instruction := .call site.method
private def linkedZero : Option Link := some (.direct 0)
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40 (.call site)) true linkedZero
    (emittedCall site) = true := by decide
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40
    (.call { site with method.returnType := intType }))
    true linkedZero (emittedCall { site with method.returnType := intType }) = false := by decide
example : validateManagedCall [⟨[], { addRaw with returnType := intType }⟩] []
    (i 40 (.call site)) true linkedZero (emittedCall site) = false := by decide
example : scalarTransfer addRaw (i 40 (.call { site with
    target := .external "Scope::System.Int32 Owner::M()", parameterCount := 0,
    method.parameters := [], method.returnType := word })) [] = some [.other] := by decide +kernel
theorem external_call_validated : scalarTransfer addRaw (i 40 (.call { site with
    target := .external "Scope::System.UInt64 Owner::M()", parameterCount := 0,
    method.parameters := [] })) [] = some [.word64] := by decide +kernel

/-- Generic return kinds agree with the substituted method argument. -/
private theorem generic_return_cases :
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::!!0 Owner::M()",
        parameterCount := 0,
        method.parameters := [],
        typeArguments := [word] })) [] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::!!0 Owner::M()",
        parameterCount := 0,
        method.parameters := [],
        typeArguments := [intType] })) [] = some [.other]) := by
  decide +kernel

#print axioms generic_return_cases

example : validateManagedCall [⟨[], addRaw⟩] []
    (i 40 (.call { site with method.parameters := [intType, word] })) true linkedZero
      (emittedCall { site with method.parameters := [intType, word] }) = false := by decide
example : scalarTransfer addRaw (i 40 (.call site)) [.word64, .word64] = some [.word64] := by decide
example : scalarTransfer addRaw (i 40 (.call site)) [.other, .word64] = none := by decide
/-- Call signatures retain parameter order, receiver kinds and generic substitutions. -/
private theorem call_signature_cases :
    (scalarTransfer addRaw (i 40 (.call { site with
        method.parameters := [intType, word] })) [.word64, .word32] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.parameters := [intType, word] })) [.word32, .word64] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.hasThis := true,
        method.parameters := [intType, word] })) [.word64, .word32, .reference] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.hasThis := true,
        method.parameters := [intType, word] })) [.word64, .word32, .other] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(System.Int32)",
        parameterCount := 1,
        method.parameters := [intType] })) [.word32] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(System.Int32)",
        parameterCount := 1,
        method.parameters := [word] })) [.word64] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(!!0)",
        typeArguments := [intType],
        parameterCount := 1,
        method.parameters := [intType] })) [.word32] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(!!0)",
        typeArguments := [intType],
        parameterCount := 1,
        method.parameters := [word] })) [.word64] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.owner := .apply (.constructor "Scope" "Owner`1") intType,
        target := .external "Scope::!0 Owner`1<System.Int32>::M(!0)",
        parameterCount := 1,
        method.parameters := [intType],
        method.returnType := intType })) [.word32] = some [.word32]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.owner := .apply (.constructor "Scope" "Owner`1") intType,
        target := .external "Scope::!0 Owner`1<System.Int32>::M(!0)",
        parameterCount := 1,
        method.parameters := [word],
        method.returnType := intType })) [.word64] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        method.owner := .aggregate "Scope::Owner`2<System.Int32,System.UInt64>" 0,
        target := .external "Scope::!1 Owner`2<System.Int32,System.UInt64>::M(!0,!1)",
        method.parameters := [intType, word] })) [.word64, .word32] = some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external
          "Scope::System.UInt64 Owner::M(Container`2<System.Int32,System.UInt64>,System.Int32)",
        method.parameters := [.aggregate "Scope::Container`2<System.Int32,System.UInt64>" 0,
          intType] })) [.word32, .other] = some [.word64]) := by
  decide +kernel

#print axioms call_signature_cases

private def faultLocalRaw := { raw [i 2, i 10, i 6, i 42] [word] with locals := [intType], returnType := intType }
private def faultLocalFeatures : FeatureCertificate :=
  ([[], [none], [], [none]] : List (List (Option W32))).map fun stack => some ⟨stack, []⟩
private def faultLocalStates : ScalarCertificate := [some [], some [.word64], some [], some [.word32]]
private def faultLocalEvidence : MethodEvidence := withBody {
  body := noBody, original := faultLocalRaw, arguments := [], closed := faultLocalRaw,
  parameterInput := { arguments := [.field .unsigned64], locals := [.field .signed32], code := [.load 0, .other, .other, .other] },
  reachable := List.replicate 4 true, featureStates := faultLocalFeatures, scalarStates := faultLocalStates, layoutUses := [], assembly := scope }
private def faultLocalMethod : Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true,
  declared := { parameters := [word], returnType := intType },
  code := [.ldarg 0, .stloc 0, .ldloc 0, .ret] }
example : TranslationValid [] #[] [] objectPlatform [faultLocalEvidence] []
    [faultLocalMethod] := by
  decide +kernel
example : scalarTransfer faultLocalRaw (i 10) [.word64] = none := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] (.stloc 0) = true := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.native] (.stloc 0) = true := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.other] (.stloc 0) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.reference] (.stloc 0) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] (.stloc 1) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] .pop = false := by decide
example :
    scalarStoreFault { faultLocalRaw with locals := [] } (i 10) [.word64] (.stloc 0) = false := by
  decide
example : ¬ ScalarFlowValid faultLocalRaw faultLocalFeatures faultLocalStates
    (faultLocalMethod.code.set 1 (.stloc 1)) := by decide
example : ¬ TranslationValid [] #[] [] objectPlatform [faultLocalEvidence] []
    [{ faultLocalMethod with code := faultLocalMethod.code.set 1 .pop }] := by decide
example (memory : Safety.Memory) (reference : Safety.Reference) (bits : W64) :
    Safety.storeLocal memory (.bytes .word32 reference) (.scalar (.i64 bits)) = .error .invalidState := rfl
example (memory : Safety.Memory) (reference : Safety.Reference) (kind : NarrowKind) (bits : W64) :
    Safety.storeLocal memory (.bytes (.narrow kind) reference) (.scalar (.i64 bits)) = .error .invalidState := rfl

private def nativeHomeRaw := raw [i 3, i 16 (.argument 0), i 2, i 110, i 42] [nativeType, word]
private def nativeHomeFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, unknown 1, unknown 1]
private def nativeHomeStates : ScalarCertificate := [some [], some [.word64], some [], some [.native], some [.word64]]
private def nativeHomeEvidence : MethodEvidence := withBody {
  body := noBody, original := nativeHomeRaw, arguments := [], closed := nativeHomeRaw,
  parameterInput := { arguments := [.field .nativeInt, .field .unsigned64], locals := [], code := [.load 1, .store 0, .load 0, .other, .other] },
  reachable := List.replicate 5 true, featureStates := nativeHomeFeatures, scalarStates := nativeHomeStates, layoutUses := [], assembly := scope }
private def nativeHomeMethod : Method := {
  locals := [], parameterHomes := [(0, .word64)], returnsValue := true,
  declared := { parameters := [nativeType, word], returnType := word },
  code := [.ldarg 1, .starg 0, .ldarg 0, .conv_u8, .ret] }
example : TranslationValid [] #[] [] objectPlatform [nativeHomeEvidence] []
    [nativeHomeMethod] := by
  decide +kernel
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.word64] = some [] := by decide
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.other] = none := by decide
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.word32] = none := by decide
example : ¬ ScalarFlowValid nativeHomeRaw nativeHomeFeatures
    (nativeHomeStates.set 1 (some [.other])) nativeHomeMethod.code := by decide

private def nativeReturnRaw := raw [i 2, i 77, i 42] [.byref word]
private def nativeReturnFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1]
private def nativeReturnStates : ScalarCertificate := [some [], some [.reference], some [.native]]
private def nativeReturnEvidence : MethodEvidence := withBody {
  body := noBody, original := nativeReturnRaw, arguments := [], closed := nativeReturnRaw,
  parameterInput := { arguments := [.reference], locals := [], code := [.load 0, .other, .other] },
  reachable := List.replicate 3 true, featureStates := nativeReturnFeatures, scalarStates := nativeReturnStates, layoutUses := [], assembly := scope }
private def nativeReturnMethod : Method := {
  locals := [], returnsValue := true,
  declared := { parameters := [.byref word], returnType := word },
  code := [.ldarg 0, .ldind .i, .ret] }
example : TranslationValid [] #[] [] objectPlatform [nativeReturnEvidence] []
    [nativeReturnMethod] := by
  decide +kernel
example : scalarTransfer nativeReturnRaw (i 42) [.native] = some [] := by decide
example : scalarTransfer { nativeReturnRaw with returnType := nativeType } (i 42) [.word64] = some [] := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.other] = none := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.word32] = none := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.native, .word64] = none := by decide
example : ¬ ScalarFlowValid { nativeReturnRaw with returnType := intType }
    nativeReturnFeatures nativeReturnStates nativeReturnMethod.code := by decide

/-- Local slot reads as `ScalarFlowValid` evaluates them, from indexes built once per body. -/
private def indexedLocals (method : RawMethod) : ScalarLocals :=
  ScalarLocals.indexed method (nativeDispatchContext method)

/-- `push; stloc.s slot; ldloc.0; ret` over one int32 local. -/
private def slotRaw (push : RawInstruction) (slot : Nat) : RawMethod :=
  { raw [push, i 19 (.local slot), i 6, i 42] [] with locals := [intType], returnType := intType }
private def slotFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, unknown 1]
private def slotStates (pushed : ScalarKind) : ScalarCertificate :=
  [some [], some [pushed], some [], some [.word32]]
private def slotCode (push : Instruction) (slot : Nat) : List Instruction :=
  [push, .stloc slot, .ldloc 0, .ret]

/-- The indexed local reads accept an int32 store to the declared local and reject a store or
    load past the declared locals and a null store into an int32 local, at the site and in the
    certificate, as the metadata lists do. -/
theorem local_slot_sites :
    let constant := slotRaw (i 22) 0
    scalarTransfer constant (i 19 (.local 0)) [.word32] (locals := indexedLocals constant) =
      some [] ∧
    scalarTransfer constant (i 19 (.local 1)) [.word32] (locals := indexedLocals constant) =
      none ∧
    scalarTransfer constant (i 19 (.local 1)) [.word32] = none ∧
    scalarTransfer constant (i 17 (.local 1)) [] (locals := indexedLocals constant) = none ∧
    scalarTransfer constant (i 17 (.local 1)) [] = none ∧
    scalarStoreFault constant (i 19 (.local 1)) [.word64] (.stloc 1)
      (indexedLocals constant) = false ∧
    scalarTransfer constant (i 19 (.local 0)) [.nullObject]
      (locals := indexedLocals constant) = none ∧
    scalarTransfer constant (i 19 (.local 0)) [.nullObject] = none ∧
    ScalarFlowValid constant slotFeatures (slotStates .word32) (slotCode (.ldc_i4 0) 0) ∧
    ¬ ScalarFlowValid (slotRaw (i 22) 1) slotFeatures (slotStates .word32)
      (slotCode (.ldc_i4 0) 1) ∧
    ¬ ScalarFlowValid (slotRaw (i 20) 0) slotFeatures (slotStates .nullObject)
      (slotCode .ldnull 0) := by
  decide +kernel
#print axioms local_slot_sites

/-- A static method of no parameters whose address `ldftn` takes and `calli` calls. -/
private def handler : CallSite :=
  { declared := { convention := 0 },
    method := {
      owner := .void, name := name!"", hasThis := false, genericArity := 0, returnType := .void,
      parameters := [] },
    target := .managed 2, typeArguments := [], parameterCount := 0, returnsValue := false }
private def handlerSignature : ManagedSignature := ⟨.void, []⟩

/-- `ldftn; stloc store; ldloc.1; calli; ret` over two native-int locals, of which `calli`
    consumes only local 1. -/
private def pointerRaw (store : Nat) : RawMethod :=
  { raw [i 65030 (.call handler), i store, i 7, i 41 (.indirectCall .void [] false false 0),
      i 42] [] with locals := [nativeType, nativeType], returnType := .void }
private def pointerFeatures : FeatureCertificate :=
  [unknown 0, unknown 1, unknown 0, unknown 1, unknown 0]
private def pointerStates : ScalarCertificate :=
  [some [], some [.methodPointer handlerSignature], some [],
    some [.methodPointer handlerSignature], some []]
private def pointerCode (slot : Nat) : List Instruction :=
  [.managed (.address ⟨"Scope::Fixture", 2, []⟩ handlerSignature), .stloc slot, .ldloc 1,
    .managed (.call handlerSignature false), .ret]

/-- The indexed pointer locals give a method pointer home only to the native-int local a `calli`
    consumes: storing a method address into the other local, or taking the consumed local's
    address, is rejected at the site and in the certificate, as the metadata lists do. -/
theorem pointer_local_sites :
    let method := pointerRaw 11
    let pointer := ScalarKind.methodPointer handlerSignature
    scalarTransfer method (i 11) [pointer] (locals := indexedLocals method) = some [] ∧
    scalarTransfer method (i 10) [pointer] (locals := indexedLocals method) = none ∧
    scalarTransfer method (i 10) [pointer] = none ∧
    scalarTransfer method (i 6) [] (locals := indexedLocals method) = some [.native] ∧
    scalarTransfer method (i 7) [] (locals := indexedLocals method) = some [pointer] ∧
    scalarTransfer method (i 18 (.local 0)) [] (locals := indexedLocals method) =
      some [.reference] ∧
    scalarTransfer method (i 18 (.local 1)) [] (locals := indexedLocals method) = none ∧
    scalarTransfer method (i 18 (.local 1)) [] = none ∧
    ScalarFlowValid method pointerFeatures pointerStates (pointerCode 1) ∧
    ¬ ScalarFlowValid (pointerRaw 10) pointerFeatures pointerStates (pointerCode 0) := by
  decide +kernel
#print axioms pointer_local_sites

/-- The closed argument storage, reading pointer locals from a set built once per body, gives a
    method pointer home to the local `calli` consumes and native integer storage to the other,
    as scanning the pointer local list does; a pointer test that admits no local gives neither
    a method pointer home. -/
theorem pointer_local_storage :
    let method := pointerRaw 11
    let context := nativeDispatchContext method
    (closedArguments [] method).map (·.locals) =
      some [.field .nativeInt, .methodPointer handlerSignature] ∧
    (closedArgumentsWith [] method context context.pointerLocals.contains).map (·.locals) =
      some [.field .nativeInt, .methodPointer handlerSignature] ∧
    (closedArgumentsWith [] method context (fun _ => false)).map (·.locals) =
      some [.field .nativeInt, .field .nativeInt] := by
  decide +kernel
#print axioms pointer_local_storage

private def byteSpanType : TypeExpr := .apply (.constructor runtime "System.ReadOnlySpan`1") (.atom runtime "System.Byte")
private def byteSpanSite : CallSite := {
  declared := { convention := 0x20, parameters := [.pointer .void, intType] },
  method := {
    owner := byteSpanType, name := name!".ctor", hasThis := true, genericArity := 0,
    returnType := .void, parameters := [.pointer .void, intType] },
  name := ".ctor",
  target := .external
    (runtime ++ "::System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,\
    System.Int32)"),
  typeArguments := [], parameterCount := 2, returnsValue := false }
private def byteSpanRaw := { raw [i 2, i 31 (.integer 16), i 115 (.call byteSpanSite), i 42] [.byref word] with returnType := byteSpanType }
private def byteSpanFeatures : FeatureCertificate := [unknown 0, unknown 1, state [some 16, none], unknown 1]
private def byteSpanStates : ScalarCertificate := [some [], some [.reference], some [.word32, .reference], some [.other]]
private def byteSpanCode : List Instruction :=
  [.ldarg 0, .ldc_i4 16, .newobj byteSpanSite.method, .ret]
/-- Span construction checks its exact signature and managed backing reference. -/
private theorem span_constructor_cases :
    (ScalarFlowValid byteSpanRaw byteSpanFeatures byteSpanStates byteSpanCode) ∧
    (¬ ScalarFlowValid byteSpanRaw byteSpanFeatures byteSpanStates (byteSpanCode.set 2 (.memory
      (.spanItem 1)))) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .reference] = some
      [.other]) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .other] = none) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .native] = none) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with
        target := .external "forged" })) [.word32, .reference] = none) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with
        name := "Other" })) [.word32, .reference] = none) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with
        method.owner := .atom runtime "Other" })) [.word32, .reference] = none) ∧
    (scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with
        method.parameters := [.pointer word, intType] })) [.word32, .reference] = none) ∧
    (scalarTransfer byteSpanRaw (i 40 (.call byteSpanSite)) [.word32, .reference, .reference] =
      some []) ∧
    (scalarTransfer byteSpanRaw (i 40 (.call byteSpanSite)) [.word32, .reference, .other] =
      none) := by
  decide +kernel

#print axioms span_constructor_cases

private def tupleType : TypeExpr := .aggregate
  (runtime ++ "::System.ValueTuple`2<System.UInt64,System.UInt64>") 0
private def tupleSite : CallSite := {
  declared := { convention := 0, returnType := tupleType, parameters := [word, word, word] },
  method := {
    owner := .atom
      "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, \
        PublicKeyToken=cc7b13ffcd2ddd51"
      "System.Runtime.Intrinsics.X86.X86Base/X64", name := name!"DivRem", hasThis := false,
    genericArity := 0, returnType := tupleType, parameters := [word, word, word] },
  name := "DivRem",
  target := .external
    "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, \
      PublicKeyToken=cc7b13ffcd2ddd51::System.ValueTuple`2<System.UInt64,System.UInt64> \
      System.Runtime.Intrinsics.X86.X86Base/X64::DivRem\
      (System.UInt64,System.UInt64,System.UInt64)", typeArguments := [], parameterCount := 3,
  returnsValue := true }
private def tupleRaw := { raw [i 2, i 3, i 4, i 40 (.call tupleSite), i 42] [word, word, word] with
  returnType := tupleType, maxStack := 3 }
/-- Tuple results retain their declared input kinds. -/
private theorem tuple_result_cases :
    (ScalarFlowValid tupleRaw [unknown 0, unknown 1, unknown 2, unknown 3, unknown 1] [some [],
      some [.word64], some [.word64, .word64], some [.word64, .word64, .word64], some [.other]]
      [.ldarg 0, .ldarg 1, .ldarg 2, .call tupleSite.method {}, .ret]) ∧
    (scalarTransfer tupleRaw (i 40 (.call { tupleSite with
        method.parameters := [word, intType, word] })) [.word64, .word32, .word64] = none) := by
  decide +kernel

#print axioms tuple_result_cases

private def tupleFieldRaw :=
  raw [i 2, i 123 (.field tupleType 0 word name!"Item1" false), i 42] [.byref tupleType]
/-- The tuple's first field, as its raw operand names it. -/
private def tupleItem1 : FieldRef :=
  { owner := tupleType, index := 0, type := word, name := name!"Item1" }
/-- Tuple field loads preserve the declared scalar result kind. -/
private theorem tuple_field_cases :
    (ScalarFlowValid tupleFieldRaw [unknown 0, unknown 1, unknown 1] [some [], some
      [.reference], some [.word64]] [.ldarg 0, .ldfld tupleItem1, .ret]) ∧
    (¬ ScalarFlowValid tupleFieldRaw [unknown 0, unknown 1, unknown 1] [some [], some
      [.reference], some [.other]] [.ldarg 0, .ldfld tupleItem1, .ret]) := by
  decide +kernel

#print axioms tuple_field_cases

private def spanType : TypeExpr := .apply (.constructor runtime "System.ReadOnlySpan`1") (.atom runtime "System.UInt32")
private def spanSite : CallSite := {
  declared := {
    convention := 0x20,
    returnType := .modified true runtime "System.Runtime.InteropServices.InAttribute"
      (.byref (.ownerParameter 0)), parameters := [intType] },
  method := {
    owner := spanType, name := name!"get_Item", hasThis := true, genericArity := 0,
    returnType := .atom runtime "!0& modreq(System.Runtime.InteropServices.InAttribute)",
    parameters := [intType] },
  name := "get_Item",
  target := .external
    (runtime ++ "::!0& modreq(System.Runtime.InteropServices.InAttribute) \
    System.ReadOnlySpan`1<System.UInt32>::get_Item(System.Int32)"),
  typeArguments := [], parameterCount := 1, returnsValue := true }
private def spanRaw := { raw [i 2, i 3, i 40 (.call spanSite), i 113 (.type intType), i 42] [.byref spanType, intType] with returnType := intType }
/-- Span and external signatures reject malformed metadata and distinguish Unicode names. -/
private theorem span_signature_cases :
    (ScalarFlowValid spanRaw [unknown 0, unknown 1, unknown 2, unknown 1, unknown 1] [some [],
      some [.reference], some [.word32, .reference], some [.reference], some [.word32]] [.ldarg 0,
      .ldarg 1, .call spanSite.method {}, .ldobj intType, .ret]) ∧
    (scalarTransfer spanRaw (i 40 (.call { spanSite with
        method.parameters := [word] })) [.word64, .reference] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(garbage(System.Int32)",
        parameterCount := 1,
        method.parameters := [intType] })) [.word32] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(Container\u0394)",
        parameterCount := 1,
        method.parameters := [.aggregate "Scope::Container\u0394" 0] })) [.other] =
          some [.word64]) ∧
    (scalarTransfer addRaw (i 40 (.call { site with
        target := .external "Scope::System.UInt64 Owner::M(Container\u0394)",
        parameterCount := 1,
        method.parameters := [.aggregate "Scope::Container\u03a9" 0] })) [.other] = none) := by
  decide +kernel

#print axioms span_signature_cases

private def joinRaw := { raw [i 2, i 45 (.target 4), i 22, i 43 (.target 5), i 22, i 42] [intType] with returnType := intType }
private def joinFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, state [some 0], unknown 0, unknown 1]
private def joinStates : ScalarCertificate := [some [], some [.word32], some [], some [.word32], some [], some [.word32]]
private def joinCode : List Instruction :=
  [.ldarg 0, .brtrue 4, .ldc_i4 0, .br 5, .ldc_i4 0, .ret]
example : ScalarFlowValid joinRaw joinFeatures joinStates joinCode := by decide
example : ¬ ScalarFlowValid { joinRaw with code := joinRaw.code.set 4 (i 33 (.integer 0)) }
    joinFeatures joinStates (joinCode.set 4 (.ldc_i8 0)) := by decide
example : ¬ ScalarFlowValid { joinRaw with code := joinRaw.code.set 4 (i 33 (.integer 0)) }
    joinFeatures (joinStates.set 5 (some [.word64])) (joinCode.set 4 (.ldc_i8 0)) := by decide

private def loopRaw := raw [i 22, i 38, i 43 (.target 0)] []
private def loopFeatures : FeatureCertificate := [unknown 0, state [some 0], unknown 0]
private def loopStates : ScalarCertificate := [some [], some [.word32], some []]
private def loopCode : List Instruction := [.ldc_i4 0, .pop, .br 0]
example : ScalarFlowValid loopRaw loopFeatures loopStates loopCode := by decide
example : ¬ ScalarFlowValid loopRaw loopFeatures (loopStates.set 1 (some [.word64]))
    loopCode := by decide
example : ¬ ScalarFlowValid { loopRaw with code := [i 22, i 0, i 43 (.target 0)] }
    [unknown 0, state [some 0], state [some 0]] [some [], some [.word32], some [.word32]]
    [.ldc_i4 0, .nop, .br 0] := by decide

-- Defaulted signature fields are accepted only where they are the true signature.
private def unsignedSite : CallSite := {
  declared := { convention := 0 },
  method := {
    owner := .void, name := name!"", hasThis := false, genericArity := 0, returnType := .void,
    parameters := [] },
  target := .managed 0x06000001, typeArguments := [], parameterCount := 2, returnsValue := true }
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40 (.call unsignedSite)) true linkedZero
    (emittedCall unsignedSite) = false := by decide
example : scalarTransfer addRaw (i 40 (.call unsignedSite)) [.word64, .word64] = none := by decide
/-- External unsigned signatures retain their exact parameter and return metadata. -/
private theorem unsigned_signature_cases :
    (scalarTransfer addRaw (i 40 (.call { unsignedSite with
        target := .external "Scope::System.UInt64 Owner::M(System.UInt64,System.UInt64)" }))
      [.word64, .word64] = none) ∧
    (scalarTransfer addRaw (i 40 (.call { unsignedSite with
        target := .external "Scope::System.Void Owner::M()",
        parameterCount := 0,
        returnsValue := false })) [] = some []) := by
  decide +kernel

#print axioms unsigned_signature_cases

-- An uncovered raw opcode with the same stack effect cannot stand in for a scalar computation.
private def holeRaw (opcode : Nat) (operand : RawOperand := .none) := raw [i 2, i 3, i opcode operand, i 38, i 2, i 42]
private def holeFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 1, unknown 0, unknown 1]
private def holeStates : ScalarCertificate :=
  [some [], some [.word64], some [.word64, .word64], some [.other], some [], some [.word64]]
private def holeCode (emitted : Instruction) : List Instruction :=
  [.ldarg 0, .ldarg 1, emitted, .pop, .ldarg 0, .ret]
example : ScalarFlowValid (holeRaw 88) holeFeatures (holeStates.set 3 (some [.word64]))
    (holeCode .add) := by decide
-- Array loads now require exact array evidence rather than accepting an equal stack effect.
example : ¬ ScalarFlowValid (holeRaw 149) holeFeatures holeStates
    (holeCode (.memory (.spanItem 4))) := by decide
example : ¬ ScalarFlowValid (holeRaw 149) holeFeatures holeStates (holeCode .add) := by decide
example : ¬ ScalarFlowValid (holeRaw 143 (.type intType)) holeFeatures holeStates
    (holeCode .div) := by decide
private def holeEvidence (opcode : Nat) (states : ScalarCertificate) : MethodEvidence := withBody {
  body := noBody, original := holeRaw opcode, arguments := [], closed := holeRaw opcode,
  parameterInput := { arguments := [.field .unsigned64, .field .unsigned64], locals := [], code := [.load 0, .load 1, .other, .other, .load 0, .other] },
  reachable := List.replicate 6 true, featureStates := holeFeatures, scalarStates := states, layoutUses := [], assembly := scope }
private def holeMethod (emitted : Instruction) : Method :=
  { locals := [], returnsValue := true, declared := wordPair, code := holeCode emitted }
/-- A scalar opcode cannot be replaced by an unrelated instruction with the same stack effect. -/
private theorem scalar_opcode_cases :
    (TranslationValid [] #[] [] objectPlatform
      [holeEvidence 88 (holeStates.set 3 (some [.word64]))] []
      [holeMethod .add]) ∧
    (¬ TranslationValid [] #[] [] objectPlatform [holeEvidence 149 holeStates] []
      [holeMethod .add]) := by
  decide +kernel

#print axioms scalar_opcode_cases

private def unaryHoleRaw (opcode : Nat) := raw [i 2, i opcode, i 38, i 2, i 42] [word]
private def unaryHoleFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1, unknown 0, unknown 1]
private def unaryHoleStates : ScalarCertificate := [some [], some [.word64], some [.other], some [], some [.word64]]
private def unaryHoleCode (emitted : Instruction) : List Instruction :=
  [.ldarg 0, emitted, .pop, .ldarg 0, .ret]
-- An access form is reserved for the opcodes that decide its width, so no conversion emits one.
example : ¬ ScalarFlowValid (unaryHoleRaw 108) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode (.loadScalar 8)) := by decide
example : ¬ ScalarFlowValid (unaryHoleRaw 108) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode .conv_i8) := by decide
-- `conv.r4` is uncovered: the site admits no access form, conversion or faulting arithmetic.
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode .conv_i) := by decide +kernel
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode (.conv_ovf .i)) := by decide +kernel
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode (.conv_ovf_un .u)) := by decide +kernel
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode (.loadScalar 8)) := by decide +kernel
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode .rem_un) := by decide +kernel
example : ([Instruction.div, .div_un, .rem, .add_ovf, .add_ovf_un, .sub_ovf, .sub_ovf_un, .mul_ovf,
    .mul_ovf_un].all fun emitted => !decide (ScalarFlowValid (unaryHoleRaw 107)
      unaryHoleFeatures unaryHoleStates (unaryHoleCode emitted))) = true := by decide +kernel

/-! ## Indirect accesses

A body pushes `pops` copies of its argument, runs the access after its prefixes, pops what the
access pushed and returns the argument. Each raw `ldind`, `stind`, `ldobj`, `stobj`, `cpblk`
and `initblk` admits exactly the emission its opcode, operand type and prefix give. -/

/-- One access with its prefixes and the emission a certificate claims for it. -/
private structure IndirectCase where
  pops : Nat
  /-- The kind the access pushes, or `none` for a store or block operation. -/
  pushed : Option ScalarKind
  prefixes : List RawInstruction := []
  access : RawInstruction
  emitted : Instruction

private def IndirectCase.pushes (access : IndirectCase) : Nat :=
  if access.pushed.isSome then 1 else 0
private def IndirectCase.middle (access : IndirectCase) : List RawInstruction :=
  access.prefixes ++ [access.access]
private def IndirectCase.rawMethod (access : IndirectCase) : RawMethod :=
  { raw (List.replicate access.pops (i 2) ++ access.middle ++
      List.replicate access.pushes (i 38) ++ [i 2, i 42]) [word] with maxStack := 3 }
private def IndirectCase.code (access : IndirectCase) : List Instruction :=
  List.replicate access.pops (.ldarg 0) ++ access.prefixes.map (fun _ => .nop) ++
    [access.emitted] ++ List.replicate access.pushes .pop ++ [.ldarg 0, .ret]
private def IndirectCase.features (access : IndirectCase) : FeatureCertificate :=
  (List.range access.pops).map unknown ++ access.middle.map (fun _ => unknown access.pops) ++
    List.replicate access.pushes (unknown 1) ++ [unknown 0, unknown 1]
private def IndirectCase.states (access : IndirectCase) : ScalarCertificate :=
  (List.range access.pops).map (fun depth => some (List.replicate depth .word64)) ++
    access.middle.map (fun _ => some (List.replicate access.pops .word64)) ++
    access.pushed.toList.map (fun kind => some [kind]) ++ [some [], some [.word64]]
private def IndirectCase.reachable (access : IndirectCase) : List Bool :=
  List.replicate access.rawMethod.code.length true
private def IndirectCase.uses (access : IndirectCase) : List ArgumentOp :=
  List.replicate access.pops (.load 0) ++ access.middle.map (fun _ => .other) ++
    List.replicate access.pushes .other ++ [.load 0, .other]
private def IndirectCase.evidence (access : IndirectCase) : MethodEvidence := withBody {
  body := noBody, original := access.rawMethod, arguments := [], closed := access.rawMethod,
  parameterInput := { arguments := [.field .unsigned64], locals := [], code := access.uses },
  reachable := access.reachable, featureStates := access.features,
  scalarStates := access.states, layoutUses := [], assembly := scope }
private def IndirectCase.method (access : IndirectCase) : Method :=
  { locals := [], returnsValue := true, declared := { parameters := [word], returnType := word },
    code := access.code }
/-- Whether the feature and scalar checks accept the claimed emission. -/
private def IndirectCase.flows (access : IndirectCase) : Bool :=
  let (method, code, states) := match access.access.operand with
    | .type type =>
      let store := access.pops == 2
      let before := if store then [scalarType type, .reference] else [.reference]
      let inputs := if store then [i 2, i 3] else [i 2]
      let loads := if store then [Instruction.ldarg 0, .ldarg 1] else [.ldarg 0]
      let method := { access.rawMethod with
        parameters := [.byref type, type, word]
        code := inputs ++ access.middle ++ List.replicate access.pushes (i 38) ++ [i 4, i 42] }
      let code := loads ++ access.prefixes.map (fun _ => .nop) ++ [access.emitted] ++
        List.replicate access.pushes .pop ++ [.ldarg 2, .ret]
      let states := [some []] ++ (if store then [some [.reference]] else []) ++
        access.middle.map (fun _ => some before) ++ access.pushed.toList.map (fun k => some [k]) ++
        [some [], some [.word64]]
      (method, code, states)
    | _ => (access.rawMethod, access.code, access.states)
  decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none) method .scalar
    access.features
      access.reachable code) &&
    decide (ScalarFlowValid method access.features states code)
/-- Whether the indirect access rule accepts the emission at the access itself. -/
private def IndirectCase.window (access : IndirectCase) : Bool :=
  indirectSiteWindow (access.rawMethod.code[·]?) (access.pops + access.prefixes.length)
    access.access access.emitted
/-- Whether every check of the method's evidence accepts it. -/
private def IndirectCase.translates (access : IndirectCase) : Bool :=
  decide (MethodEvidenceValid [] #[] [] objectPlatform [access.evidence]
    [] access.evidence access.method)

private def load (opcode : Nat) (emitted : Instruction) (kind : ScalarKind := .word32)
    (prefixes : List RawInstruction := []) (operand : RawOperand := .none) : IndirectCase :=
  { pops := 1, pushed := some kind, prefixes, access := i opcode operand, emitted }
private def store (opcode : Nat) (emitted : Instruction) (prefixes : List RawInstruction := [])
    (operand : RawOperand := .none) : IndirectCase :=
  { pops := 2, pushed := none, prefixes, access := i opcode operand, emitted }
private def block (opcode : Nat) (emitted : Instruction) (prefixes : List RawInstruction := []) :
    IndirectCase :=
  { pops := 3, pushed := none, prefixes, access := i opcode, emitted }
private def unaligned (alignment : Int) : RawInstruction := i 65042 (.integer alignment)
private def sbyteType : TypeExpr := .atom runtime "System.SByte"
private def aggregateType : TypeExpr := .aggregate "S" 0
private def enumType : TypeExpr := .enum "E" (.atom runtime "System.Int16")
private def vectorType : TypeExpr :=
  .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1") intType
/-- An `ldobj` (113) or `stobj` (129) of `type`, pushing the kind the scalar check gives it. -/
private def typed (opcode : Nat) (type : TypeExpr) (emitted : Instruction) : IndirectCase :=
  if opcode == 113 then load 113 emitted (scalarType type) (operand := .type type)
  else store 129 emitted (operand := .type type)
/-- A static call taking one word and returning one, the stack effect of a 64-bit load. -/
private def loadSite : CallSite :=
  { declared := { convention := 0, returnType := word, parameters := [word] },
    method := {
      owner := .void, name := name!"", hasThis := false, genericArity := 0, returnType := word,
      parameters := [word] },
    target := .managed 0x06000002, typeArguments := [], parameterCount := 1, returnsValue := true }
/-- A static call taking two words and returning nothing, the stack effect of a 64-bit store. -/
private def storeSite : CallSite :=
  { declared := { convention := 0, parameters := [word, word] },
    method := {
      owner := .void, name := name!"", hasThis := false, genericArity := 0,
      returnType := .void, parameters := [word, word] },
    target := .managed 0x06000002, typeArguments := [], parameterCount := 2,
    returnsValue := false }

/-- The emissions extraction gives these accesses, none of which carries a metadata token. -/
private def indirectEmitted : List IndirectCase := [
  load 70 (.ldind .i1), load 71 (.ldind .u1), load 72 (.ldind .i2), load 73 (.ldind .u2),
  load 74 (.ldind .i4), load 75 (.ldind .u4), load 76 (.ldind .i8) .word64,
  load 77 (.ldind .i) .native, store 82 (.stind .i1), store 83 (.stind .i2),
  store 84 (.stind .i4), store 85 (.stind .i8), store 223 (.stind .i),
  block 65047 (.memory (.copyBlock 8)), block 65048 (.memory (.initBlock 8)),
  block 65047 (.memory (.copyBlock 1)) [unaligned 1],
  block 65048 (.memory (.initBlock 2)) [unaligned 2],
  block 65047 (.memory (.copyBlock 4)) [unaligned 4],
  load 74 (.ldind .i4) (prefixes := [unaligned 1]),
  store 85 (.stind .i8) [unaligned 2]]

/-- `ldobj` and `stobj` of primitive, aggregate, enum and vector types, whose type tokens the
    test encoder cannot write. -/
private def objectEmitted : List IndirectCase := [
  typed 113 intType (.ldobj intType), typed 113 sbyteType (.ldobj sbyteType),
  typed 113 word (.ldobj word), typed 129 intType (.stobj intType),
  typed 129 sbyteType (.stobj sbyteType), typed 113 aggregateType (.ldobj aggregateType),
  typed 129 aggregateType (.stobj aggregateType), typed 113 enumType (.ldobj enumType),
  typed 113 vectorType (.ldobj vectorType)]

/-- Each emits other than the decoded instruction: a wrong width, sign, alignment or operation,
    a runtime-model load or store, a kind or prefix extraction refuses, and an access form at an
    unrelated opcode. -/
private def indirectForged : List IndirectCase := [
  -- Width.
  load 70 (.ldind .i4), load 73 (.ldind .u1), load 74 (.ldind .i8),
  load 76 (.ldind .i4) .word64, load 77 (.ldind .i8) .native,
  load 70 (.memory .load128), store 82 (.stind .i4), store 84 (.stind .i8),
  store 85 (.stind .i4), store 223 (.stind .i2),
  -- Sign.
  load 70 (.ldind .u1), load 71 (.ldind .i1), load 72 (.ldind .u2), load 73 (.ldind .i2),
  -- Runtime-model transfers of the right width, which no raw `ldind` or `stind` decodes to.
  load 74 (.loadScalar 4 false), load 70 (.loadScalar 1 true), store 84 (.stobj intType),
  -- Alignment and operation.
  block 65047 (.memory (.copyBlock 1)), block 65048 (.memory (.initBlock 4)),
  block 65047 (.memory (.copyBlock 8)) [unaligned 1],
  block 65048 (.memory (.initBlock 2)) [unaligned 4],
  block 65047 (.memory (.initBlock 8)), block 65048 (.memory (.copyBlock 8)),
  -- Kinds and prefixes extraction refuses.
  block 65047 (.memory (.copyBlock 3)) [unaligned 3],
  load 74 (.ldind .i4) (prefixes := [i 65043]),
  load 78 (.ldind .i4) .other, load 79 (.ldind .i8) .other,
  load 80 (.ldind .i) .other, store 81 (.stind .i8), store 86 (.stind .i4),
  store 87 (.stind .i8),
  -- Access forms at other opcodes.
  load 108 (.loadScalar 8 false) .other, load 108 (.ldind .i8) .other,
  load 107 (.ldind .i4) .other]

/-- Forged emissions at operands the test encoder cannot write: wrong widths and signs of `ldobj`
    and `stobj`, field accesses at operand types extraction refuses, and calls emitting an
    `ldind` or `stind`. -/
private def objectForged : List IndirectCase := [
  load 113 (.loadScalar 2 false) (operand := .type intType),
  load 113 (.loadScalar 4 true) (operand := .type intType),
  load 113 (.loadScalar 1 false) (operand := .type sbyteType),
  load 113 (.ldind .i8) .word64 (operand := .type word),
  store 129 (.stind .i1) (operand := .type intType),
  store 129 (.stind .i8) (operand := .type sbyteType),
  typed 113 aggregateType (.loadScalar 4 false), typed 129 aggregateType (.ldobj aggregateType),
  typed 113 enumType (.loadScalar 2 false), typed 113 vectorType (.memory .load256),
  -- Floating-point and pointer operands, which extraction refuses.
  typed 113 (.atom runtime "System.Double") (.fieldAt 0 4 false),
  typed 129 (.atom runtime "System.Single") (.setFieldAt 0 8),
  typed 113 (.pointer intType) (.fieldAt 0 1 true),
  load 40 (.ldind .i8) .word64 (operand := .call loadSite),
  store 40 (.stind .i8) (operand := .call storeSite)]

/-- Every emission extraction gives passes the indirect access rule, both flow checks and, where
    the body has no token, every check of the method's evidence. -/
private theorem indirect_emissions_accepted :
    (indirectEmitted.all fun access => access.window && access.flows && access.translates) ∧
    (objectEmitted.all fun access => access.window && access.flows) := by
  decide +kernel

#print axioms indirect_emissions_accepted

/-- Every forged emission fails the indirect access rule, so both flow checks and the method's
    evidence check reject it. -/
private theorem indirect_forgeries_rejected :
    (indirectForged.all fun access => !access.window && !access.flows && !access.translates) ∧
    (objectForged.all fun access => !access.window && !access.flows) := by
  decide +kernel

#print axioms indirect_forgeries_rejected

-- `unaligned.` takes only an access, with an alignment of 1, 2 or 4, and emits nothing.
example : indirectSiteWindow ([unaligned 1, i 105][·]?) 0 (unaligned 1) .nop = false := by decide
example : indirectSiteWindow ([unaligned 1, i 74][·]?) 0 (unaligned 1) .nop = true := by decide
example : indirectSiteWindow ([unaligned 8, i 74][·]?) 0 (unaligned 8) .nop = false := by decide
example : indirectSiteWindow ([unaligned 1][·]?) 0 (unaligned 1) .nop = false := by decide
example : indirectSiteWindow ([i 65043, i 74][·]?) 0 (i 65043) .nop = false := by decide

private def pushHoleRaw (opcode : Nat) := raw [i opcode, i 38, i 2, i 42] [word]
private def pushHoleFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, unknown 1]
private def pushHoleStates : ScalarCertificate := [some [], some [.other], some [], some [.word64]]
private def pushHoleCode (emitted : Instruction) : List Instruction :=
  [emitted, .pop, .ldarg 0, .ret]
example : ScalarFlowValid (pushHoleRaw 20) pushHoleFeatures
    (pushHoleStates.set 1 (some [.nullObject])) (pushHoleCode .ldnull) := by decide
-- `ldnull` has one canonical null; the byref null of `Unsafe.NullRef` is a different value.
example : ¬ ScalarFlowValid (pushHoleRaw 20) pushHoleFeatures
    (pushHoleStates.set 1 (some [.nullObject])) (pushHoleCode (.memory .nullRef)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 20) pushHoleFeatures
    (pushHoleStates.set 1 (some [.nullObject])) (pushHoleCode (.ldc_i8 0)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 35) pushHoleFeatures pushHoleStates
    (pushHoleCode (.ldc_i8 0)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 35) pushHoleFeatures pushHoleStates
    (pushHoleCode (.ldc_i4 0)) := by decide

/-- A class with a field at raw index 1, read by `ldarg.0; ldfld; ret`. -/
private def account : TypeExpr := .object "Scope" "Scope.Account"
private def balance : FieldRef :=
  { owner := account, index := 1, type := word, name := name!"balance" }
private def fieldRaw : RawMethod :=
  { raw [i 2, i 123 (.field account 1 word name!"balance" false), i 42] [account] with
    maxStack := 1 }
private def fieldFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1]
private def fieldStates : ScalarCertificate := [some [], some [.object], some [.word64]]
private def fieldCode (access : Instruction) : List Instruction := [.ldarg 0, access, .ret]
-- The scalar check and the code equation accept the load of the field the raw operand names.
example : Tests.DecodedFlow fieldRaw fieldFeatures fieldStates (fieldCode (.ldfld balance)) := by
  decide +kernel
example : ¬ ScalarFlowValid fieldRaw fieldFeatures fieldStates
    (fieldCode (.stfld balance)) := by decide

/-- A class-typed field at raw index 1 of `Scope.Node`, holding another node. -/
private def node : TypeExpr := .object "Scope" "Scope.Node"
private def nextField : RawOperand := .field node 1 node name!"next" false
private def next : FieldRef := { owner := node, index := 1, type := node, name := name!"next" }
/-- A scalar field at raw index 0 of `Scope.Node`. -/
private def valueField : RawOperand := .field node 0 word name!"value" false
private def value : FieldRef := { owner := node, index := 0, type := word, name := name!"value" }
private def nextRaw : RawMethod :=
  { raw [i 2, i 123 nextField, i 42] [node] with returnType := node, maxStack := 1 }
private def nextStates : ScalarCertificate := [some [], some [.object], some [.object]]
-- A class-typed field load names its own field; the step reads the slot the field's type gives.
example : Tests.DecodedFlow nextRaw fieldFeatures nextStates (fieldCode (.ldfld next)) := by
  decide +kernel

/-- `raw` as the evidence of a method whose every pc is reachable. -/
private def reachableEvidence (raw : RawMethod) : MethodEvidence :=
  { addEvidence with closed := raw, reachable := raw.code.map fun _ => true }

/-- The evidence of `raw`, every pc reachable, refuses a method emitting `code`. -/
private def EvidenceRefuses (raw : RawMethod) (code : List Instruction) : Prop :=
  ¬ MethodEvidenceValid [] #[] [] objectPlatform [reachableEvidence raw] [] (reachableEvidence raw)
    { addMethod with code }

/-- Code other than the decoding of `raw` is refused by the code equation conjunct alone. -/
private theorem refused_by_code_equation {raw : RawMethod} {code : List Instruction}
    (different : code ≠ methodCode addMethod.profile addMethod.environment addMethod.links
      (raw.code.map fun _ => true) raw) : EvidenceRefuses raw code :=
  fun valid => different valid.code_eq
#print axioms refused_by_code_equation

/-- Evidence refuses a class field load naming another owner, index, held type or name than its
    raw operand. The scalar check skips the operand at this ordinary site, so each refusal is
    proved from the code equation conjunct. -/
theorem forged_field_loads_refused :
    EvidenceRefuses fieldRaw (fieldCode (.ldfld { balance with index := 0 })) ∧
    EvidenceRefuses fieldRaw
      (fieldCode (.ldfld { balance with owner := .object "Scope" "Scope.Other" })) ∧
    EvidenceRefuses fieldRaw
      (fieldCode (.ldfld { balance with type := .atom runtime "System.Int32" })) ∧
    EvidenceRefuses fieldRaw (fieldCode (.ldfld { balance with name := name!"limit" })) ∧
    EvidenceRefuses nextRaw (fieldCode (.ldfld { next with index := 0 })) ∧
    EvidenceRefuses nextRaw (fieldCode (.ldfld { next with owner := account })) :=
  ⟨refused_by_code_equation (by decide +kernel), refused_by_code_equation (by decide +kernel),
    refused_by_code_equation (by decide +kernel), refused_by_code_equation (by decide +kernel),
    refused_by_code_equation (by decide +kernel), refused_by_code_equation (by decide +kernel)⟩
#print axioms forged_field_loads_refused
example : scalarEmissionMatches none none (i 123 nextField) [.object]
    (.ldfld value) = false := by
  decide
example : scalarEmissionMatches none none (i 123 valueField) [.object]
    (.ldfld next) = false := by
  decide
-- A store to a class-typed field takes an object or null as its value; a load is no store.
example : scalarEmissionMatches none none (i 125 nextField) [.object, .object]
    (.stfld next) = true := by decide
example : scalarEmissionMatches none none (i 125 nextField) [.nullObject, .object]
    (.stfld next) = true := by decide
example : scalarEmissionMatches none none (i 125 nextField) [.word64, .object]
    (.stfld next) = false := by decide
example : scalarEmissionMatches none none (i 125 nextField) [.object, .object]
    (.ldfld next) = false := by decide
example : scalarEmissionMatches none none (i 125 valueField) [.word64, .object]
    (.stfld next) = false := by decide
-- The receiver of a field access is an object or null.
example : scalarEmissionMatches none none (i 123 valueField) [.word64]
    (.ldfld value) = false := by
  decide
example : scalarEmissionMatches none none (i 123 valueField) [.reference]
    (.ldfld value) = false :=
  by decide
example : scalarEmissionMatches none none (i 124 valueField) [.word64]
    (.ldflda value) = false := by
  decide
example : scalarEmissionMatches none none (i 124 valueField) [.reference]
    (.ldflda value) = false :=
  by decide
example : scalarEmissionMatches none none (i 125 valueField) [.word64, .object]
    (.stfld value) = true := by decide
example : scalarEmissionMatches none none (i 125 valueField) [.word64, .word64]
    (.stfld value) = false := by decide
-- `ldflda` of a class field is decoded; its step faults, since an object field has no address.
example : scalarEmissionMatches none none (i 124 valueField) [.object]
    (.ldflda value) = true := by
  decide
/-- Whether a `stfld` of a `Scope.Node` field at raw index 0 holding `type` admits a stored
    `value` of that kind. -/
private def storesInto (type : TypeExpr) (value : ScalarKind) : Bool :=
  scalarEmissionMatches none none (i 125 (.field node 0 type name!"value" false))
    [value, .object] (.stfld { owner := node, index := 0, type, name := name!"value" })
/-- The runtime primitive type `name`. -/
private def primitive (name : String) : TypeExpr := .atom runtime name
-- A stored integer has the field's stack kind, `int32` up to 4 bytes and `int64` or native for
-- 8, since the step reads an `int32` only into a narrow slot and an `int64` only into a wide one.
example : storesInto (primitive "System.SByte") .word64 = false := by decide
example : storesInto (primitive "System.Int16") .word64 = false := by decide
example : storesInto (primitive "System.Int32") .word64 = false := by decide
example : storesInto (primitive "System.Int32") .native = false := by decide
example : storesInto (primitive "System.Int64") .word32 = false := by decide
example : storesInto (primitive "System.IntPtr") .word32 = false := by decide
example : storesInto (.enum "E" (primitive "System.Int64")) .word32 = false := by decide
example : storesInto (primitive "System.Int32") .word32 = true := by decide
example : storesInto (primitive "System.Boolean") .word32 = true := by decide
example : storesInto (primitive "System.Char") .word32 = true := by decide
example : storesInto (.enum "E" (primitive "System.Int16")) .word32 = true := by decide
example : storesInto (primitive "System.Int64") .native = true := by decide
example : storesInto (primitive "System.IntPtr") .word64 = true := by decide
-- A field typed as an array of a class holds the array's reference, stored as an object or null;
-- a value array field stores only an array.
private def itemsField : RawOperand := .field node 1 (.array node) name!"items" false
private def items : FieldRef :=
  { owner := node, index := 1, type := .array node, name := name!"items" }
/-- A value-array field at raw index 1 of `Scope.Node`. -/
private def samplesField : RawOperand := .field node 1 (.array word) name!"samples" false
private def samples : FieldRef :=
  { owner := node, index := 1, type := .array word, name := name!"samples" }
example : scalarEmissionMatches none none (i 123 itemsField) [.object]
    (.ldfld items) = true := by
  decide
example : scalarEmissionMatches none none (i 125 itemsField) [.nullObject, .object]
    (.stfld items) = true := by decide
example : scalarEmissionMatches none none (i 123 samplesField) [.object]
    (.ldfld items) = false := by decide
example : scalarEmissionMatches none none (i 125 samplesField)
    [.object, .object] (.stfld samples) = false := by decide
-- A value-array field names its element type; it stores only an array of that element.
example : scalarEmissionMatches none none (i 123 samplesField) [.object]
    (.ldfld samples) = true := by decide
example : scalarEmissionMatches none none (i 123 samplesField) [.object]
    (.ldfld { samples with type := .array (.atom runtime "System.Int64") }) = false := by
  decide
example : scalarEmissionMatches none none (i 123 samplesField) [.object]
    (.ldfld { samples with index := 0 }) = false := by decide
example : scalarEmissionMatches none none (i 123 itemsField) [.object]
    (.ldfld samples) = false := by decide
example : scalarEmissionMatches none none (i 125 samplesField) [.array .unsigned64, .object]
    (.stfld samples) = true := by decide
example : scalarEmissionMatches none none (i 125 samplesField) [.array .signed32, .object]
    (.stfld samples) = false := by decide
example : scalarEmissionMatches none none (i 125 samplesField) [.object, .object]
    (.stfld samples) = false := by decide

/-- `Scope.Pair`, a struct at layout 0, with fields of each kind the step resolves: an integer,
    an enum, a vector, a nested struct and a generic struct instance. -/
private def pairType : TypeExpr := .aggregate "Scope::Scope.Pair" 0
private def modeType : TypeExpr := .enum "Scope::Scope.Mode" intType
private def laneType : TypeExpr :=
  .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1") word
private def innerType : TypeExpr := .aggregate "Scope::Scope.Inner" 1
/-- The field of `Scope.Pair` at raw index `index` holding `type`, as a reference. -/
private def pairField (index : Nat) (type : TypeExpr) : FieldRef :=
  { owner := pairType, index, type, name := name!"item" }
/-- Whether a struct field instruction of `opcode` on the field at `index` holding `type`
    emits `emitted` over `stack`. -/
private def structSite (opcode index : Nat) (type : TypeExpr) (stack : List ScalarKind)
    (emitted : Instruction) : Bool :=
  scalarEmissionMatches none none (i opcode (.field pairType index type name!"item" false))
    stack emitted

/-- A struct field site emits the decoded access of the field its operand names: a load through
    a reference or from a value, an address and a store through a reference, for a field of each
    kind, storing a value of the field's stack kind. -/
theorem struct_field_sites_accepted :
    structSite 123 0 word [.reference] (.ldfld (pairField 0 word)) = true ∧
    structSite 123 0 word [.other] (.ldfld (pairField 0 word)) = true ∧
    structSite 124 0 word [.reference] (.ldflda (pairField 0 word)) = true ∧
    structSite 125 0 word [.word64, .reference] (.stfld (pairField 0 word)) = true ∧
    structSite 125 1 modeType [.word32, .reference] (.stfld (pairField 1 modeType)) = true ∧
    structSite 125 2 laneType [.other, .reference] (.stfld (pairField 2 laneType)) = true ∧
    structSite 125 3 innerType [.other, .reference] (.stfld (pairField 3 innerType)) = true ∧
    structSite 125 4 tupleType [.other, .reference] (.stfld (pairField 4 tupleType)) = true := by
  decide +kernel
#print axioms struct_field_sites_accepted

/-- A struct field site refuses each forged emission: a load where the raw instruction is a
    store, a receiver of the wrong kind, a stored value of another stack kind, and a reference
    naming another index, owner, held type or name than the operand. -/
theorem struct_field_forgeries_refused :
    structSite 125 0 word [.word64, .reference] (.ldfld (pairField 0 word)) = false ∧
    structSite 123 0 word [.object] (.ldfld (pairField 0 word)) = false ∧
    structSite 124 0 word [.other] (.ldflda (pairField 0 word)) = false ∧
    structSite 125 0 word [.word64, .other] (.stfld (pairField 0 word)) = false ∧
    structSite 125 0 word [.word32, .reference] (.stfld (pairField 0 word)) = false ∧
    structSite 123 0 word [.reference] (.ldfld (pairField 1 word)) = false ∧
    structSite 123 0 word [.reference] (.ldfld { pairField 0 word with owner := innerType }) =
      false ∧
    structSite 123 0 word [.reference] (.ldfld (pairField 0 intType)) = false ∧
    structSite 123 0 word [.reference] (.ldfld { pairField 0 word with name := name!"other" }) =
      false := by
  decide +kernel
#print axioms struct_field_forgeries_refused

-- `ldstr` loads exactly its own text, nothing else loads a literal, and a folded throw's
-- message emits nothing.
example : scalarEmissionMatches none none (i 114 (.text "a")) []
    (.memory (.stringLiteral "a")) = true := by decide
example : scalarEmissionMatches none none (i 114 (.text "a")) []
    (.memory (.stringLiteral "b")) = false := by decide
example : scalarEmissionMatches none none (i 0) [] (.memory (.stringLiteral "a")) = false := by
  decide
example : scalarEmissionMatches (some .interior) none (i 114 (.text "a")) []
    (.memory (.stringLiteral "a")) = false := by decide
example : scalarEmissionMatches none none (i 114 (.text "a")) [] .nop = false := by decide

/-- A genuine open guard declaration with the element substituted in the closed reference. -/
private def guardSite (name : String) (element : TypeExpr) (comparison := false) : CallSite :=
  let key := (MetadataName.ofBytes? (bytesOf name)).getD ⟨0⟩
  let null := name == "ThrowIfNull"
  let label := TypeExpr.object runtimeScope "System.String"
  let owner := if null then "System.ArgumentNullException" else "System.ArgumentOutOfRangeException"
  let parameters (type : TypeExpr) := if null then [.atom runtimeScope "System.Object", label]
    else if comparison then [type, type, label] else [type, label]
  let signature := if null then "System.Object,System.String"
    else if comparison then "!!0,!!0,System.String" else "!!0,System.String"
  let arguments := if null then [] else [element]
  { declared := { convention := if null then 0 else 0x10, parameters := parameters (.parameter 0) }
    method :=
      { owner := .atom runtimeScope owner, name := key, hasThis := false,
        genericArity := arguments.length, returnType := .void, parameters := parameters element,
        methodArguments := arguments }
    name, target := .external s!"{runtimeScope}::System.Void {owner}::{name}({signature})"
    typeArguments := arguments, parameterCount := (parameters element).length,
    returnsValue := false }

/-- Every guard keeps its exact call. A different shape or a floating element is refused. -/
theorem guard_decoding :
    let uint := TypeExpr.atom runtimeScope "System.UInt32"
    let unary := ["ThrowIfZero", "ThrowIfNegative", "ThrowIfNegativeOrZero"]
    let binary := ["ThrowIfEqual", "ThrowIfNotEqual", "ThrowIfGreaterThan", "ThrowIfLessThan",
      "ThrowIfGreaterThanOrEqual", "ThrowIfLessThanOrEqual"]
    Tests.ModelOperands.checks (guardSite "ThrowIfNull" uint) = true ∧
    (unary.all (fun name => Tests.ModelOperands.checks (guardSite name uint))) = true ∧
    (binary.all (fun name => Tests.ModelOperands.checks (guardSite name uint true))) = true ∧
    (unary ++ binary).all (fun name => decide (Tests.ModelOperands.decoded
      (guardSite name (.atom runtimeScope "System.Double") (binary.contains name)) =
        liveHoleAt 0 40)) = true ∧
    runtimeModel {} .call (guardSite "ThrowIfNegative" uint).method =
      some (.memory (.zeroGuard .negative 32 false)) ∧
    runtimeModel {} .call (guardSite "ThrowIfNegative" (.atom runtimeScope "System.Int32")).method =
      some (.memory (.zeroGuard .negative 32 true)) ∧
    runtimeModel {} .call (guardSite "ThrowIfNull" uint).method = some (.memory .throwIfNull) := by
  decide +kernel

#print axioms guard_decoding
-- A narrow guard reads the low bits of its stack slot with the declared signedness, and an
-- operand of another width is ill-typed.
example : (guardOperand 8 true (.i32 0xFF#32)).map ZeroGuard.negative.throws = some true := by
  decide
example : (guardOperand 8 false (.i32 0xFF#32)).map ZeroGuard.negative.throws = some false := by
  decide
example : guardOperand 16 true (.i32 0x00018000#32) = some (-32768) := by decide
example : guardOperand 8 false (.i32 0x80#32) = some 128 := by decide
example : ComparisonGuard.greaterThan.throws 128 127 = true := by decide
example : guardOperand 8 true (.i32 0x80#32) = some (-128) := by decide
example : ComparisonGuard.greaterThan.throws (-128) 127 = false := by decide
example : guardOperand 64 true (.i32 0#32) = none := by decide
example : guardOperand 32 true (.i64 0#64) = none := by decide
example : (guardOperand 64 false (.i64 0xFFFFFFFFFFFFFFFF#64)).map ZeroGuard.negative.throws =
    some false := by decide
-- A typed size instruction and a retained SizeOf call have different literal encodings.
private def sizeRaw (instruction : RawInstruction) := raw [instruction, i 38, i 2, i 42] [word]
private def sizeStates : ScalarCertificate := [some [], some [.word32], some [], some [.word64]]
private def sizeCode (bits : W32) : List Instruction := [.ldc_i4 bits, .pop, .ldarg 0, .ret]
private def sizeAt (instruction : RawInstruction) (bits : W32) : Bool :=
  decide (ScalarFlowValid (sizeRaw instruction) pushHoleFeatures sizeStates (sizeCode bits))
/-- A typed size site must bind the operand and resolve to the stated byte width. -/
private def typedSizeAt (type emitted : TypeExpr) (bits : Nat) : Bool :=
  let environment : LayoutEnvironment := {
    rawLayouts := [{ identity := "Fixture::Packet", explicit := false, packing := 0,
                      declaredSize := 24, fields := [] }]
    layouts := #[⟨⟨24, []⟩, 1⟩] }
  decide (ScalarFlowValid (sizeRaw (i 65052 (.type type))) pushHoleFeatures sizeStates
    [.sizeof emitted, .pop, .ldarg 0, .ret]) && (environment.valueShape type).size? == some bits

/-- The decoder keeps a sizeof operand: with equal layout sizes, the scalar check and the code
    equation accept the operand's own struct and refuse another. -/
private theorem sizeof_equal_layouts :
    let a := TypeExpr.aggregate "Fixture::A" 0
    let b := TypeExpr.aggregate "Fixture::B" 1
    let row : RawLayout := {
      identity := "Fixture::A", explicit := false, packing := 0, declaredSize := 0
      fields := [{ type := .signed32 }] }
    let layout : ComputedLayout := ⟨⟨4, [⟨0, 4, false⟩]⟩, 4⟩
    let rows := [row, { row with identity := "Fixture::B" }]
    let environment : LayoutEnvironment := { rawLayouts := rows, layouts := #[layout, layout] }
    let input := sizeRaw (i 65052 (.type a))
    let valid := fun type => Tests.DecodedFlow input pushHoleFeatures sizeStates
      [.sizeof type, .pop, .ldarg 0, .ret]
    LayoutsValid rows environment.layouts .x64 ∧ environment.valueShape a = .aggregate 4 ∧
      environment.valueShape b = .aggregate 4 ∧ valid a ∧ ¬ valid b := by decide +kernel
#print axioms sizeof_equal_layouts

/-- Evidence refuses a sizeof naming another struct than its raw operand, through the code
    equation conjunct. -/
theorem sizeof_other_struct_refused :
    EvidenceRefuses (sizeRaw (i 65052 (.type (.aggregate "Fixture::A" 0))))
      [.sizeof (.aggregate "Fixture::B" 1), .pop, .ldarg 0, .ret] :=
  refused_by_code_equation (by decide +kernel)
#print axioms sizeof_other_struct_refused

private def sizeOfSite (type : TypeExpr) : CallSite := {
  declared := { convention := 0x10, returnType := intType },
  method := {
    owner := .atom runtime "System.Runtime.CompilerServices.Unsafe", name := name!"SizeOf",
    hasThis := false, genericArity := 1, returnType := intType, parameters := [],
    methodArguments := [type] },
  name := "SizeOf",
  target := .external (runtime ++ "::System.Int32 System.Runtime.CompilerServices.Unsafe::SizeOf(\
    )"),
  typeArguments := [type], parameterCount := 0, returnsValue := true }
private def vector128 : TypeExpr := .apply
  (.constructor
    "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"
    "System.Runtime.Intrinsics.Vector128`1") word
private def packet : TypeExpr := .aggregate "Fixture::Packet" 0
/-- `sizeof` retains exact widths and rejects unsupported pointer and void types; a call of
    `Unsafe.SizeOf` keeps its call, so a constant emitted for it is refused at any width. -/
private theorem size_instruction_cases :
    (typedSizeAt intType intType 4 = true) ∧
    (typedSizeAt nativeType nativeType 8 = true) ∧
    (typedSizeAt packet packet 24 = true) ∧
    (typedSizeAt intType intType 7 = false) ∧
    (typedSizeAt (.pointer word) (.pointer word) 8 = false) ∧
    (sizeAt (i 40 (.call (sizeOfSite intType))) 4 = false) ∧
    (sizeAt (i 40 (.call (sizeOfSite vector128))) 16 = false) ∧
    (sizeAt (i 40 (.call (sizeOfSite packet))) 24 = false) ∧
    (sizeAt (i 40 (.call (sizeOfSite intType))) 5 = false) := by
  decide +kernel

#print axioms size_instruction_cases
private def otherSite : CallSite := { sizeOfSite intType with
  name := "Other", target := .external (runtime ++ "::System.Int32 System.Runtime.CompilerServices.Unsafe::Other()") }
/-- Size intrinsics require the expected declaring identity. -/
private theorem size_identity_cases :
    (sizeAt (i 40 (.call otherSite)) 4 = false) ∧
    (sizeAt (i 40 (.call { sizeOfSite intType with declared.returnType := .parameter 0 }))
      4 = false) ∧
    (sizeAt (i 40 (.call { sizeOfSite intType with
        method.owner := .atom "Forged" "System.Runtime.CompilerServices.Unsafe" }))
      4 = false) := by
  decide +kernel

#print axioms size_identity_cases

-- Compare-and-branch: exact encoding, one wrapper exactly for native/int32, and no mixed unsigned form.
private def branchRaw (opcode : Nat) (parameters : List TypeExpr) :=
  { raw [i 2, i 3, i opcode (.target 3), i 42] parameters with returnType := .void }
private def branchFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 0]
private def branchStates (left right : ScalarKind) : ScalarCertificate := [some [], some [left], some [right, left], some []]
private def branchCode (emitted : Instruction) : List Instruction :=
  [.ldarg 0, .ldarg 1, emitted, .ret]
private def branchAt (opcode : Nat) (left right : ScalarKind) (emitted : Instruction) : Bool :=
  let parameters := [left, right].map fun | .native => nativeType | .word32 => intType | .word64 => word | _ => .byref word
  decide (ScalarFlowValid (branchRaw opcode parameters) branchFeatures (branchStates left right)
    (branchCode emitted))
private def branches : List (Nat × Instruction) := [
  (46, .beq 3), (47, .bge 3), (48, .bgt 3), (49, .ble 3), (50, .blt 3), (51, .bne_un 3),
  (52, .bge_un 3), (53, .bgt_un 3), (54, .ble_un 3), (55, .blt_un 3), (59, .beq 3), (60, .bge 3),
  (61, .bgt 3), (62, .ble 3), (63, .blt 3), (64, .bne_un 3), (65, .bge_un 3), (66, .bgt_un 3),
  (67, .ble_un 3), (68, .blt_un 3)]
/-- Branch encodings retain operand kinds and the raw opcode family. -/
private theorem branch_encoding_cases :
    (branches.all (fun (opcode, emitted) => branchAt opcode .word64 .word64 emitted) = true) ∧
    (branches.all (fun (opcode, emitted) => branchAt opcode .word32 .word32 emitted) = true) ∧
    (branches.all (fun (opcode, _) => !branchAt opcode .word64 .word64 (if opcode ∈ [50, 63]
      then .bge 3 else .blt 3)) = true) ∧
    (branches.all (fun (opcode, emitted) => branchAt opcode .native .word32
      emitted == (opcode ∈ [46, 47, 48, 49, 50, 59, 60, 61, 62, 63])) = true) ∧
    (branches.all (fun (opcode, emitted) => branchAt opcode .word32 .native
      emitted == (opcode ∈ [46, 47, 48, 49, 50, 59, 60, 61, 62, 63])) = true) ∧
    (branches.all (fun (opcode, emitted) => !branchAt opcode .native .word64 emitted) = true) ∧
    (branches.all (fun (opcode, emitted) => !branchAt opcode .word32 .word64 emitted) = true) ∧
    (branches.all (fun (opcode, emitted) => branchAt opcode .reference .reference emitted ==
      (opcode ∈ [46, 51, 52, 53, 54, 55, 59, 64, 65, 66, 67, 68])) = true) := by
  decide +kernel

#print axioms branch_encoding_cases

example (valid : ScalarFlowValid addRaw addFeatures addStates addCode) :
    scalarEmissionMatches none none (i 88) [.word64, .word64] .add = true :=
  valid.instruction_checked (live := fun _ => true) (decodeSite := fun _ => Instruction.ofRaw)
    (pc := 2) (by decide) rfl rfl rfl rfl rfl

#print axioms external_call_validated

/-- External signatures normalize closed generic storage without accepting a scalar argument. -/
theorem closed_generic_fill_signature :
    let element := TypeExpr.aggregate ("Scope::Pair`1<" ++ runtime ++ "::System.UInt64>") 0
    let site : CallSite := {
      declared := { convention := 0x20, parameters := [element] },
      method := {
        owner := .apply (.constructor runtime "System.Span`1") element, name := name!"Fill",
        hasThis := true, genericArity := 0, returnType := .void, parameters := [element] },
      name := "Fill",
      target := .external (runtime ++
        "::System.Void System.Span`1<Pair`1<System.UInt64>>::Fill(!0)"), typeArguments := [],
      parameterCount := 1, returnsValue := false }
    scalarTransfer (raw []) (i 40 (.call site)) [.other, .reference] = some [] ∧
      scalarTransfer (raw []) (i 40 (.call { site with method.parameters := [word] }))
        [.word64, .reference] = none := by decide +kernel
#print axioms closed_generic_fill_signature

/-- The ECMA-335 augments make int32-to-`native unsigned int` coercion sign-extending, unlike
    the 2012 text; scalar flow admits no implicit int32-to-native coercion in either direction. -/
theorem no_implicit_native_coercion :
    let unsignedNative : TypeExpr := .atom runtime "System.UIntPtr"
    ([nativeType, unsignedNative].all fun home =>
      let method := { addRaw with locals := [home], parameters := [home], returnType := home }
      let call := i 40 (.call { site with parameterCount := 1, method.parameters := [home] })
      scalarTransfer method (i 10) [.word32] == none &&
        scalarTransfer method (i 10) [.native] == some [] &&
        scalarTransfer method (i 16 (.argument 0)) [.word32] == none &&
        scalarTransfer method (i 16 (.argument 0)) [.native] == some [] &&
        scalarTransfer method (i 42) [.word32] == none &&
        scalarTransfer method (i 42) [.native] == some [] &&
        scalarTransfer method call [.word32] == none &&
        scalarTransfer method call [.native] == some [.word64]) = true := by
  decide +kernel
#print axioms no_implicit_native_coercion

/-- The checked interpreter likewise never widens an int32 into a native-width home. -/
theorem native_home_rejects_int32 :
    CIL.Safety.localNumber .word64 (.i32 (-1)) = .error .invalidState ∧
      CIL.Safety.localNumber .word64 (.i64 (-1)) = .ok (2 ^ 64 - 1) :=
  ⟨rfl, rfl⟩
#print axioms native_home_rejects_int32

/-- Every evidence record in this file carries the bytes of its own original body, so the
    certificate checks above fail for the reason they state and not for a missing body. -/
theorem fixtures_carry_their_bodies :
    ([addEvidence, literalEvidence, convertEvidence, floatEvidence 107, floatEvidence 108,
      localEvidence, argumentEvidence, faultLocalEvidence, nativeHomeEvidence,
      nativeReturnEvidence, holeEvidence 88 holeStates, holeEvidence 149 holeStates] ++
      (arithmeticFlagCases ++ arithmeticFlagMutations).map fun entry =>
        binaryEvidence entry.1).all (fun item => bodyMatches item.body item.original []) =
      true := by
  decide +kernel
#print axioms fixtures_carry_their_bodies

/-! ## Only the kernel decides the body and metadata check

The elaborator evaluates a call by name, so a certificate whose evidence carries a computed
metadata slice would be unfolded again at every use. `bodyMatches` is irreducible, so `decide`
refuses at once, within a small heartbeat budget, and `decide +kernel` decides. -/

set_option maxHeartbeats 20000 in
/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : BodyDecodes [] objectPlatform scope addEvidence.body addEvidence.original
    [] addEvidence.signature := by
  decide

set_option maxHeartbeats 20000 in
/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : TranslationValid [] #[] [] objectPlatform [addEvidence] [] [addMethod] := by decide

set_option maxHeartbeats 20000 in
/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence addMethod := by
  decide

/-- A method with eight times the parameters and four times the locals of `addRaw`. -/
private def wideRaw : RawMethod :=
  { addRaw with parameters := List.replicate 16 word, locals := List.replicate 8 intType }

-- The fixture encoder reduces in the elaborator, within a small budget, at both sizes.
set_option maxHeartbeats 100000 in
example : (encodeBody scope addRaw).isSome = true := by decide

set_option maxHeartbeats 100000 in
example : (encodeBody scope wideRaw).isSome = true := by decide
example : (encodeBody scope addRaw).isSome = true := by decide +kernel
example : BodyDecodes [] objectPlatform scope addEvidence.body addEvidence.original
    [] addEvidence.signature := by
  decide +kernel
example : MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence addMethod := by
  decide +kernel
example : MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence addMethod := by decide +kernel

/-- A method that fills a block through its byref argument with an unprefixed `initblk`. -/
private def blockInit : RawMethod :=
  { raw [i 2, i 22, i 22, i 65048, i 42] [.byref intType] with
    maxStack := 3, returnType := .void }

/-- A hole at a reachable block initialization is refused: the scalar check compares it with
    the block operation the decoder gives that pc. -/
theorem decoded_block_hole_refused :
    ¬ ScalarFlowValid blockInit ([0, 1, 2, 3, 0].map unknown)
      [some [], some [.reference], some [.word32, .reference],
        some [.word32, .word32, .reference], some []]
      ((Instruction.ofRawCode none blockInit.code).set 3 (.unadmitted 65048)) := by
  decide +kernel
#print axioms decoded_block_hole_refused

/-- The certificate refused above is valid over the code the decoder gives `blockInit`, so the
    refusal comes from the hole at pc 3. -/
theorem decoded_block_init_valid :
    ScalarFlowValid blockInit ([0, 1, 2, 3, 0].map unknown)
      [some [], some [.reference], some [.word32, .reference],
        some [.word32, .word32, .reference], some []]
      (Instruction.ofRawCode none blockInit.code) := by
  decide +kernel
#print axioms decoded_block_init_valid

/-- Evidence refuses an extra static site on a method whose body has none. -/
theorem addition_rejects_extra_static_site :
    let site : StaticDescriptor := { identity := 1, field := value, bytes := [] }
    let altered := { addMethod with staticSites := [(0, site)] }
    ¬ MethodEvidenceValid [] #[] [] objectPlatform [addEvidence] [] addEvidence altered := by
  decide +kernel
#print axioms addition_rejects_extra_static_site

/-- Valid evidence gives the full scalar encoding check at every reachable pc, from its scalar
    check and its code equation conjunct. -/
theorem checked_method_encodings {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {pins : List AssemblyPin} {platform : PlatformTable} {all : List MethodEvidence} {imports : List ImportSlot}
    {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method)
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole} {feature : FeatureState}
    {stack : List ScalarKind} {emitted : Instruction}
    (rawAt : item.closed.code[pc]? = some instruction)
    (roleAt : (foldRoles item.closed.code)[pc]? = some role)
    (featureAt : item.featureStates[pc]? = some (some feature))
    (stackAt : item.scalarStates[pc]? = some (some stack))
    (emittedAt : method.code[pc]? = some emitted) :
    scalarEmissionMatches role (rawBefore (item.closed.code[·]?) pc) instruction stack emitted =
      true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨flow, binding⟩, _⟩ := valid
  exact flow.instruction_checked (binding.trans (methodCode_eq ..)) rawAt roleAt featureAt stackAt
    emittedAt

#print axioms checked_method_encodings

/-- A literal load with a different owner layout cannot use decoded evidence. -/
theorem wrong_decoded_owner_refused (item : MethodEvidence) :
    let owner := TypeExpr.aggregate "Fixture" 0
    let source := raw [i 123 (.field owner 0 intType (name!"Field") false)]
    let evidence := { item with closed := source }
    let field : FieldRef := ⟨.aggregate "Fixture" 1, 0, intType, name!"Field"⟩
    ¬ MethodEvidenceValid [] #[] [] objectPlatform [evidence] [] evidence
      { addMethod with code := [.ldfld field] } := by
  intro owner source evidence field valid
  have different : [Instruction.ldfld field] ≠
      methodCode addMethod.profile addMethod.environment addMethod.links
        item.reachable source := by
    rw [methodCode_eq]
    simp only [methodInstruction, indexedRead?_eq]
    change [Instruction.ldfld field] ≠ [if !item.reachable.toArray[0]?.getD false then
      .unadmitted 123 else .ldfld { field with owner := owner }]
    cases item.reachable.toArray[0]?.getD false <;> decide +kernel
  exact different valid.code_eq
#print axioms wrong_decoded_owner_refused

end Tests.ScalarEvidence
