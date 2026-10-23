import CIL.Extraction.Translation
import CIL.Safety.Frames

namespace Tests.ScalarEvidence
open CIL CIL.Extraction

private def runtime := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def word : TypeExpr := .atom runtime "System.UInt64"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def nativeType : TypeExpr := .atom runtime "System.IntPtr"
private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (code : List RawInstruction) (parameters : List TypeExpr := [word, word]) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := word, parameters, locals := [], initLocals := true, maxStack := 2,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩
private def unknown (count : Nat) := state (List.replicate count none)

private def arithmetic : List (Nat × Op) := [
  (88, .add), (89, .sub), (90, .mul), (91, .divide true false), (92, .divide false false),
  (93, .divide true true), (94, .divide false true), (95, .band), (96, .bor), (97, .bxor),
  (98, .shl), (99, .shr), (100, .shrUn), (214, .checkedArithmetic .add true),
  (215, .checkedArithmetic .add false), (216, .checkedArithmetic .mul true),
  (217, .checkedArithmetic .mul false), (218, .checkedArithmetic .sub true),
  (219, .checkedArithmetic .sub false), (65025, .eq), (65026, .gt), (65027, .gtu),
  (65028, .lt), (65029, .ltu)]
example : arithmetic.all (fun (opcode, operation) => scalarOpMatches (i opcode) [.word32, .word32] operation) = true := by decide
example : arithmetic.all (fun (opcode, _operation) =>
    !scalarOpMatches (i opcode) [.word32, .word32] (if opcode == 88 then .sub else .add)) = true := by decide
example : scalarOpMatches (i 101) [.word64] .neg = true := by decide
example : scalarOpMatches (i 102) [.word64] .bnot = true := by decide
example : scalarOpMatches (i 101) [.word64] .bnot = false := by decide
example : scalarOpMatches (i 88 (.integer 0)) [.word64, .word64] .add = false := by decide
example : scalarOpMatches (i 88) [.other, .other] .add = false := by decide
example : scalarOpMatches (i 88) [.reference, .word32] .add = false := by decide
example : scalarOpMatches (i 88) [.native, .word64] (.nativeBinary .add) = false := by decide
example : scalarOpMatches (i 88) [.word32, .native] (.nativeBinary .add) = true := by decide
example : scalarOpMatches (i 88) [.word32, .native] .add = false := by decide
example : scalarOpMatches (i 88) [.word64, .word64] (.nativeBinary .add) = false := by decide
example : scalarOpMatches (i 88) [.word32, .native] (.nativeBinary .sub) = false := by decide

private def arithmeticFlagMutations : List (Nat × Op) := [
  (91, .divide false false), (91, .divide true true), (91, .divide false true),
  (92, .divide true false), (92, .divide false true), (92, .divide true true),
  (93, .divide false true), (93, .divide true false), (93, .divide false false),
  (94, .divide true true), (94, .divide false false), (94, .divide true false),
  (214, .checkedArithmetic .add false), (215, .checkedArithmetic .add true),
  (216, .checkedArithmetic .mul false), (217, .checkedArithmetic .mul true),
  (218, .checkedArithmetic .sub false), (219, .checkedArithmetic .sub true)]
example : arithmeticFlagMutations.all (fun (opcode, operation) =>
    !scalarOpMatches (i opcode) [.word64, .word64] operation) = true := by decide

private def conversions : List (Nat × Op) := [
  (103, .convI1), (104, .convI2), (105, .convI4), (106, .convI8), (109, .convU4), (110, .convU8),
  (130, .checkedConvert 8 true true), (131, .checkedConvert 16 true true),
  (132, .checkedConvert 32 true true), (133, .checkedConvert 64 true true),
  (134, .checkedConvert 8 false true), (135, .checkedConvert 16 false true),
  (136, .checkedConvert 32 false true), (137, .checkedConvert 64 false true),
  (138, .checkedConvert 64 true true), (139, .checkedConvert 64 false true),
  (179, .checkedConvert 8 true false), (180, .checkedConvert 8 false false),
  (181, .checkedConvert 16 true false), (182, .checkedConvert 16 false false),
  (183, .checkedConvert 32 true false), (184, .checkedConvert 32 false false),
  (185, .checkedConvert 64 true false), (186, .checkedConvert 64 false false),
  (209, .convU2), (210, .convU1), (211, .convI8), (212, .checkedConvert 64 true false),
  (213, .checkedConvert 64 false false), (224, .convU)]
example : conversions.all (fun (opcode, operation) => scalarOpMatches (i opcode) [.word64] operation) = true := by decide
example : scalarOpMatches (i 106) [.word32] .convU8 = false := by decide
example : scalarOpMatches (i 133) [.word32] (.checkedConvert 64 true false) = false := by decide
example : scalarOpMatches (i 133) [.word32] (.checkedConvert 64 false true) = false := by decide
example : scalarOpMatches (i 133) [.word32] .convI8 = false := by decide
example : scalarOpMatches (i 106) [.word32] (.checkedConvert 64 true false) = false := by decide
example : scalarOpMatches (i 183) [.word64] (.checkedConvert 16 true false) = false := by decide

example : scalarOpMatches (i 21) [] (.const32 (BitVec.ofInt 32 (-1))) = true := by decide
example : scalarOpMatches (i 30) [] (.const32 8) = true := by decide
example : scalarOpMatches (i 31 (.integer (-128))) [] (.const32 (BitVec.ofInt 32 (-128))) = true := by decide
example : scalarOpMatches (i 31 (.integer 128)) [] (.const32 128) = false := by decide
example : scalarOpMatches (i 32 (.integer (-2147483648))) [] (.const32 2147483648) = true := by decide
example : scalarOpMatches (i 32 (.integer 2147483648)) [] (.const32 2147483648) = false := by decide
example : scalarOpMatches (i 33 (.integer (-9223372036854775808))) [] (.const64 9223372036854775808) = true := by decide
example : scalarOpMatches (i 33 (.integer 9223372036854775807)) [] (.const64 9223372036854775807) = true := by decide
example : scalarOpMatches (i 33 (.integer (-1))) [] (.const64 18446744073709551615) = true := by decide
example : scalarOpMatches (i 33 (.integer (-9223372036854775808))) [] (.const64 0) = false := by decide
example : scalarOpMatches (i 33 (.integer (-9223372036854775808))) [] (.const64 9223372036854775809) = false := by decide
example : scalarOpMatches (i 33 (.integer 9223372036854775808)) [] (.const64 9223372036854775808) = false := by decide
example : scalarOpMatches (i 33) [] (.const64 0) = false := by decide

private def addRaw := raw [i 2, i 3, i 88, i 42]
private def addFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 1]
private def addStates : ScalarCertificate := [some [], some [.word64], some [.word64, .word64], some [.word64]]
private def addCode : List Op := [.arg 0, .arg 1, .add, .ret]
private def addEvidence : MethodEvidence := {
  original := addRaw, arguments := [], closed := addRaw,
  parameterInput := { arguments := [.field .unsigned64, .field .unsigned64], locals := [], code := [.load 0, .load 1, .other, .other] },
  reachable := List.replicate 4 true, featureStates := addFeatures, scalarStates := addStates, layoutUses := [] }
private def addMethod : Method := { locals := [], returnsValue := true, code := addCode }

example : TranslationValid [] #[] [addEvidence] [] [addMethod] := by decide
example : ¬ TranslationValid [] #[] [addEvidence] [] [{ addMethod with code := addCode.set 2 .sub }] := by decide
example : ¬ TranslationValid [] #[] [{ addEvidence with scalarStates := addStates.set 2 (some [.native, .word32]) }] []
    [{ addMethod with code := addCode.set 2 (.nativeBinary .add) }] := by decide
example : ¬ ScalarFlowValid { addRaw with maxStack := 1 } addFeatures addStates addCode := by decide
example : ¬ ScalarFlowValid addRaw addFeatures (addStates.set 0 (some [.word64])) addCode := by decide
example : ¬ ScalarFlowValid addRaw addFeatures (addStates.drop 1) addCode := by decide
example : ¬ ScalarFlowValid addRaw addFeatures addStates (addCode.drop 1) := by decide
example : ¬ ScalarFlowValid addRaw (addFeatures.drop 1) addStates addCode := by decide

private def binaryEvidence (opcode : Nat) : MethodEvidence :=
  { addEvidence with original := { addRaw with code := addRaw.code.set 2 (i opcode) }, closed := { addRaw with code := addRaw.code.set 2 (i opcode) } }
private def binaryMethod (operation : Op) : Method := { addMethod with code := addCode.set 2 operation }
private def arithmeticFlagCases : List (Nat × Op) := [
  (91, .divide true false), (92, .divide false false), (93, .divide true true), (94, .divide false true),
  (214, .checkedArithmetic .add true), (215, .checkedArithmetic .add false),
  (216, .checkedArithmetic .mul true), (217, .checkedArithmetic .mul false),
  (218, .checkedArithmetic .sub true), (219, .checkedArithmetic .sub false)]
example : arithmeticFlagCases.all (fun (opcode, operation) =>
    decide (TranslationValid [] #[] [binaryEvidence opcode] [] [binaryMethod operation])) = true := by decide
example : arithmeticFlagMutations.all (fun (opcode, operation) =>
    decide (¬ TranslationValid [] #[] [binaryEvidence opcode] [] [binaryMethod operation])) = true := by decide

private def literalRaw := raw [i 33 (.integer (-9223372036854775808)), i 42] []
private def literalFeatures : FeatureCertificate := [unknown 0, unknown 1]
private def literalStates : ScalarCertificate := [some [], some [.word64]]
private def literalEvidence : MethodEvidence := {
  original := literalRaw, arguments := [], closed := literalRaw,
  parameterInput := { arguments := [], locals := [], code := [.other, .other] },
  reachable := [true, true], featureStates := literalFeatures, scalarStates := literalStates, layoutUses := [] }
private def literalMethod : Method := { locals := [], returnsValue := true, code := [.const64 9223372036854775808, .ret] }
example : TranslationValid [] #[] [literalEvidence] [] [literalMethod] := by decide
example : ¬ TranslationValid [] #[] [literalEvidence] []
    [{ literalMethod with code := [.const64 9223372036854775809, .ret] }] := by decide

private def convertRaw := raw [i 2, i 133, i 42] [word]
private def convertFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1]
private def convertStates : ScalarCertificate := [some [], some [.word64], some [.word64]]
private def convertEvidence : MethodEvidence := {
  original := convertRaw, arguments := [], closed := convertRaw,
  parameterInput := { arguments := [.field .unsigned64], locals := [], code := [.load 0, .other, .other] },
  reachable := [true, true, true], featureStates := convertFeatures, scalarStates := convertStates, layoutUses := [] }
private def convertMethod : Method := { locals := [], returnsValue := true, code := [.arg 0, .checkedConvert 64 true true, .ret] }
example : TranslationValid [] #[] [convertEvidence] [] [convertMethod] := by decide
example : ¬ TranslationValid [] #[] [convertEvidence] []
    [{ convertMethod with code := [.arg 0, .checkedConvert 64 false true, .ret] }] := by decide
example : ¬ TranslationValid [] #[] [convertEvidence] []
    [{ convertMethod with code := [.arg 0, .checkedConvert 64 true false, .ret] }] := by decide
example : ¬ TranslationValid [] #[] [convertEvidence] []
    [{ convertMethod with code := [.arg 0, .convI8, .ret] }] := by decide

private def floatRaw (opcode : Nat) := raw [i 23, i opcode, i 106, i 42] []
private def floatFeatures : FeatureCertificate := [unknown 0, state [some 1], unknown 1, unknown 1]
private def floatStates : ScalarCertificate := [some [], some [.word32], some [.word32], some [.word64]]
private def floatEvidence (opcode : Nat) : MethodEvidence := {
  original := floatRaw opcode, arguments := [], closed := floatRaw opcode,
  parameterInput := { arguments := [], locals := [], code := List.replicate 4 .other },
  reachable := List.replicate 4 true, featureStates := floatFeatures, scalarStates := floatStates, layoutUses := [] }
private def floatMethod : Method := { locals := [], returnsValue := true, code := [.const32 1, .neg, .convI8, .ret] }
example : FeatureFlowValid (floatRaw 107) .scalar floatFeatures (List.replicate 4 true) floatMethod.code := by decide
example : FeatureFlowValid (floatRaw 108) .scalar floatFeatures (List.replicate 4 true) floatMethod.code := by decide
example : scalarTransfer (floatRaw 107) (i 107) [.word32] = some [.other] := by decide
example : scalarTransfer (floatRaw 108) (i 108) [.word32] = some [.other] := by decide
example : ¬ TranslationValid [] #[] [floatEvidence 107] [] [floatMethod] := by decide
example : ¬ TranslationValid [] #[] [floatEvidence 108] [] [floatMethod] := by decide
example : ¬ ScalarFlowValid (floatRaw 107) floatFeatures (floatStates.set 2 (some [.other])) floatMethod.code := by decide
example : ¬ ScalarFlowValid (floatRaw 108) floatFeatures (floatStates.set 2 (some [.other])) floatMethod.code := by decide
example : scalarTransfer addRaw (i 80) [.reference] = some [.other] := by decide
example : scalarTransfer addRaw (i 150) [.word32, .reference] = some [.other] := by decide
example : scalarTransfer addRaw (i 154) [.word32, .reference] = some [.other] := by decide

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
  ([[], [some 1], [none], [], [none], [none]] : List (List (Option W32))).map fun stack => some ⟨stack, [none]⟩
private def localStates : ScalarCertificate := [some [], some [.word32], some [.other], some [], some [.word32], some [.word64]]
private def localEvidence : MethodEvidence := {
  original := localRaw, arguments := [], closed := localRaw,
  parameterInput := { arguments := [], locals := [.field .signed32], code := List.replicate 6 .other },
  reachable := List.replicate 6 true, featureStates := localFeatures, scalarStates := localStates, layoutUses := [] }
private def localMethod : Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true,
  code := [.const32 1, .neg, .setLocal 0, .local 0, .convI8, .ret] }
example : FeatureFlowValid localRaw .scalar localFeatures (List.replicate 6 true) localMethod.code := by decide
example : ¬ TranslationValid [] #[] [localEvidence] [] [localMethod] := by decide

private def argumentRaw := raw [i 23, i 108, i 16 (.argument 0), i 2, i 106, i 42] [intType]
private def argumentFeatures : FeatureCertificate := [unknown 0, state [some 1], unknown 1, unknown 0, unknown 1, unknown 1]
private def argumentEvidence : MethodEvidence := {
  original := argumentRaw, arguments := [], closed := argumentRaw,
  parameterInput := { arguments := [.field .signed32], locals := [], code := [.other, .other, .store 0, .load 0, .other, .other] },
  reachable := List.replicate 6 true, featureStates := argumentFeatures, scalarStates := localStates, layoutUses := [] }
private def argumentMethod : Method := {
  locals := [], parameterHomes := [(0, .word32)], returnsValue := true,
  code := [.const32 1, .neg, .setLocal 0, .local 0, .convI8, .ret] }
example : FeatureFlowValid argumentRaw .scalar argumentFeatures (List.replicate 6 true) argumentMethod.code := by decide
example : ¬ TranslationValid [] #[] [argumentEvidence] [] [argumentMethod] := by decide

private def mixedRaw := { raw [i 2, i 3, i 88, i 42] [nativeType, intType] with returnType := nativeType }
private def mixedStates : ScalarCertificate := [some [], some [.native], some [.word32, .native], some [.native]]
private def mixedCode : List Op := [.arg 0, .arg 1, .nativeBinary .add, .ret]
example : ScalarFlowValid mixedRaw addFeatures mixedStates mixedCode := by decide
example : ¬ ScalarFlowValid mixedRaw addFeatures mixedStates (mixedCode.set 2 .add) := by decide
example : ¬ ScalarFlowValid addRaw addFeatures addStates (addCode.set 2 (.nativeBinary .add)) := by decide
example : ¬ ScalarFlowValid { mixedRaw with parameters := [nativeType, word] } addFeatures mixedStates mixedCode := by decide

private def site : CallSite := {
  target := .managed 1, typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := word, parameterTypes := [word, word] }
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40 (.call site)) true (.call 0 2) = true := by decide
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40 (.call { site with returnType := intType })) true (.call 0 2) = false := by decide
example : validateManagedCall [⟨[], { addRaw with returnType := intType }⟩] [] (i 40 (.call site)) true (.call 0 2) = false := by decide
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.Int32 Owner::M()", parameterCount := 0, parameterTypes := [], returnType := word })) [] = some [.other] := by decide +kernel
theorem external_call_validated : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M()", parameterCount := 0, parameterTypes := [] })) [] = some [.word64] := by decide +kernel

example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::!!0 Owner::M()", parameterCount := 0, parameterTypes := [], typeArguments := [word] })) [] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::!!0 Owner::M()", parameterCount := 0, parameterTypes := [], typeArguments := [intType] })) [] = some [.other] := by decide +kernel

example : validateManagedCall [⟨[], addRaw⟩] []
    (i 40 (.call { site with parameterTypes := [intType, word] })) true (.call 0 2) = false := by decide
example : scalarTransfer addRaw (i 40 (.call site)) [.word64, .word64] = some [.word64] := by decide
example : scalarTransfer addRaw (i 40 (.call site)) [.other, .word64] = none := by decide
example : scalarTransfer addRaw (i 40 (.call { site with parameterTypes := [intType, word] })) [.word64, .word32] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with parameterTypes := [intType, word] })) [.word32, .word64] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with hasThis := true, parameterTypes := [intType, word] })) [.word64, .word32, .reference] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with hasThis := true, parameterTypes := [intType, word] })) [.word64, .word32, .other] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(System.Int32)", parameterCount := 1, parameterTypes := [intType] })) [.word32] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(System.Int32)", parameterCount := 1, parameterTypes := [word] })) [.word64] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(!!0)", typeArguments := [intType], parameterCount := 1, parameterTypes := [intType] })) [.word32] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(!!0)", typeArguments := [intType], parameterCount := 1, parameterTypes := [word] })) [.word64] = none := by decide +kernel

example : scalarTransfer addRaw (i 40 (.call { site with declaringType := .apply (.constructor "Scope" "Owner`1") intType, target := .external "Scope::!0 Owner`1<System.Int32>::M(!0)", parameterCount := 1, parameterTypes := [intType], returnType := intType })) [.word32] = some [.word32] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with declaringType := .apply (.constructor "Scope" "Owner`1") intType, target := .external "Scope::!0 Owner`1<System.Int32>::M(!0)", parameterCount := 1, parameterTypes := [word], returnType := intType })) [.word64] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with declaringType := .aggregate "Scope::Owner`2<System.Int32,System.UInt64>" 0, target := .external "Scope::!1 Owner`2<System.Int32,System.UInt64>::M(!0,!1)", parameterTypes := [intType, word] })) [.word64, .word32] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(Container`2<System.Int32,System.UInt64>,System.Int32)", parameterTypes := [.aggregate "Scope::Container`2<System.Int32,System.UInt64>" 0, intType] })) [.word32, .other] = some [.word64] := by decide +kernel

private def faultLocalRaw := { raw [i 2, i 10, i 6, i 42] [word] with locals := [intType], returnType := intType }
private def faultLocalFeatures : FeatureCertificate :=
  ([[], [none], [], [none]] : List (List (Option W32))).map fun stack => some ⟨stack, [none]⟩
private def faultLocalStates : ScalarCertificate := [some [], some [.word64], some [], some [.word32]]
private def faultLocalEvidence : MethodEvidence := {
  original := faultLocalRaw, arguments := [], closed := faultLocalRaw,
  parameterInput := { arguments := [.field .unsigned64], locals := [.field .signed32], code := [.load 0, .other, .other, .other] },
  reachable := List.replicate 4 true, featureStates := faultLocalFeatures, scalarStates := faultLocalStates, layoutUses := [] }
private def faultLocalMethod : Method := {
  locals := [.i32 0], localKinds := [.word32], returnsValue := true,
  code := [.arg 0, .setLocal 0, .local 0, .ret] }
example : TranslationValid [] #[] [faultLocalEvidence] [] [faultLocalMethod] := by decide +kernel
example : scalarTransfer faultLocalRaw (i 10) [.word64] = none := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] (.setLocal 0) = true := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.native] (.setLocal 0) = true := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.other] (.setLocal 0) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.reference] (.setLocal 0) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] (.setLocal 1) = false := by decide
example : scalarStoreFault faultLocalRaw (i 10) [.word64] .pop = false := by decide
example : scalarStoreFault { faultLocalRaw with locals := [] } (i 10) [.word64] (.setLocal 0) = false := by decide
example : ¬ ScalarFlowValid faultLocalRaw faultLocalFeatures faultLocalStates
    (faultLocalMethod.code.set 1 (.setLocal 1)) := by decide
example : ¬ TranslationValid [] #[] [faultLocalEvidence] []
    [{ faultLocalMethod with code := faultLocalMethod.code.set 1 .pop }] := by decide
example (memory : Safety.Memory) (reference : Safety.Reference) (bits : W64) :
    Safety.storeLocal memory (.bytes .word32 reference) (.scalar (.i64 bits)) = .error .invalidState := rfl
example (memory : Safety.Memory) (reference : Safety.Reference) (kind : NarrowKind) (bits : W64) :
    Safety.storeLocal memory (.bytes (.narrow kind) reference) (.scalar (.i64 bits)) = .error .invalidState := rfl

private def nativeHomeRaw := raw [i 3, i 16 (.argument 0), i 2, i 110, i 42] [nativeType, word]
private def nativeHomeFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, unknown 1, unknown 1]
private def nativeHomeStates : ScalarCertificate := [some [], some [.word64], some [], some [.native], some [.word64]]
private def nativeHomeEvidence : MethodEvidence := {
  original := nativeHomeRaw, arguments := [], closed := nativeHomeRaw,
  parameterInput := { arguments := [.field .nativeInt, .field .unsigned64], locals := [], code := [.load 1, .store 0, .load 0, .other, .other] },
  reachable := List.replicate 5 true, featureStates := nativeHomeFeatures, scalarStates := nativeHomeStates, layoutUses := [] }
private def nativeHomeMethod : Method := {
  locals := [], parameterHomes := [(0, .word64)], returnsValue := true,
  code := [.arg 1, .setLocal 0, .local 0, .convU8, .ret] }
example : TranslationValid [] #[] [nativeHomeEvidence] [] [nativeHomeMethod] := by decide +kernel
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.word64] = some [] := by decide
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.other] = none := by decide
example : scalarTransfer nativeHomeRaw (i 16 (.argument 0)) [.word32] = none := by decide
example : ¬ ScalarFlowValid nativeHomeRaw nativeHomeFeatures
    (nativeHomeStates.set 1 (some [.other])) nativeHomeMethod.code := by decide

private def nativeReturnRaw := raw [i 2, i 77, i 42] [.byref word]
private def nativeReturnFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1]
private def nativeReturnStates : ScalarCertificate := [some [], some [.reference], some [.native]]
private def nativeReturnEvidence : MethodEvidence := {
  original := nativeReturnRaw, arguments := [], closed := nativeReturnRaw,
  parameterInput := { arguments := [.reference], locals := [], code := [.load 0, .other, .other] },
  reachable := List.replicate 3 true, featureStates := nativeReturnFeatures, scalarStates := nativeReturnStates, layoutUses := [] }
private def nativeReturnMethod : Method := { locals := [], returnsValue := true, code := [.arg 0, .loadScalar 8, .ret] }
example : TranslationValid [] #[] [nativeReturnEvidence] [] [nativeReturnMethod] := by decide +kernel
example : scalarTransfer nativeReturnRaw (i 42) [.native] = some [] := by decide
example : scalarTransfer { nativeReturnRaw with returnType := nativeType } (i 42) [.word64] = some [] := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.other] = none := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.word32] = none := by decide
example : scalarTransfer nativeReturnRaw (i 42) [.native, .word64] = none := by decide
example : ¬ ScalarFlowValid { nativeReturnRaw with returnType := intType }
    nativeReturnFeatures nativeReturnStates nativeReturnMethod.code := by decide

private def byteSpanType : TypeExpr := .apply (.constructor runtime "System.ReadOnlySpan`1") (.atom runtime "System.Byte")
private def byteSpanSite : CallSite := {
  declaringType := byteSpanType, name := ".ctor", target := .external
    (runtime ++ "::System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)"),
  typeArguments := [], parameterCount := 2, parameterTypes := [.pointer .void, intType],
  hasThis := true, returnsValue := false, returnType := .void }
private def byteSpanRaw := { raw [i 2, i 31 (.integer 16), i 115 (.call byteSpanSite), i 42] [.byref word] with returnType := byteSpanType }
private def byteSpanFeatures : FeatureCertificate := [unknown 0, unknown 1, state [some 16, none], unknown 1]
private def byteSpanStates : ScalarCertificate := [some [], some [.reference], some [.word32, .reference], some [.other]]
private def byteSpanCode : List Op := [.arg 0, .const32 16, .memory .spanCreate, .ret]
example : ScalarFlowValid byteSpanRaw byteSpanFeatures byteSpanStates byteSpanCode := by decide +kernel
example : ¬ ScalarFlowValid byteSpanRaw byteSpanFeatures byteSpanStates
    (byteSpanCode.set 2 (.memory (.spanItem 1))) := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .reference] = some [.other] := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .other] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call byteSpanSite)) [.word32, .native] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with target := .external "forged" }))
    [.word32, .reference] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with name := "Other" }))
    [.word32, .reference] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with declaringType := .atom runtime "Other" }))
    [.word32, .reference] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 115 (.call { byteSpanSite with parameterTypes := [.pointer word, intType] }))
    [.word32, .reference] = none := by decide +kernel
example : scalarTransfer byteSpanRaw (i 40 (.call byteSpanSite))
    [.word32, .reference, .reference] = none := by decide +kernel

private def tupleType : TypeExpr := .aggregate
  (runtime ++ "::System.ValueTuple`2<System.UInt64,System.UInt64>") 0
private def tupleSite : CallSite := {
  declaringType := .atom "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51" "System.Runtime.Intrinsics.X86.X86Base/X64",
  name := "DivRem", target := .external
    "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51::System.ValueTuple`2<System.UInt64,System.UInt64> System.Runtime.Intrinsics.X86.X86Base/X64::DivRem(System.UInt64,System.UInt64,System.UInt64)",
  typeArguments := [], parameterCount := 3, parameterTypes := [word, word, word],
  hasThis := false, returnsValue := true, returnType := tupleType }
private def tupleRaw := { raw [i 2, i 3, i 4, i 40 (.call tupleSite), i 42] [word, word, word] with
  returnType := tupleType, maxStack := 3 }
example : ScalarFlowValid tupleRaw [unknown 0, unknown 1, unknown 2, unknown 3, unknown 1]
    [some [], some [.word64], some [.word64, .word64], some [.word64, .word64, .word64], some [.other]]
    [.arg 0, .arg 1, .arg 2, .intrinsic (.x86Base .divRem64) 3, .ret] := by decide +kernel
example : scalarTransfer tupleRaw (i 40 (.call { tupleSite with parameterTypes := [word, intType, word] }))
    [.word64, .word32, .word64] = none := by decide +kernel

private def tupleFieldRaw := raw [i 2, i 123 (.field tupleType 0 word false), i 42] [.byref tupleType]
example : ScalarFlowValid tupleFieldRaw [unknown 0, unknown 1, unknown 1]
    [some [], some [.reference], some [.word64]] [.arg 0, .fieldAt 0 8, .ret] := by decide +kernel
example : ¬ ScalarFlowValid tupleFieldRaw [unknown 0, unknown 1, unknown 1]
    [some [], some [.reference], some [.other]] [.arg 0, .fieldAt 0 8, .ret] := by decide +kernel

private def spanType : TypeExpr := .apply (.constructor runtime "System.ReadOnlySpan`1") (.atom runtime "System.UInt32")
private def spanSite : CallSite := {
  declaringType := spanType, name := "get_Item", target := .external
    (runtime ++ "::!0& modreq(System.Runtime.InteropServices.InAttribute) System.ReadOnlySpan`1<System.UInt32>::get_Item(System.Int32)"),
  typeArguments := [], parameterCount := 1, parameterTypes := [intType], hasThis := true, returnsValue := true,
  returnType := .atom runtime "!0& modreq(System.Runtime.InteropServices.InAttribute)" }
private def spanRaw := { raw [i 2, i 3, i 40 (.call spanSite), i 113 (.type intType), i 42] [.byref spanType, intType] with returnType := intType }
example : ScalarFlowValid spanRaw [unknown 0, unknown 1, unknown 2, unknown 1, unknown 1]
    [some [], some [.reference], some [.word32, .reference], some [.other], some [.word32]]
    [.arg 0, .arg 1, .memory (.spanItem 4), .loadScalar 4, .ret] := by decide +kernel
example : scalarTransfer spanRaw (i 40 (.call { spanSite with parameterTypes := [word] }))
    [.word64, .reference] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with target := .external "Scope::System.UInt64 Owner::M(garbage(System.Int32)", parameterCount := 1, parameterTypes := [intType] }))
    [.word32] = none := by decide +kernel

example : scalarTransfer addRaw (i 40 (.call { site with
    target := .external "Scope::System.UInt64 Owner::M(Container\u0394)", parameterCount := 1,
    parameterTypes := [.aggregate "Scope::Container\u0394" 0] })) [.other] = some [.word64] := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { site with
    target := .external "Scope::System.UInt64 Owner::M(Container\u0394)", parameterCount := 1,
    parameterTypes := [.aggregate "Scope::Container\u03a9" 0] })) [.other] = none := by decide +kernel

private def joinRaw := { raw [i 2, i 45 (.target 4), i 22, i 43 (.target 5), i 22, i 42] [intType] with returnType := intType }
private def joinFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, state [some 0], unknown 0, unknown 1]
private def joinStates : ScalarCertificate := [some [], some [.word32], some [], some [.word32], some [], some [.word32]]
private def joinCode : List Op := [.arg 0, .brnonzero 4, .const32 0, .branch 5, .const32 0, .ret]
example : ScalarFlowValid joinRaw joinFeatures joinStates joinCode := by decide
example : ¬ ScalarFlowValid { joinRaw with code := joinRaw.code.set 4 (i 33 (.integer 0)) }
    joinFeatures joinStates (joinCode.set 4 (.const64 0)) := by decide
example : ¬ ScalarFlowValid { joinRaw with code := joinRaw.code.set 4 (i 33 (.integer 0)) }
    joinFeatures (joinStates.set 5 (some [.word64])) (joinCode.set 4 (.const64 0)) := by decide

private def loopRaw := raw [i 22, i 38, i 43 (.target 0)] []
private def loopFeatures : FeatureCertificate := [unknown 0, state [some 0], unknown 0]
private def loopStates : ScalarCertificate := [some [], some [.word32], some []]
private def loopCode : List Op := [.const32 0, .pop, .branch 0]
example : ScalarFlowValid loopRaw loopFeatures loopStates loopCode := by decide
example : ¬ ScalarFlowValid loopRaw loopFeatures (loopStates.set 1 (some [.word64])) loopCode := by decide
example : ¬ ScalarFlowValid { loopRaw with code := [i 22, i 0, i 43 (.target 0)] }
    [unknown 0, state [some 0], state [some 0]] [some [], some [.word32], some [.word32]]
    [.const32 0, .nop, .branch 0] := by decide

-- Defaulted signature fields are accepted only where they are the true signature.
private def unsignedSite : CallSite := {
  target := .managed 1, typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true }
example : validateManagedCall [⟨[], addRaw⟩] [] (i 40 (.call unsignedSite)) true (.call 0 2) = false := by decide
example : scalarTransfer addRaw (i 40 (.call unsignedSite)) [.word64, .word64] = none := by decide
example : scalarTransfer addRaw (i 40 (.call { unsignedSite with
    target := .external "Scope::System.UInt64 Owner::M(System.UInt64,System.UInt64)" })) [.word64, .word64] = none := by decide +kernel
example : scalarTransfer addRaw (i 40 (.call { unsignedSite with
    target := .external "Scope::System.Void Owner::M()", parameterCount := 0, returnsValue := false })) [] = some [] := by decide +kernel

-- An uncovered raw opcode with the same stack effect cannot stand in for a scalar computation.
private def holeRaw (opcode : Nat) (operand : RawOperand := .none) := raw [i 2, i 3, i opcode operand, i 38, i 2, i 42]
private def holeFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 1, unknown 0, unknown 1]
private def holeStates : ScalarCertificate :=
  [some [], some [.word64], some [.word64, .word64], some [.other], some [], some [.word64]]
private def holeCode (emitted : Op) : List Op := [.arg 0, .arg 1, emitted, .pop, .arg 0, .ret]
example : ScalarFlowValid (holeRaw 88) holeFeatures (holeStates.set 3 (some [.word64])) (holeCode .add) := by decide
example : ScalarFlowValid (holeRaw 149) holeFeatures holeStates (holeCode (.memory (.spanItem 4))) := by decide
example : ¬ ScalarFlowValid (holeRaw 149) holeFeatures holeStates (holeCode .add) := by decide
example : ¬ ScalarFlowValid (holeRaw 143 (.type intType)) holeFeatures holeStates (holeCode (.divide true false)) := by decide
example : ¬ ScalarFlowValid (holeRaw 149) holeFeatures holeStates (holeCode (.nativeBinary .add)) := by decide
private def holeEvidence (opcode : Nat) (states : ScalarCertificate) : MethodEvidence := {
  original := holeRaw opcode, arguments := [], closed := holeRaw opcode,
  parameterInput := { arguments := [.field .unsigned64, .field .unsigned64], locals := [], code := [.load 0, .load 1, .other, .other, .load 0, .other] },
  reachable := List.replicate 6 true, featureStates := holeFeatures, scalarStates := states, layoutUses := [] }
private def holeMethod (emitted : Op) : Method := { locals := [], returnsValue := true, code := holeCode emitted }
example : TranslationValid [] #[] [holeEvidence 88 (holeStates.set 3 (some [.word64]))] [] [holeMethod .add] := by decide +kernel
example : ¬ TranslationValid [] #[] [holeEvidence 149 holeStates] [] [holeMethod .add] := by decide +kernel

private def unaryHoleRaw (opcode : Nat) := raw [i 2, i opcode, i 38, i 2, i 42] [word]
private def unaryHoleFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 1, unknown 0, unknown 1]
private def unaryHoleStates : ScalarCertificate := [some [], some [.word64], some [.other], some [], some [.word64]]
private def unaryHoleCode (emitted : Op) : List Op := [.arg 0, emitted, .pop, .arg 0, .ret]
example : ScalarFlowValid (unaryHoleRaw 108) unaryHoleFeatures unaryHoleStates (unaryHoleCode (.loadScalar 8)) := by decide
example : ¬ ScalarFlowValid (unaryHoleRaw 108) unaryHoleFeatures unaryHoleStates (unaryHoleCode .convI8) := by decide
example : ¬ ScalarFlowValid (unaryHoleRaw 107) unaryHoleFeatures unaryHoleStates
    (unaryHoleCode (.checkedConvert 64 true false)) := by decide

private def pushHoleRaw (opcode : Nat) := raw [i opcode, i 38, i 2, i 42] [word]
private def pushHoleFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 0, unknown 1]
private def pushHoleStates : ScalarCertificate := [some [], some [.other], some [], some [.word64]]
private def pushHoleCode (emitted : Op) : List Op := [emitted, .pop, .arg 0, .ret]
example : ScalarFlowValid (pushHoleRaw 20) pushHoleFeatures pushHoleStates (pushHoleCode (.memory .nullRef)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 20) pushHoleFeatures pushHoleStates (pushHoleCode (.const64 0)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 35) pushHoleFeatures pushHoleStates (pushHoleCode (.const64 0)) := by decide
example : ¬ ScalarFlowValid (pushHoleRaw 35) pushHoleFeatures pushHoleStates (pushHoleCode (.const32 0)) := by decide

-- Size constants are the only uncovered literal producers; primitive widths are bound here.
private def sizeRaw (instruction : RawInstruction) := raw [instruction, i 38, i 2, i 42] [word]
private def sizeStates : ScalarCertificate := [some [], some [.word32], some [], some [.word64]]
private def sizeCode (bits : W32) : List Op := [.const32 bits, .pop, .arg 0, .ret]
private def sizeAt (instruction : RawInstruction) (bits : W32) : Bool :=
  decide (ScalarFlowValid (sizeRaw instruction) pushHoleFeatures sizeStates (sizeCode bits))
private def sizeOfSite (type : TypeExpr) : CallSite := {
  declaringType := .atom runtime "System.Runtime.CompilerServices.Unsafe", name := "SizeOf",
  target := .external (runtime ++ "::System.Int32 System.Runtime.CompilerServices.Unsafe::SizeOf()"),
  typeArguments := [type], parameterCount := 0, hasThis := false, returnsValue := true,
  returnType := intType, parameterTypes := [] }
private def vector128 : TypeExpr := .apply
  (.constructor "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"
    "System.Runtime.Intrinsics.Vector128`1") word
private def packet : TypeExpr := .aggregate "Fixture::Packet" 0
example : sizeAt (i 65052 (.type intType)) 4 = true := by decide +kernel
example : sizeAt (i 65052 (.type nativeType)) 8 = true := by decide +kernel
example : sizeAt (i 65052 (.type packet)) 24 = true := by decide +kernel
example : sizeAt (i 65052 (.type intType)) 7 = false := by decide +kernel
example : sizeAt (i 65052 (.type (.pointer word))) 8 = false := by decide +kernel
example : sizeAt (i 40 (.call (sizeOfSite intType))) 4 = true := by decide +kernel
example : sizeAt (i 40 (.call (sizeOfSite vector128))) 16 = true := by decide +kernel
example : sizeAt (i 40 (.call (sizeOfSite packet))) 24 = true := by decide +kernel
example : sizeAt (i 40 (.call (sizeOfSite intType))) 5 = false := by decide +kernel
private def otherSite : CallSite := { sizeOfSite intType with
  name := "Other", target := .external (runtime ++ "::System.Int32 System.Runtime.CompilerServices.Unsafe::Other()") }
example : sizeAt (i 40 (.call otherSite)) 4 = false := by decide +kernel
example : sizeAt (i 40 (.call { sizeOfSite intType with declaringType := .atom "Forged" "System.Runtime.CompilerServices.Unsafe" })) 4 = false := by decide +kernel

-- Compare-and-branch: exact encoding, one wrapper exactly for native/int32, and no mixed unsigned form.
private def branchRaw (opcode : Nat) (parameters : List TypeExpr) :=
  { raw [i 2, i 3, i opcode (.target 3), i 42] parameters with returnType := .void }
private def branchFeatures : FeatureCertificate := [unknown 0, unknown 1, unknown 2, unknown 0]
private def branchStates (left right : ScalarKind) : ScalarCertificate := [some [], some [left], some [right, left], some []]
private def branchCode (emitted : Op) : List Op := [.arg 0, .arg 1, emitted, .ret]
private def branchAt (opcode : Nat) (left right : ScalarKind) (emitted : Op) : Bool :=
  let parameters := [left, right].map fun | .native => nativeType | .word32 => intType | .word64 => word | _ => .byref word
  decide (ScalarFlowValid (branchRaw opcode parameters) branchFeatures (branchStates left right) (branchCode emitted))
private def branches : List (Nat × Op) := [
  (46, .beq 3), (47, .bge 3), (48, .bgt 3), (49, .ble 3), (50, .blt 3), (51, .bne 3), (52, .bgeu 3),
  (53, .bgtu 3), (54, .bleu 3), (55, .bltu 3), (59, .beq 3), (60, .bge 3), (61, .bgt 3), (62, .ble 3),
  (63, .blt 3), (64, .bne 3), (65, .bgeu 3), (66, .bgtu 3), (67, .bleu 3), (68, .bltu 3)]
example : branches.all (fun (opcode, emitted) => branchAt opcode .word64 .word64 emitted) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => branchAt opcode .word32 .word32 emitted) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => !branchAt opcode .word64 .word64 (.nativeBinary emitted)) = true := by decide +kernel
example : branches.all (fun (opcode, _) => !branchAt opcode .word64 .word64 (if opcode ∈ [50, 63] then .bge 3 else .blt 3)) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => branchAt opcode .native .word32 (.nativeBinary emitted) ==
    (opcode ∈ [46, 47, 48, 49, 50, 59, 60, 61, 62, 63])) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => branchAt opcode .word32 .native (.nativeBinary emitted) ==
    (opcode ∈ [46, 47, 48, 49, 50, 59, 60, 61, 62, 63])) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => !branchAt opcode .native .word32 emitted) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => !branchAt opcode .native .word64 emitted) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => !branchAt opcode .word32 .word64 emitted) = true := by decide +kernel
example : branches.all (fun (opcode, emitted) => !branchAt opcode .reference .reference emitted) = true := by decide +kernel

example (valid : ScalarFlowValid addRaw addFeatures addStates addCode) :
    scalarEmissionMatches none (i 88) [.word64, .word64] .add = true :=
  valid.instruction_checked (pc := 2) rfl rfl rfl rfl rfl

#print axioms external_call_validated

end Tests.ScalarEvidence
