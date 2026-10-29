import CIL.Extraction.Features

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.TypeTestEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def word : TypeExpr := .atom runtime "System.UInt64"
private def marker : TypeExpr := .aggregate (owner ++ "::Fixture.Marker") 0
private def other : TypeExpr := .aggregate (owner ++ "::Fixture.Other") 1

private def typeCall (name signature : String) (parameters : Nat) : RawOperand := .call {
  declaringType := .atom runtime "System.Type", name,
  target := .external (runtime ++ "::" ++ signature),
  typeArguments := [], parameterCount := parameters, hasThis := false, returnsValue := true,
  returnType := .atom runtime (if name == "GetTypeFromHandle" then "System.Type" else "System.Boolean"),
  parameterTypes := if name == "GetTypeFromHandle" then [.atom runtime "System.RuntimeTypeHandle"]
    else [.atom runtime "System.Type", .atom runtime "System.Type"] }
private def fromHandle := typeCall "GetTypeFromHandle" "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)" 1
private def equality := typeCall "op_Equality" "System.Boolean System.Type::op_Equality(System.Type,System.Type)" 2
private def inequality := typeCall "op_Inequality" "System.Boolean System.Type::op_Inequality(System.Type,System.Type)" 2

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def test (left right : TypeExpr) (comparison := equality) : List RawInstruction :=
  [i 208 (.type left), i 40 fromHandle, i 208 (.type right), i 40 fromHandle, i 40 comparison]
private def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [], locals := [], initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

-- Identity follows full names; one name in two scopes is undecided.
example : sameRuntimeType marker marker = some true := by decide
example : sameRuntimeType marker other = some false := by decide
example : sameRuntimeType marker word = some false := by decide
example : sameRuntimeType (.atom "Forwarder" "System.UInt64") word = none := by decide
example : sameRuntimeType (.atom runtime "System.UInt64 modreq(X)") word = none := by decide
example : sameRuntimeType (.atom runtime "System.UInt64[]") (.atom runtime "System.Int64[]") = none := by decide
example : sameRuntimeType (.pointer word) word = some false := by decide
example : sameRuntimeType (.apply (.constructor runtime "System.Nullable`1") word)
    (.apply (.constructor runtime "System.Nullable`1") intType) = some false := by decide
example : sameRuntimeType (.parameter 0) word = none := by decide
example : sameRuntimeType .void .void = none := by decide
example : sameRuntimeType (.aggregate "Fixture::Bad::Name" 0) (.aggregate "Fixture::Bad::Other" 0) = none := by decide

example : foldRoles [] (test marker marker) =
    [some .head, some .interior, some .interior, some .interior, some (.result true)] := by decide
example : foldRoles [] (test marker other inequality) =
    [some .head, some .interior, some .interior, some .interior, some (.result true)] := by decide
example : foldRoles [] (test (.atom "Forwarder" "System.UInt64") word) = List.replicate 5 none := by decide
-- Any instruction between the operands breaks the exact encoding.
example : foldRoles [] ((test marker marker).insertIdx 2 (i 0)) = List.replicate 6 none := by decide

-- 0: typeof(Marker) == typeof(Marker); 5: brfalse 8; 6: ldc.i4.1; 7: ret; 8: ldc.i4.0; 9: ret
private def foldRaw := raw (test marker marker ++ [i 44 (.target 8), i 23, i 42, i 22, i 42])
private def foldStates : FeatureCertificate := [state [], state [none], state [none],
  state [none, none], state [none, none], state [some 1], state [], state [some 1], none, none]
private def foldMask := [true, true, true, true, true, true, true, true, false, false]
private def foldCode : List Op := [.nop, .nop, .nop, .nop, .const32 1, .brzero 8, .const32 1, .ret none,
  .unsupported "pruned", .unsupported "pruned"]

example : FeatureFlowValid #[] foldRaw .scalar foldStates foldMask foldCode := by decide
-- A forged constant fails even with matching facts, and forged facts cannot prune the live branch.
example : ¬ FeatureFlowValid #[] foldRaw .scalar foldStates foldMask (foldCode.set 4 (.const32 0)) := by decide
example : ¬ FeatureFlowValid #[] foldRaw .scalar (foldStates.set 5 (state [some 0])) foldMask foldCode := by decide
example : ¬ FeatureFlowValid #[] foldRaw .scalar foldStates foldMask (foldCode.set 2 (.const32 0)) := by decide
-- Distinct types decide the opposite edge.
private def distinctRaw := raw (test marker other ++ [i 44 (.target 8), i 23, i 42, i 22, i 42])
example : ¬ FeatureFlowValid #[] distinctRaw .scalar foldStates foldMask foldCode := by decide
example : FeatureFlowValid #[] distinctRaw .scalar
    ((foldStates.set 5 (state [some 0])).set 6 none |>.set 7 none |>.set 8 (state []) |>.set 9 (state [some 0]))
    [true, true, true, true, true, true, false, false, true, true]
    [.nop, .nop, .nop, .nop, .const32 0, .brzero 8, .unsupported "pruned", .unsupported "pruned", .const32 0, .ret none] := by decide

-- A branch into the operands would reach the comparison with a different emitted stack.
private def enteredRaw := raw ([i 22, i 43 (.target 4)] ++ test marker marker ++ [i 42])
example : ¬ FeatureFlowValid #[] enteredRaw .scalar
    [state [], state [some 0], none, none, state [some 0], state [none, some 0], state [none, some 0], state [some 1]]
    [true, true, false, false, true, true, true, true]
    [.const32 0, .branch 4, .unsupported "", .unsupported "", .nop, .nop, .const32 1, .ret none] := by decide
-- The same facts are accepted once the edge enters at the first operand.
example : FeatureFlowValid #[] (raw ([i 22, i 43 (.target 2)] ++ test marker marker ++ [i 42])) .scalar
    [state [], state [some 0], state [some 0], state [none, some 0], state [none, some 0], state [none, none, some 0], state [none, none, some 0], state [some 1, some 0]]
    [true, true, true, true, true, true, true, true]
    [.const32 0, .branch 2, .nop, .nop, .nop, .nop, .const32 1, .ret none] := by decide

-- Undecided comparisons and stray type handles have no admitted translation.
private def undecidedRaw := raw (test (.atom "Forwarder" "System.UInt64") word ++ [i 42])
example : ¬ FeatureFlowValid #[] undecidedRaw .scalar
    [state [], state [none], state [none], state [none, none], state [none, none], state [none]]
    (List.replicate 6 true) [.nop, .nop, .nop, .nop, .const32 0, .ret none] := by decide
example : featureOpMatchesAt #[] foldRaw none (i 208 (.type marker)) (.const32 0) = false := by decide
example : featureOpMatchesAt #[] foldRaw none (i 40 equality) (.eq) = false := by decide
example : featureOpMatchesAt #[] foldRaw none (i 40 fromHandle) (.convU4) = false := by decide

end Tests.TypeTestEvidence
