import CIL.Extraction.Features

set_option maxRecDepth 4096

namespace Tests.SpanEvidence
open CIL CIL.Extraction

private def runtime := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def span (scope element : String) : TypeExpr :=
  .apply (.constructor scope "System.ReadOnlySpan`1") (.atom runtime element)
private def words := span runtime "System.UInt32"

private def getItem : RawOperand := .call {
  declaringType := words, name := "get_Item",
  target := .external (runtime ++ "::!0& modreq(System.Runtime.InteropServices.InAttribute) System.ReadOnlySpan`1<System.UInt32>::get_Item(System.Int32)"),
  typeArguments := [], parameterCount := 1, hasThis := true, returnsValue := true }

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (locals : List TypeExpr) (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [words, intType], locals, initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, [none]⟩

-- Only a primitive runtime span names a span local.
example : spanLocal words ∧ spanLocal (span runtime "System.Byte") := by decide
example : ¬ spanLocal (span owner "System.UInt32") ∧ ¬ spanLocal (span runtime "System.Double") ∧
    ¬ spanLocal intType := by decide

-- 0: ldarg.0; 1: stloc.0; 2: ldloca.s 0; 3: ldarg.1; 4: get_Item; 5: ldind.u4; 6: ret
private def itemCode := [i 2, i 10, i 18 (.local 0), i 3, i 40 getItem, i 74, i 42]
private def itemStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none, none], state [none], state [none]]
private def itemOps : List Op :=
  [.arg 0, .nop, .nop, .arg 1, .memory (.spanItem 4), .loadScalar 4, .ret none]

example : foldRoles [words] itemCode = [none, some .head, some .interior, none, none, none, none] := by decide
example : foldRoles [intType] itemCode = List.replicate 7 none := by decide
example : foldRoles [words] [i 10, i 18 (.local 1)] = [none, none] := by decide
-- Only the store may be entered from elsewhere.
example : foldEntry (foldRoles [words] itemCode) 1 ∧ ¬ foldEntry (foldRoles [words] itemCode) 2 := by decide

example : FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true) itemOps := by decide
-- The receiver must stay on the stack: a real store or address is not the fold.
example : ¬ FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true)
    (itemOps.set 1 (.setLocal 0 none)) := by decide
example : ¬ FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true)
    (itemOps.set 2 (.localAddr 0)) := by decide

-- A span local has no storage, so any access outside the fold is rejected; an int local is not.
private def loadCode := [i 2, i 10, i 6, i 42]
private def loadOps : List Op := [.arg 0, .setLocal 0 none, .local 0 none, .ret none]
private def loadStates : FeatureCertificate := [state [], state [none], state [], state [none]]
example : FeatureFlowValid (raw [intType] loadCode) .scalar loadStates (List.replicate 4 true) loadOps := by decide
example : ¬ FeatureFlowValid (raw [words] loadCode) .scalar loadStates (List.replicate 4 true) loadOps := by decide

-- `ldtoken` of a field is static data; only a type handle belongs to a type test.
example : ¬ typeTestInstruction (i 208 (.field (.atom owner "<PrivateImplementationDetails>") 0 intType true)) ∧
    typeTestInstruction (i 208 (.type intType)) := by decide

end Tests.SpanEvidence
