import CIL.Extraction.Features

set_option maxRecDepth 4096

namespace Tests.ThrowEvidence
open CIL CIL.Extraction

private def runtime := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"

private def ctor (scope type : String) (parameters : Nat) : RawOperand := .call {
  declaringType := .atom scope type, name := ".ctor",
  target := .external (scope ++ "::System.Void " ++ type ++ "::.ctor(" ++
    ",".intercalate (List.replicate parameters "System.String") ++ ")"),
  typeArguments := [], parameterCount := parameters, hasThis := true, returnsValue := false }
private def argument := ctor runtime "System.ArgumentException" 1
private def divide := ctor runtime "System.DivideByZeroException" 0

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [intType], locals := [], initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

-- The exact encoding folds; extra loads, a wrong arity or a non-runtime type do not.
example : foldRoles [] [i 114 (.text "zero"), i 115 argument, i 122] =
    [some .head, some .interior, some (.raise "System.ArgumentException")] := by decide
example : foldRoles [] [i 115 divide, i 122] = [some .head, some (.raise "System.DivideByZeroException")] := by decide
example : foldRoles [] [i 20, i 114 (.text "zero"), i 115 argument, i 122] =
    [none, some .head, some .interior, some (.raise "System.ArgumentException")] := by decide
example : throwFold [i 115 argument, i 122] = none := by decide
example : throwFold [i 115 (ctor owner "Fixture.Failure" 0), i 122] = none := by decide
example : throwFold [i 115 divide, i 38, i 122] = none := by decide

theorem rejects_non_exception : throwFold [i 115 (ctor runtime "System.Object" 0), i 122] = none := by decide
#print axioms rejects_non_exception

theorem rejects_missing_constructor :
    throwFold [i 114 (.text "a"), i 114 (.text "b"), i 115 (ctor runtime "System.DivideByZeroException" 2), i 122] = none := by decide
#print axioms rejects_missing_constructor

private def wrongParameter : RawOperand := .call {
  declaringType := .atom runtime "System.DivideByZeroException", name := ".ctor",
  target := .external (runtime ++ "::System.Void System.DivideByZeroException::.ctor(System.Int32)"),
  typeArguments := [], parameterCount := 1, hasThis := true, returnsValue := false }

theorem rejects_wrong_signature : throwFold [i 114 (.text "a"), i 115 wrongParameter, i 122] = none := by decide
#print axioms rejects_wrong_signature

theorem accepts_two_strings :
    throwFold [i 20, i 114 (.text "message"), i 115 (ctor runtime "System.ArgumentOutOfRangeException" 2), i 122] =
      some (2, "System.ArgumentOutOfRangeException") := by decide
#print axioms accepts_two_strings

theorem rejects_non_exception_certificate :
    ¬ FeatureFlowValid (raw [i 115 (ctor runtime "System.Object" 0), i 122]) .scalar
      [state [], state [none]] [true, true] [.nop, .throw "System.Object"] := by decide
#print axioms rejects_non_exception_certificate

-- 0: ldarg.0; 1: brtrue 5; 2: ldstr; 3: newobj ArgumentException(string); 4: throw; 5: ldarg.0; 6: ret
private def guardRaw := raw [i 2, i 45 (.target 5), i 114 (.text "zero"), i 115 argument, i 122, i 2, i 42]
private def guardStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none], state [], state [none]]
private def guardCode : List Op :=
  [.arg 0, .brnonzero 5, .nop, .nop, .throw "System.ArgumentException", .arg 0, .ret none]

example : FeatureFlowValid guardRaw .scalar guardStates (List.replicate 7 true) guardCode := by decide
-- The raised type is the constructed one, and the fold cannot be emitted as a hole.
example : ¬ FeatureFlowValid guardRaw .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.throw "System.InvalidOperationException")) := by decide
example : ¬ FeatureFlowValid guardRaw .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.unsupported "hidden")) := by decide

-- A branch to the raw `throw` would raise whatever object it carries, so it is rejected.
private def enteredRaw := raw [i 2, i 37, i 45 (.target 6), i 38, i 114 (.text "zero"), i 115 argument, i 122]
example : ¬ FeatureFlowValid enteredRaw .scalar
    [state [], state [none], state [none, none], state [none], state [], state [none], state [none]]
    (List.replicate 7 true) [.arg 0, .dup, .brnonzero 6, .pop, .nop, .nop, .throw "System.ArgumentException"] := by decide

-- A `throw` outside the exact encoding stays unsupported.
example : ¬ FeatureFlowValid (raw [i 20, i 122]) .scalar [state [], state [none]] [true, true]
    [.nop, .throw "System.Object"] := by decide

end Tests.ThrowEvidence
