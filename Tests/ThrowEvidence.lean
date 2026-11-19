import CIL.Extraction.DecodedMethod
import CIL.Extraction.Features

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.ThrowEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"

private def ctor (scope type : String) (parameters : Nat) : RawOperand := .call {
  declared := {
    convention := 0x20,
    parameters := List.replicate parameters (.object runtime "System.String") },
  method := {
    owner := .atom scope type, name := name!".ctor", hasThis := true, genericArity := 0,
    returnType := .void,
    parameters := List.replicate parameters (.object runtime "System.String") },
  name := ".ctor",
  target := .external (scope ++ "::System.Void " ++ type ++ "::.ctor(" ++
    ",".intercalate (List.replicate parameters "System.String") ++ ")"), typeArguments := [],
  parameterCount := parameters, returnsValue := false }
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
    [some .head, some .interior, some (.raise .argument)] := by decide
example : foldRoles [] [i 115 divide, i 122] = [some .head, some (.raise .divideByZero)] := by
  decide
example : foldRoles [] [i 20, i 114 (.text "zero"), i 115 argument, i 122] =
    [none, some .head, some .interior, some (.raise .argument)] := by decide
example : throwFold [i 115 argument, i 122] = none := by decide
example : throwFold [i 115 (ctor owner "Fixture.Failure" 0), i 122] = none := by decide
example : throwFold [i 115 divide, i 38, i 122] = none := by decide

/-- A throw message has the operand of a string or null load. -/
theorem message_operands :
    throwFold [i 114, i 115 argument, i 122] = none ∧
    throwFold [i 20 (.text "forged"), i 115 argument, i 122] = none := by decide
#print axioms message_operands

/-- An ordinary string load retains its text, while a throw consumes its own message. -/
theorem string_and_throw :
    let closed := raw [i 114 (.text "keep"), i 38, i 114 (.text "message"), i 115 argument, i 122]
    methodCode .scalar {} [] (List.replicate 5 true) closed =
      [.memory (.stringLiteral "keep"), .pop, .nop, .nop, .throw .argument] := rfl
#print axioms string_and_throw

/-- Rejecting an oversized message prefix still discovers an admitted fold in its suffix. -/
theorem long_prefix_suffix :
    foldRoles [] ([i 20, i 20, i 20] ++
      [i 115 (ctor runtime "System.ArgumentException" 2), i 122]) =
      [none, some .head, some .interior, some .interior,
        some (.raise .argument)] := by decide +kernel
#print axioms long_prefix_suffix

/-- A long message-only body never invents a constructor or throw. -/
theorem message_only_body : foldRoles [] (List.replicate 128 (i 20)) =
    List.replicate 128 none := by decide +kernel
#print axioms message_only_body

theorem rejects_non_exception : throwFold [i 115 (ctor runtime "System.Object" 0), i 122] = none := by decide
#print axioms rejects_non_exception

theorem rejects_missing_constructor :
    throwFold [i 114 (.text "a"), i 114 (.text "b"), i 115 (ctor runtime "System.DivideByZeroException" 2), i 122] = none := by decide
#print axioms rejects_missing_constructor

private def wrongParameter : RawOperand := .call {
  declared := { convention := 0x20, parameters := [intType] },
  method := {
    owner := .atom runtime "System.DivideByZeroException", name := name!".ctor", hasThis := true,
    genericArity := 0, returnType := .void, parameters := [] },
  name := ".ctor",
  target := .external (runtime ++ "::System.Void System.DivideByZeroException::.ctor(\
    System.Int32)"),
  typeArguments := [], parameterCount := 1, returnsValue := false }

theorem rejects_wrong_signature : throwFold [i 114 (.text "a"), i 115 wrongParameter, i 122] = none := by decide
#print axioms rejects_wrong_signature

theorem accepts_two_strings :
    throwFold [i 20, i 114 (.text "message"), i 115 (ctor runtime "System.ArgumentOutOfRangeException" 2), i 122] =
      some (2, .argumentOutOfRange) := by decide
#print axioms accepts_two_strings

theorem rejects_non_exception_certificate :
    ∀ claimed ∈ ExceptionType.all, ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none)
        (raw [i 115 (ctor runtime "System.Object" 0), i 122]) .scalar
      [state [], state [none]] [true, true] [.nop, .throw claimed] := by decide +kernel
#print axioms rejects_non_exception_certificate

-- 0: ldarg.0; 1: brtrue 5; 2: ldstr; 3: newobj ArgumentException(string); 4: throw; 5: ldarg.0; 6: ret
private def guardRaw := raw [i 2, i 45 (.target 5), i 114 (.text "zero"), i 115 argument, i 122, i 2, i 42]
private def guardStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none], state [], state [none]]
private def guardCode : List Instruction :=
  [.ldarg 0, .brtrue 5, .nop, .nop, .throw .argument, .ldarg 0, .ret]

example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) guardRaw .scalar guardStates
    (List.replicate 7 true) guardCode := by decide
-- The raised type is the constructed one, and the fold cannot be emitted as a hole.
example : ∀ other ∈ ExceptionType.all, other ≠ .argument → ¬ FeatureFlowValid #[] (fun _ => none)
    (fun _ => none)
    guardRaw .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.throw other)) := by decide +kernel
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none)
    guardRaw .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.unadmitted 122)) := by decide

-- A branch to the raw `throw` would raise whatever object it carries, so it is rejected.
private def enteredRaw := raw [i 2, i 37, i 45 (.target 6), i 38, i 114 (.text "zero"), i 115 argument, i 122]
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) enteredRaw .scalar
    [state [], state [none], state [none, none], state [none], state [], state [none], state [none]]
    (List.replicate 7 true) [.ldarg 0, .dup, .brtrue 6, .pop, .nop, .nop,
        .throw .argument] := by decide

/-- An adjacent raw null is the only operand admitted by the null-throw fold. -/
theorem null_throw_encoding :
    foldRoles [] [i 20, i 122] =
      [some .head, some (.raise .nullReference)] ∧
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20, i 122]) .scalar
      [state [], state [none]] [true, true] [.nop, .throw .nullReference] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 22, i 122]) .scalar
      [state [], state [some 0]] [true, true] [.nop, .throw .nullReference] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20 (.text "forged"), i 122])
      .scalar
      [state [], state [none]] [true, true] [.nop, .throw .nullReference] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20, i 0, i 122]) .scalar
      [state [], state [none], state [none]] [true, true, true]
      [.nop, .nop, .throw .nullReference] := by decide +kernel
#print axioms null_throw_encoding

/-- A branch may enter at the null load, but not skip it to reach the folded throw. -/
theorem null_throw_entry :
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw
      [i 20, i 43 (.target 2), i 20, i 122]) .scalar
      [state [], state [none], state [none], state [none, none]]
      [true, true, true, true]
      [.memory .nullRef, .br 2, .nop, .throw .nullReference] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw
      [i 20, i 43 (.target 3), i 20, i 122]) .scalar
      [state [], state [none], none, state [none]] [true, true, false, true]
      [.memory .nullRef, .br 3, .unadmitted 20, .throw .nullReference] :=
  by decide +kernel
#print axioms null_throw_entry

/-- A direct edge or switch arm into the throw disables just the entered fold. -/
theorem decoded_throw_entry :
    let source := fun edge => raw
      [i 2, i 45 (.target 4), i 20, edge, i 115 divide, i 122, i 115 divide, i 122]
    let mask := List.replicate 8 true
    let decode := fun edge => (Method.ofRaw? .scalar {} [] mask (source edge) []).map
      fun body => (body.code[5]?, body.code[7]?)
    let refused := fun edge =>
      let code := methodCode .scalar {} [] mask (source edge)
      decode edge = none ∧ code[5]? = some (.unadmitted 122) ∧
        code[7]? = some (.throw .divideByZero)
    let raised := some (Instruction.throw .divideByZero)
    decode (i 43 (.target 4)) = some (raised, raised) ∧
      refused (i 43 (.target 5)) ∧ refused (i 69 (.targets [4, 5])) := by decide +kernel

#print axioms decoded_throw_entry

-- A null throw cannot claim another exception type.
example : ∀ other ∈ ExceptionType.all, other ≠ .nullReference → ¬ FeatureFlowValid #[]
    (fun _ => none) (fun _ => none) (raw [i 20, i 122]) .scalar [state [], state [none]] [true,
      true]
    [.nop, .throw other] := by decide +kernel

/-- Types outside the constructor allowlist cannot form a throw fold. -/
theorem rejects_unadmitted_owners :
    foldRoles [] [i 115 (ctor runtime "System.PlatformNotSupportedException" 0), i 122] =
      [none, none] ∧
    foldRoles [] [i 115 (ctor runtime "System.InvalidCastException" 0), i 122] = [none, none] ∧
    exceptionOwner? (.atom runtimeScope "System.Object") = none := by decide +kernel
#print axioms rejects_unadmitted_owners

end Tests.ThrowEvidence
