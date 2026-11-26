import CIL.Safety.Execution
import CIL.Extraction.Scalars
import CIL.Extraction.DecodedMethod
import Tests.Support.RawDecoding

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.TypeTestEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .primitive .int32
private def word : TypeExpr := .primitive .uint64
private def marker : TypeExpr := .aggregate (owner ++ "::Fixture.Marker") 0
private def other : TypeExpr := .aggregate (owner ++ "::Fixture.Other") 1

private def typeCall (name : String) (methodName : MetadataName) (signature : String)
    (parameters : Nat) : RawOperand := .call {
  declared := {
    convention := 0, returnType := if name == "GetTypeFromHandle" then .atom runtime "System.Type"
        .classType
      else .primitive .boolean,
    parameters := if name == "GetTypeFromHandle" then [.atom runtime "System.RuntimeTypeHandle"
        .valueType]
      else [.atom runtime "System.Type" .classType, .atom runtime "System.Type" .classType] },
  method := {
    owner := .atom runtime "System.Type" .classType, name := methodName, hasThis := false,
    genericArity := 0,
    returnType := if name == "GetTypeFromHandle" then .atom runtime "System.Type" .classType
      else .primitive .boolean,
    parameters := if name == "GetTypeFromHandle" then [.atom runtime "System.RuntimeTypeHandle"
        .valueType]
      else [.atom runtime "System.Type" .classType, .atom runtime "System.Type" .classType] },
  name, target := .external (runtime ++ "::" ++ signature),
  typeArguments := [], parameterCount := parameters, returnsValue := true }
private def fromHandle := typeCall "GetTypeFromHandle" name!"GetTypeFromHandle"
  "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)" 1
private def equality := typeCall "op_Equality" name!"op_Equality"
  "System.Boolean System.Type::op_Equality(System.Type,System.Type)" 2
private def inequality := typeCall "op_Inequality" name!"op_Inequality"
  "System.Boolean System.Type::op_Inequality(System.Type,System.Type)" 2

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
example : sameRuntimeType (.atom "Forwarder" "System.UInt64" .valueType) word = none := by decide
example : sameRuntimeType (.spelledModified runtime "System.UInt64 modreq(X)") word = none := by
  decide
example : sameRuntimeType (.atom runtime "System.UInt64[]" .classType) (.atom runtime
    "System.Int64[]" .classType) = none := by decide
example : sameRuntimeType (.pointer word) word = some false := by decide
example : sameRuntimeType (.apply (.constructor runtime "System.Nullable`1") word)
    (.apply (.constructor runtime "System.Nullable`1") intType) = some false := by decide
example : sameRuntimeType (.parameter 0) word = none := by decide
example : sameRuntimeType .void .void = none := by decide
example : sameRuntimeType (.aggregate "Fixture::Bad::Name" 0) (.aggregate "Fixture::Bad::Other" 0) = none := by decide

example : foldRoles (test marker marker) =
    [some .typeHead, some .typeOperand, some .typeOperand, some .typeOperand, some (.result true)] := by decide
example : foldRoles (test marker other inequality) =
    [some .typeHead, some .typeOperand, some .typeOperand, some .typeOperand, some (.result true)] := by decide
example : foldRoles (test (.atom "Forwarder" "System.UInt64" .valueType)
    word) = List.replicate 5 none := by
  decide
-- Any instruction between the operands breaks the exact encoding.
example : foldRoles ((test marker marker).insertIdx 2 (i 0)) = List.replicate 6 none := by decide

-- 0: typeof(Marker) == typeof(Marker); 5: brfalse 8; 6: ldc.i4.1; 7: ret; 8: ldc.i4.0; 9: ret
private def foldRaw := raw (test marker marker ++ [i 44 (.target 8), i 23, i 42, i 22, i 42])
private def foldStates : FeatureCertificate := [state [], state [none], state [none],
  state [none, none], state [none, none], state [some 1], state [], state [some 1], none, none]
private def foldMask := [true, true, true, true, true, true, true, true, false, false]
private def typeOperands (left right : TypeExpr) : List Instruction :=
  [.ldtoken (.type left), .call getTypeFromHandle.method, .ldtoken (.type right),
   .call getTypeFromHandle.method]

private def equalCall : Instruction := .call (runtimeTypeComparison true).method

private def foldCode : List Instruction :=
  typeOperands marker marker ++ [equalCall, .brfalse 8, .ldc_i4 1, .ret, .unadmitted 22,
   .unadmitted 42]

example : FeatureFlowValid #[] (fun _ => none) (fun _ => none)
    foldRaw .scalar foldStates foldMask foldCode := by decide
-- A forged constant fails even with matching facts, and forged facts cannot prune the live branch.
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) foldRaw .scalar foldStates
    foldMask
    (foldCode.set 4 (.ldc_i4 0)) := by decide
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) foldRaw .scalar
    (foldStates.set 5 (state [some 0])) foldMask foldCode := by decide
-- The code equation fixes the type operands, refusing a forged constant among them.
example : foldCode = methodCode .scalar {} [] foldMask foldRaw ∧
    foldCode.set 2 (.ldc_i4 0) ≠ methodCode .scalar {} [] foldMask foldRaw := by decide +kernel
-- Distinct types decide the opposite edge.
private def distinctRaw := raw (test marker other ++ [i 44 (.target 8), i 23, i 42, i 22, i 42])
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none)
    distinctRaw .scalar foldStates foldMask foldCode := by decide
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) distinctRaw .scalar
    ((foldStates.set 5 (state [some 0])).set 6 none |>.set 7 none |>.set 8 (state []) |>.set 9 (state [some 0]))
    [true, true, true, true, true, true, false, false, true, true]
    (typeOperands marker other ++ [equalCall, .brfalse 8, .unadmitted 23, .unadmitted 42,
      .ldc_i4 0, .ret]) := by decide

-- A branch into the operands would reach the comparison with a different emitted stack.
private def enteredRaw := raw ([i 22, i 43 (.target 4)] ++ test marker marker ++ [i 42])
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) enteredRaw .scalar
    [state [], state [some 0], none, none, state [some 0], state [none, some 0], state [none, some 0], state [some 1]]
    [true, true, false, false, true, true, true, true]
    [.ldc_i4 0, .br 4, .unadmitted 208, .unadmitted 40, .ldtoken (.type marker),
      .call getTypeFromHandle.method, equalCall, .ret] := by decide
-- The same facts are accepted once the edge enters at the first operand.
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none)
    (raw ([i 22, i 43 (.target 2)] ++ test marker marker ++ [i 42])) .scalar
    [state [], state [some 0], state [some 0], state [none, some 0], state [none, some 0], state [none, none, some 0], state [none, none, some 0], state [some 1, some 0]]
    [true, true, true, true, true, true, true, true]
    ([.ldc_i4 0, .br 2] ++ typeOperands marker marker ++ [equalCall, .ret]) := by decide

-- Undecided type comparisons cannot certify an emitted constant.
private def undecidedRaw := raw (test (.atom "Forwarder" "System.UInt64" .valueType) word ++ [i
    42])
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) undecidedRaw .scalar
    [state [], state [none], state [none], state [none, none], state [none, none], state [none]]
    (List.replicate 6 true) [.nop, .nop, .nop, .nop, .ldc_i4 0, .ret] := by decide
example : featureOpMatchesAt #[] foldRaw none (i 208 (.type marker)) (.ldc_i4 0) = false := by decide
example : featureOpMatchesAt #[] foldRaw none (i 40 equality) (.ceq) = false := by decide
example : featureOpMatchesAt #[] foldRaw none (i 40 fromHandle) (.conv_u4) = false := by decide

/-- The exact reference-equality branch form, with two distinct return paths. -/
private def branchRaw (same : Bool) (opcode : Nat) (target := 7) :=
  raw ((test word (if same then word else intType)).take 4 ++
    [i opcode (.target target), i 23, i 42, i 22, i 42])

/-- Raw typeof values occupy two slots before the decided branch consumes them. -/
private def branchStates (taken : Bool) : FeatureCertificate :=
  [state [], state [none], state [none], state [none, none], state [none, none],
    if taken then none else state [], if taken then none else state [some 1],
    if taken then state [] else none, if taken then state [some 0] else none]

/-- The scalar certificate tracks the two type operands consumed by the branch. -/
private def branchKinds (taken : Bool) : ScalarCertificate :=
  [some [], some [.other], some [.other], some [.other, .other], some [.other, .other],
    if taken then none else some [], if taken then none else some [.word32],
    if taken then some [] else none, if taken then some [.word32] else none]

/-- The executed type branch retains both handle loads, both calls and its original target. -/
private def branchCode (same : Bool) (opcode : Nat) : List Instruction :=
  let equal := opcode == 46 || opcode == 59
  let taken := same == equal
  typeOperands word (if same then word else intType) ++ [if equal then .beq 7 else .bne_un 7,
    if taken then .unadmitted 23 else .ldc_i4 1,
    if taken then .unadmitted 42 else .ret,
    if taken then .ldc_i4 0 else .unadmitted 22,
    if taken then .ret else .unadmitted 42]

/-- Short and long equality/inequality branches certify both type-identity outcomes. -/
theorem reference_type_branches :
    ([46, 51, 59, 64].all fun opcode => [true, false].all fun same =>
      let taken := same == (opcode == 46 || opcode == 59)
      let body := branchRaw same opcode
      let states := branchStates taken
      decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none) body .scalar states
        (states.map Option.isSome)
        (branchCode same opcode)) &&
      decide (ScalarFlowValid body states (branchKinds taken) (branchCode same opcode))) = true := by
  decide +kernel
#print axioms reference_type_branches

/-- The code equation refuses a changed branch operation, and the fold and entry checks refuse a
    forged edge. -/
theorem reference_type_branch_rejections :
    let states := branchStates true
    let mask := states.map Option.isSome
    let code := branchCode true 46
    let forwarded := raw ((branchRaw true 46).code.set 2
      (i 208 (.type (.atom "Forwarder" "System.UInt64" .valueType))))
    code = methodCode .scalar {} [] mask (branchRaw true 46) ∧
    code.set 4 (.beq 5) ≠ methodCode .scalar {} [] mask (branchRaw true 46) ∧
    (¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (branchRaw true 47) .scalar states
      mask code) ∧
    (¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (branchRaw true 46) .scalar
      (branchStates false) ((branchStates false).map Option.isSome) (branchCode false 46)) ∧
    ([1, 4, 9].all fun target =>
      let untouched := branchStates false
      !decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none) (branchRaw false 46 target)
        .scalar untouched
        (untouched.map Option.isSome) (branchCode false 46))) = true ∧
    (¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) forwarded .scalar states mask code) :=
      by
  decide +kernel
#print axioms reference_type_branch_rejections

/-- Operandless `ceq` returns the closed type identity as a word, with the raw two-value stack;
    the code equation refuses the opposite word there. -/
theorem reference_type_results :
    ([true, false].all fun same =>
      let body := raw ((test word (if same then word else intType)).take 4 ++ [i 65025, i 42])
      let result := if same then 1 else 0
      let states := (branchStates false).take 5 ++ [state [some result]]
      let kinds := (branchKinds false).take 5 ++ [some [.word32]]
      let code := typeOperands word (if same then word else intType) ++ [.ceq, .ret]
      decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none)
          body .scalar states (List.replicate 6 true) code) &&
      decide (ScalarFlowValid body states kinds code) &&
      !decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none)
        { body with code := body.code.set 4 (i 65026) }
        .scalar states (List.replicate 6 true) code) &&
      !decide (FeatureFlowValid #[] (fun _ => none) (fun _ => none)
          { body with code := body.code.set 4 (i 65025 (.target 5)) }
        .scalar states (List.replicate 6 true) code) &&
      decide (code = methodCode .scalar {} [] (List.replicate 6 true) body) &&
      decide (code.set 4 (.ldc_i4 (if same then 0 else 1)) ≠
        methodCode .scalar {} [] (List.replicate 6 true) body)) = true := by
  decide +kernel
#print axioms reference_type_results

private def dog : TypeExpr := .object owner "Fixture.Dog"
private def bird : TypeExpr := .object owner "Fixture.Bird"

/-- `castclass` and `isinst` of a class match their own raw opcode and class on an object or
    null. -/
theorem class_tests_match :
    scalarEmissionMatches none none (i 116 (.type dog)) [.object] (.castclass dog) = true ∧
    scalarEmissionMatches none none (i 117 (.type dog)) [.nullObject]
      (.isinst dog) = true := by
  decide
#print axioms class_tests_match

/-- A raw `isinst` emitted as `castclass` is rejected by the scalar check and the decoder: the
    two differ on a failed test. -/
theorem isinst_decoded_as_castclass :
    scalarEmissionMatches none none (i 117 (.type dog)) [.object] (.castclass dog) = false ∧
    valueEncodingMatches none (i 117 (.type dog)) (.castclass dog) = false := by
  decide
#print axioms isinst_decoded_as_castclass

/-- A cast emitted against another class than its raw operand is rejected by the scalar check
    and the decoder. -/
theorem cast_other_type :
    scalarEmissionMatches none none (i 116 (.type dog)) [.object] (.castclass bird) = false ∧
    valueEncodingMatches none (i 116 (.type dog)) (.castclass bird) = false := by
  decide
#print axioms cast_other_type

/-- The feature check ties each type test to its own raw opcode: a raw `castclass` emitted as
    `isinst` and a raw `isinst` emitted as `castclass` are rejected. -/
theorem type_test_feature_opcodes :
    featureOpMatches #[] (raw []) (i 116 (.type dog)) (.castclass dog) = true ∧
    featureOpMatches #[] (raw []) (i 117 (.type dog)) (.isinst dog) = true ∧
    featureOpMatches #[] (raw []) (i 116 (.type dog)) (.isinst dog) = false ∧
    featureOpMatches #[] (raw []) (i 117 (.type dog)) (.castclass dog) = false := by
  decide +kernel
#print axioms type_test_feature_opcodes

/-- Both equality calls retain their method operand and both closed type tokens. -/
theorem decodedTypeEquality :
    ((Method.ofRaw? .scalar {} [] (List.replicate 5 true)
        (raw (test word word)) []).map Method.code) =
      some (typeOperands word word ++ [equalCall]) ∧
    ((Method.ofRaw? .scalar {} [] (List.replicate 5 true)
        (raw (test word intType)) []).map Method.code) =
      some (typeOperands word intType ++ [equalCall]) := ⟨rfl, rfl⟩

#print axioms decodedTypeEquality

/-- The call operand with one field of its site changed. -/
private def changeSite (operand : RawOperand) (change : CallSite → CallSite) : RawOperand :=
  match operand with
  | .call site => .call (change site)
  | other => other

/-- A same-named GetTypeFromHandle or op_Equality outside the runtime's System.Type folds no
    type test, so the live ldtoken at pc 0 refuses the method. -/
theorem foreign_type_members :
    let foreignOwner := changeSite fromHandle fun site =>
      { site with method.owner := .atom "Fixture" "System.Type" .classType }
    let signature := "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)"
    let foreignTarget := changeSite fromHandle fun site =>
      { site with target := .external ("Fixture::" ++ signature) }
    let forwarded := changeSite equality fun site =>
      { site with method.owner := .atom "Forwarder" "System.Type" .classType }
    let control := test marker marker
    [control.set 1 (i 40 foreignOwner), control.set 1 (i 40 foreignTarget),
      control.set 4 (i 40 forwarded)].all (fun code =>
        decide (foldRoles code = List.replicate 5 none) &&
          decide ((decodeRaw .scalar {} [] (List.replicate 5 true) (raw code) []).map
            Method.code = liveHoleAt 0 208)) = true := by
  decide +kernel

#print axioms foreign_type_members

/-- Same-named types in different possible forwarding scopes leave both the operator and
    the reference branch inconclusive. Neither operation reports an unequal result. -/
theorem unresolved_runtime_identity (body : Method) (frame : Safety.Frame) (memory : Safety.Memory) :
    let stack : List Safety.Value := [.runtimeType word,
        .runtimeType (.atom "Forwarder" "System.UInt64" .valueType)]
    let failure : Safety.ExecutionResult Safety.FrameAction :=
      .error (.unsupported "Type comparison needs a resolved type identity")
    Safety.runModel body (.typeEquality true) 0 frame stack memory = failure ∧
    Safety.step body (.bne_un 7) 0 [] frame stack memory = failure := ⟨rfl, rfl⟩

#print axioms unresolved_runtime_identity

end Tests.TypeTestEvidence
