import CIL.Extraction.Features

/-!
# Constant-return calls in feature flow

A static Boolean slot whose resolved body is exactly `ldc.i4.0; ret` or `ldc.i4.1; ret` decides
the branch that tests it. These checks pin which program callees `FeatureFlowValid` accepts as
constant, and that a pruned certificate is rejected whenever the emitted callee does not return
the claimed word.
-/

namespace Tests.ConstantCalls
open CIL CIL.Extraction

private def runtime := runtimeScope
private def boolean : TypeExpr := .atom runtime "System.Boolean"
private def integer : TypeExpr := .atom runtime "System.Int32"
private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction :=
  ⟨0, opcode, operand⟩

private def raw (code : List RawInstruction) (returnType : TypeExpr := integer)
    (parameters : List TypeExpr := []) (hasThis := false) : RawMethod := {
  token := 1, owner := "Fixture", hasThis, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType, parameters, locals := [], initLocals := true, maxStack := 8,
  genericParameters := [], code }

/-- A parameterless static Boolean slot, as a constrained static call names it. -/
private def slot : CallSite := {
  declaringType := .atom "Fixture" "Fixture.IFlag", name := "get_IsActive",
  target := .managed 7, typeArguments := [], parameterCount := 0, hasThis := false,
  returnsValue := true, returnType := boolean }

private def callee (code : List RawInstruction) (returnType : TypeExpr := boolean)
    (parameters : List TypeExpr := []) : SpecializedMethod :=
  ⟨[], raw code returnType parameters⟩

/-- Program methods: the off and on getters, a getter reading a static, an `Int32` constant, and
    a parameterized constant. -/
private def callees : List SpecializedMethod := [
  callee [i 22, i 42], callee [i 23, i 42],
  callee [i 126 (.field (.atom "Fixture" "Fixture.Flags") 0 boolean true), i 42],
  callee [i 22, i 42] integer, callee [i 22, i 42] boolean [integer]]

/-- `constrained. Off; call IFlag::get_IsActive(); brfalse 5; ldc.i4.7; ret; ldc.i4.1; ret`. -/
private def caller := raw [i 65046 (.type (.atom "Fixture" "Fixture.Off")), i 40 (.call slot),
  i 44 (.target 5), i 29, i 42, i 23, i 42]

private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

/-- The certificate that prunes the block a true flag would run. -/
private def offStates : FeatureCertificate :=
  [state [], state [], state [some 0], none, none, state [], state [some 1]]

private def offCode (index : Nat) : List Op := [.nop, .call index 0, .brzero 5,
  .unsupported "pruned", .unsupported "pruned", .const32 1, .ret none]

/-- The certificate that prunes the block a false flag would run. -/
private def onStates : FeatureCertificate :=
  [state [], state [], state [some 1], state [], state [some 7], none, none]

private def onCode (index : Nat) : List Op := [.nop, .call index 0, .brzero 5,
  .const32 7, .ret none, .unsupported "pruned", .unsupported "pruned"]

/-- A call to the `ldc.i4.0; ret` getter prunes the block it guards. -/
theorem constant_off_prunes :
    FeatureFlowValid #[] callees caller .scalar offStates (offStates.map Option.isSome)
      (offCode 0) := by decide

#print axioms constant_off_prunes

/-- A call to the `ldc.i4.1; ret` getter prunes the other block. -/
theorem constant_on_prunes :
    FeatureFlowValid #[] callees caller .scalar onStates (onStates.map Option.isSome)
      (onCode 1) := by decide

#print axioms constant_on_prunes

/-- Swapping the emitted callee to the other getter rejects either pruned certificate. -/
theorem constant_swap_rejected :
    ¬ FeatureFlowValid #[] callees caller .scalar offStates (offStates.map Option.isSome)
      (offCode 1) ∧
    ¬ FeatureFlowValid #[] callees caller .scalar onStates (onStates.map Option.isSome)
      (onCode 0) := by decide

#print axioms constant_swap_rejected

/-- A claimed word the callee does not return is rejected, as is a claim with no method table. -/
theorem constant_forged_rejected :
    ¬ FeatureFlowValid #[] callees caller .scalar (offStates.set 2 (state [some 1]))
      (offStates.map Option.isSome) (offCode 0) ∧
    ¬ FeatureFlowValid #[] [] caller .scalar offStates (offStates.map Option.isSome)
      (offCode 0) := by decide

#print axioms constant_forged_rejected

/-- A static read, an `Int32` return, a parameter or an absent callee is never a constant, so
    each leaves the guarded block live. -/
theorem constant_body_rejected :
    (List.range 4).all (fun index => !decide (FeatureFlowValid #[] callees caller .scalar
      offStates (offStates.map Option.isSome) (offCode (index + 2)))) := by decide

#print axioms constant_body_rejected

/-- Only a parameterless emitted call reads the table; a tail call or argument count does not. -/
theorem calleeConstant_exact :
    calleeConstant callees (.call 0 0) = some 0 ∧ calleeConstant callees (.call 1 0) = some 1 ∧
    calleeConstant callees (.call 0 1) = none ∧ calleeConstant callees (.tailCall 0 0) = none ∧
    (List.range 4).all (fun index => calleeConstant callees (.call (index + 2) 0) == none) := by
  decide

#print axioms calleeConstant_exact

/-- With the guarded block live, the unknown answer accepts both successors. -/
theorem constant_unknown_keeps_both :
    FeatureFlowValid #[] callees caller .scalar
      [state [], state [], state [none], state [], state [some 7], state [], state [some 1]]
      (List.replicate 7 true)
      [.nop, .call 2 0, .brzero 5, .const32 7, .ret none, .const32 1, .ret none] := by decide

#print axioms constant_unknown_keeps_both

end Tests.ConstantCalls
