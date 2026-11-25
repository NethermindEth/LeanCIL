import CIL.Extraction.Translation
import Tests.BodyEncoding

/-!
# Constant-return calls in feature flow

A static, parameterless Boolean method whose own feature certificate shows the same 0 or 1 at
every reachable `ret` decides the branch that tests a call to it. These checks pin which program
methods `evidenceConstants` reads as constant, that computed getters fold through their callees'
certificates, and that the whole-program obligation rejects a certificate claiming a word its
body does not compute.
-/

namespace Tests.ConstantCalls
open CIL CIL.Extraction

private def boolean : TypeExpr := .primitive .boolean
private def integer : TypeExpr := .primitive .int32
private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction :=
  ⟨0, opcode, operand⟩

private def raw (code : List RawInstruction) (returnType : TypeExpr := integer)
    (parameters : List TypeExpr := []) (hasThis := false) : RawMethod := {
  token := 1, owner := "Fixture", hasThis, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType, parameters, locals := [], initLocals := true, maxStack := 8,
  genericParameters := [], code }

/-- A parameterless static Boolean slot, as a call to a flag getter names it. -/
private def slot : CallSite := {
  declared := { convention := 0, returnType := boolean },
  method := {
    owner := .atom "Fixture" "Fixture.IFlag", name := name!"get_IsActive", hasThis := false,
    genericArity := 0, returnType := boolean, parameters := [] },
  name := "get_IsActive", target := .managed 7, typeArguments := [], parameterCount := 0,
  returnsValue := true }

private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

/-- A program method as the whole-program obligation sees it: only its closed body and feature
    certificate matter here. -/
private def method (closed : RawMethod) (featureStates : FeatureCertificate) : MethodEvidence := {
  original := closed, body := Tests.BodyEncoding.noBody, arguments := [], closed,
  parameterInput := ⟨[], [], []⟩, reachable := featureStates.map Option.isSome,
  featureStates, scalarStates := [], layoutUses := [], assembly := ⟨Tests.fixtureAssembly⟩ }

/-- `ldc.i4.0; ret` and `ldc.i4.1; ret` as Boolean getters. -/
private def offBody := raw [i 22, i 42] boolean
private def onBody := raw [i 23, i 42] boolean
private def offStates : FeatureCertificate := [state [], state [some 0]]
private def onStates : FeatureCertificate := [state [], state [some 1]]

/-- `=> On.IsActive && On.IsActive`, as Roslyn compiles it; a false first operand jumps to
    `ldc.i4.0; ret`, which the certificate prunes. -/
private def andBody := raw [i 40 (.call slot), i 44 (.target 4), i 40 (.call slot), i 42,
  i 22, i 42] boolean
private def andStates : FeatureCertificate :=
  [state [], state [some 1], state [], state [some 1], none, none]
private def andCode : List Instruction :=
  [.call slot.method, .brfalse 4, .call slot.method, .ret, .unadmitted 22, .unadmitted 42]

/-- The links of a body whose calls, at `pcs`, enter method `index`. -/
private def linkedAt (index : Nat) (pcs : List Nat) (pc : Nat) : Option Link :=
  if pcs.contains pc then some (.direct index) else none

/-- Bodies that never fold: a static read, an `Int32` constant, a parameterized constant, two
    `ret`s with different words, a `ret`-free body, and a Boolean slot returning 2. -/
private def staticLoad :=
  i 126 (.field (.atom "Fixture" "Fixture.Flags") 0 boolean name!"Enabled" true)
private def staticBody := raw [staticLoad, i 42] boolean
private def ignored : List MethodEvidence := [
  method staticBody [state [], state [none]],
  method (raw [i 22, i 42]) offStates,
  method (raw [i 22, i 42] boolean [integer]) offStates,
  method (raw [staticLoad, i 44 (.target 4), i 22, i 42, i 23, i 42] boolean)
    [state [], state [none], state [], state [some 0], state [], state [some 1]],
  method (raw [i 20, i 122] boolean) [state [], state [none]],
  method (raw [i 24, i 42] boolean) [state [], state [some 2]]]

/-- The program: off, on, the computed conjunction, then every non-folding body. -/
private def program : List MethodEvidence :=
  [method offBody offStates, method onBody onStates, method andBody andStates] ++ ignored

/-- `call IFlag::get_IsActive(); brfalse 4; ldc.i4.7; ret; ldc.i4.1; ret`. -/
private def caller := raw [i 40 (.call slot), i 44 (.target 4), i 29, i 42, i 23, i 42]

/-- The certificate that prunes the block a true flag would run. -/
private def callerOff : FeatureCertificate :=
  [state [], state [some 0], none, none, state [], state [some 1]]

private def callerOffCode : List Instruction :=
  [.call slot.method, .brfalse 4, .unadmitted 29, .unadmitted 42, .ldc_i4 1, .ret]

/-- The certificate that prunes the block a false flag would run. -/
private def callerOn : FeatureCertificate :=
  [state [], state [some 1], state [], state [some 7], none, none]

private def callerOnCode : List Instruction :=
  [.call slot.method, .brfalse 4, .ldc_i4 7, .ret, .unadmitted 23, .unadmitted 42]

/-- The table reads the off, on and computed getters, and nothing else, including any index past
    the program, where a contract import would be. -/
theorem evidenceConstants_exact :
    (List.range 10).map (evidenceConstants program) =
      [some 0, some 1, some 1, none, none, none, none, none, none, none] := by decide

#print axioms evidenceConstants_exact

/-- The conjunction folds through its callee's word, under its own obligation. -/
theorem computed_and_validated :
    FeatureFlowValid #[] (evidenceConstants program) (linkedAt 1 [0, 2]) andBody .scalar
      andStates (andStates.map Option.isSome) andCode := by decide

#print axioms computed_and_validated

/-- Calls to the off, on and computed getters each prune the block their word rules out. -/
theorem constant_calls_prune :
    FeatureFlowValid #[] (evidenceConstants program) (linkedAt 0 [0]) caller .scalar
      callerOff (callerOff.map Option.isSome) callerOffCode ∧
    FeatureFlowValid #[] (evidenceConstants program) (linkedAt 1 [0]) caller .scalar
      callerOn (callerOn.map Option.isSome) callerOnCode ∧
    FeatureFlowValid #[] (evidenceConstants program) (linkedAt 2 [0]) caller .scalar
      callerOn (callerOn.map Option.isSome) callerOnCode := by decide

#print axioms constant_calls_prune

/-- Linking the call to the other getter rejects either pruned certificate. -/
theorem constant_swap_rejected :
    ¬ FeatureFlowValid #[] (evidenceConstants program) (linkedAt 1 [0]) caller .scalar
      callerOff (callerOff.map Option.isSome) callerOffCode ∧
    ¬ FeatureFlowValid #[] (evidenceConstants program) (linkedAt 0 [0]) caller .scalar
      callerOn (callerOn.map Option.isSome) callerOnCode := by decide

#print axioms constant_swap_rejected

/-- No non-folding body or import prunes the guarded block. -/
theorem constant_body_rejected :
    (List.range 7).all (fun index => !decide (FeatureFlowValid #[] (evidenceConstants program)
      (linkedAt (index + 3) [0]) caller .scalar callerOff (callerOff.map Option.isSome)
      callerOffCode)) := by
  decide

#print axioms constant_body_rejected

/-- A program whose only method is `ldc.i4.0; ret` with a certificate claiming it returns 1. -/
private def forged : List MethodEvidence := [method offBody onStates]

/-- The table believes the forged claim and the caller's pruning checks against it, but the
    callee's own obligation, also part of the program's, rejects the claim. -/
theorem forged_constant_rejected :
    evidenceConstants forged 0 = some 1 ∧
    FeatureFlowValid #[] (evidenceConstants forged) (linkedAt 0 [0]) caller .scalar
      callerOn (callerOn.map Option.isSome) callerOnCode ∧
    ¬ FeatureFlowValid #[] (evidenceConstants forged) (fun _ => none) offBody .scalar onStates
      (onStates.map Option.isSome) [.ldc_i4 1, .ret] ∧
    ¬ FeatureFlowValid #[] (evidenceConstants forged) (fun _ => none) offBody .scalar onStates
      (onStates.map Option.isSome) [.ldc_i4 0, .ret] := by decide

#print axioms forged_constant_rejected

/-- Only a parameterless emitted call reads the table, at the callee its link names; a tail call,
    an argument or a pc without a direct link does not. -/
theorem calleeConstant_exact :
    calleeConstant (evidenceConstants program) (some (.direct 0)) (.call slot.method) = some 0 ∧
    calleeConstant (evidenceConstants program) (some (.direct 2)) (.call slot.method) = some 1 ∧
    calleeConstant (evidenceConstants program) (some (.direct 0))
      (.call { slot.method with parameters := [integer] }) = none ∧
    calleeConstant (evidenceConstants program) (some (.direct 0))
      (.call slot.method { tail := true }) = none ∧
    calleeConstant (evidenceConstants program) none (.call slot.method) = none := by decide

#print axioms calleeConstant_exact

/-- With the guarded block live, the unknown answer accepts both successors. -/
theorem constant_unknown_keeps_both :
    FeatureFlowValid #[] (evidenceConstants program) (linkedAt 3 [0]) caller .scalar
      [state [], state [none], state [], state [some 7], state [], state [some 1]]
      (List.replicate 6 true)
      [.call slot.method, .brfalse 4, .ldc_i4 7, .ret, .ldc_i4 1, .ret] := by decide

#print axioms constant_unknown_keeps_both

end Tests.ConstantCalls
