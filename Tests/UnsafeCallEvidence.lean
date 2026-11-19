import CIL.Extraction.DecodedMethod

/-! Exact runtime operands, modelled SkipInit calls and lowered null-reference operations. -/

open CIL CIL.Extraction

namespace Tests.UnsafeCallEvidence

private def scope :=
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def unsafeType : TypeExpr := .atom scope "System.Runtime.CompilerServices.Unsafe"
private def word : TypeExpr := .atom scope "System.UInt64"
private def call : CallSite := {
  declared := { convention := 0x10, parameters := [.byref (.parameter 0)] },
  method := {
    owner := unsafeType, name := name!"SkipInit", hasThis := false, genericArity := 1,
    returnType := .void, parameters := [.byref word], methodArguments := [word] },
  name := "SkipInit",
  target := .external (scope ++ "::System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(\
    !!0&)"),
  typeArguments := [word], parameterCount := 1, returnsValue := false }
private def nullCall : CallSite := {
  declared := { convention := 0x10, returnType := .byref (.parameter 0) },
  method := {
    owner := unsafeType, name := name!"NullRef", hasThis := false, genericArity := 1,
    returnType := .byref word, parameters := [], methodArguments := [word] },
  name := "NullRef",
  target := .external (scope ++ "::!!0& System.Runtime.CompilerServices.Unsafe::NullRef()"),
  typeArguments := [word], parameterCount := 0, returnsValue := true }
private def testCall : CallSite := {
  declared := {
    convention := 0x10, returnType := .atom runtimeScope "System.Boolean",
    parameters := [.byref (.parameter 0)] },
  method := {
    owner := unsafeType, name := name!"IsNullRef", hasThis := false, genericArity := 1,
    returnType := .atom scope "System.Boolean", parameters := [.byref word],
    methodArguments := [word] },
  name := "IsNullRef",
  target := .external (scope ++ "::System.Boolean System.Runtime.CompilerServices.Unsafe::\
    IsNullRef(!!0&)"),
  typeArguments := [word], parameterCount := 1, returnsValue := true }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 1, genericParameters := [], code := [⟨0, 0x28, .call site⟩] }
private def nonCall : RawMethod := { raw call with code := [⟨0, 0x26, .none⟩] }

/-- Changing a redundant call field or the typed reference cannot retain the SkipInit call. -/
theorem skipInitOperand :
    let decode := fun operand =>
      (Method.ofRaw? .scalar {} [] [true] (raw operand) []).map Method.code
    decode call = some [.call call.method {}] ∧
      [{ call with name := "Other" }, { call with target := .external "forged" },
       { call with method.owner := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe" },
       { call with method.hasThis := true }, { call with parameterCount := 2 },
       { call with returnsValue := true }, { call with typeArguments := [.byref word] },
       { call with typeArguments := [] }, { call with method.genericArity := 2 }].all
        (fun changed => decide (decode changed = some [.unadmitted 40])) = true := by
  decide +kernel

#print axioms skipInitOperand

-- No live site emits the dedicated SkipInit instruction.
example : UnsafeCallsValid [] (raw call) [true] [.call call.method {}] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] nonCall [true] [.skipInit] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [] [.call call.method {}] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw call) [true] [] := by decide +kernel

-- `NullRef` must push the null reference: no other operation with its stack effect.
example : UnsafeCallsValid [] (raw nullCall) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true] [.ldc_i4 0] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true]
    [.ldsflda { owner := .void, index := 0, type := .void, name := name!"Field" }] := by
  decide +kernel
example : ¬ UnsafeCallsValid [] (raw nullCall) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with target := .external "forged" }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with parameterCount := 1 }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with returnsValue := false }) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with method.hasThis := true }) [true]
    [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { nullCall with typeArguments := [.byref word] }) [true] [.memory .nullRef] := by decide +kernel

-- `IsNullRef` must test for null: a constant or a reinterpretation cannot stand in for it.
example : UnsafeCallsValid [] (raw testCall) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw testCall) [true] [.memory .asRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw testCall) [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with name := "NullRef" }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with target := .external "forged" }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with parameterCount := 2 }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with returnsValue := false }) [true] [.memory .isNullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] (raw { testCall with typeArguments := [word, word] }) [true] [.memory .isNullRef] := by decide +kernel

/-- A closed Boolean result includes its defining assembly. -/
theorem isNullRefResultScope :
    UnsafeHelper.isNullRef.resolves [] testCall = true ∧
      UnsafeHelper.isNullRef.resolves [] { testCall with
        method.returnType := .atom "Fixture" "System.Boolean" } = false := by decide +kernel

#print axioms isNullRefResultScope

-- A helper operation cannot replace an unrelated instruction.
example : ¬ UnsafeCallsValid [] nonCall [true] [.memory .nullRef] := by decide +kernel
example : ¬ UnsafeCallsValid [] nonCall [true] [.memory .isNullRef] := by decide +kernel
example : UnsafeCallsValid [] nonCall [true] [.pop] := by decide +kernel
-- Unreachable sites are emitted as holes and are not bound.
example : UnsafeCallsValid [] (raw nullCall) [false] [.unadmitted 0x28] := by decide +kernel

end Tests.UnsafeCallEvidence

namespace Tests.UnsafeCallEvidence

/-- A type of the fixture's own assembly with the runtime `Unsafe` class's name. -/
private def localUnsafe : TypeExpr := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe"

/-- A managed generic AreSame method in the fixture's assembly. -/
private def localAreSame : CallSite := {
  declared := {
    convention := 0x10, returnType := .atom runtimeScope "System.Boolean",
    parameters := [.byref (.parameter 0), .byref (.parameter 0)] }
  method := {
    owner := localUnsafe, name := name!"AreSame", hasThis := false, genericArity := 1,
    methodArguments := [word], returnType := .atom runtimeScope "System.Boolean",
    parameters := [.byref word, .byref word] }
  name := "AreSame", target := .managed 23, typeArguments := [word],
  parameterCount := 2, returnsValue := true }

/-- A managed lookalike retains its operand and the direct link to its instantiated method. -/
theorem local_reference_helper_name :
    let instruction := RawInstruction.mk 0 40 (.call localAreSame)
    let emitted := Instruction.call localAreSame.method {}
    let callee : SpecializedMethod := {
      arguments := [word], closed := { raw localAreSame with
        token := 23, owner := "Fixture::System.Runtime.CompilerServices.Unsafe",
        parameters := localAreSame.parameterTypes, returnType := localAreSame.returnType } }
    let check := validateManagedCallWith 1 (fun i => if i == 0 then some callee else none)
      (fun _ => none) instruction true
    UnsafeCallsValid [] (raw localAreSame) [true] [emitted] ∧
      siteClaim loweredCallFamily {} (some (.direct 0)) instruction = .link ∧
      check (some (.direct 0)) emitted = true ∧ check (some (.direct 1)) emitted = false := by
  decide +kernel
#print axioms local_reference_helper_name

/-- A helper which resolves to a hole accepts exactly the hole with that raw opcode. -/
theorem unresolvedHelperOnlyHole (layouts : List RawLayout) (raw : RawInstruction)
    (helper : UnsafeHelper) (emitted : CIL.Instruction)
    (family : unsafeHelperFamily raw = some helper)
    (unresolved : helper.decode layouts raw = .unadmitted raw.opcode) :
    unsafeHelperMatches layouts raw emitted = true ↔ emitted = .unadmitted raw.opcode := by
  simp only [unsafeHelperMatches, family, unresolved]
  cases emitted <;> simp

#print axioms unresolvedHelperOnlyHole

/-- A resolving helper accepts only its own operation. -/
theorem resolvedHelperOnlyOperation (layouts : List RawLayout) (raw : RawInstruction)
    (helper : UnsafeHelper) (emitted : CIL.Instruction)
    (family : unsafeHelperFamily raw = some helper)
    (resolved : helper.decode layouts raw = helper.instruction) :
    unsafeHelperMatches layouts raw emitted = true ↔ emitted = helper.instruction := by
  simp only [unsafeHelperMatches, family, resolved]
  cases helper <;> cases emitted <;> simp [UnsafeHelper.instruction, emittedUnsafeHelper] <;>
    rename_i operation <;> cases operation <;> simp

#print axioms resolvedHelperOnlyOperation

end Tests.UnsafeCallEvidence
