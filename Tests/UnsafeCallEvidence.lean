import CIL.Extraction.DecodedMethod
import Tests.Support.RawDecoding
import Tests.Support.FixtureAssembly

/-! Exact runtime operands, modelled reference helpers and the opcodes that can emit null. -/

open CIL CIL.Extraction

namespace Tests.UnsafeCallEvidence

private def scope :=
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def unsafeType : TypeExpr := .atom scope "System.Runtime.CompilerServices.Unsafe"
    .classType
private def word : TypeExpr := .primitive .uint64
private def call : CallSite := {
  declared := { convention := 0x10, parameters := [.byref (.parameter 0)] },
  method := {
    owner := unsafeType, name := name!"SkipInit", hasThis := false, genericArity := 1,
    returnType := .void, parameters := [.byref word], methodArguments := [word] },
  name := "SkipInit",
  target := .external (scope ++ "::System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(\
    !!0&)"),
  typeArguments := [word], parameterCount := 1, returnsValue := false }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 1, genericParameters := [], code := [⟨0, 0x28, .call site⟩] }
private def nonCall : RawMethod := { raw call with code := [⟨0, 0x26, .none⟩] }

/-- Changing a redundant call field or the typed reference cannot retain the SkipInit call. -/
theorem skipInitOperand :
    let decode := fun operand =>
      (decodeRaw .scalar {} [] [true] (raw operand) []).map Method.code
    decode call = .ok [.call call.method {}] ∧
      [{ call with name := "Other" }, { call with target := .external "forged" },
       { call with
         method.owner := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe" .classType },
       { call with method.hasThis := true }, { call with parameterCount := 2 },
       { call with returnsValue := true }, { call with typeArguments := [.byref word] },
       { call with typeArguments := [] }, { call with method.genericArity := 2 }].all
        (fun changed => decide (decode changed = liveHoleAt 0 40)) = true := by
  decide +kernel

#print axioms skipInitOperand

-- A SkipInit call must retain the checked call operand.
example : UnsafeCallsValid (raw call) [true] [.call call.method {}] := by decide +kernel
example : ¬ UnsafeCallsValid (raw call) [true] [.pop] := by decide +kernel
example : ¬ UnsafeCallsValid (raw call) [] [.call call.method {}] := by decide +kernel
example : ¬ UnsafeCallsValid (raw call) [true] [] := by decide +kernel

-- A real SkipInit call and ordinary stack operations retain distinct opcode and metadata evidence.
example : Instruction.ofRaw? none ⟨0, 38, .none⟩ = some .pop ∧
    valueEncodingMatches none ⟨0, 38, .none⟩ (.call call.method {}) = false ∧
    Instruction.ofRaw? none ⟨0, 20, .none⟩ = some .ldnull ∧
    valueEncodingMatches none ⟨0, 20, .none⟩ (.call call.method {}) = false ∧
    Instruction.ofRaw? none ⟨0, 20, .call call⟩ = none := by decide +kernel
-- Unreachable sites are emitted as holes and are not bound.
example : UnsafeCallsValid (raw call) [false] [.unadmitted 0x28] := by decide +kernel

end Tests.UnsafeCallEvidence

namespace Tests.UnsafeCallEvidence

/-- A type of the fixture's own assembly with the runtime `Unsafe` class's name. -/
private def localUnsafe : TypeExpr := .atom fixtureScope "System.Runtime.CompilerServices.Unsafe"
    .classType

/-- A managed generic AreSame method in the fixture's assembly. -/
private def localAreSame : CallSite := {
  declared := {
    convention := 0x10, returnType := .primitive .boolean,
    parameters := [.byref (.parameter 0), .byref (.parameter 0)] }
  method := {
    owner := localUnsafe, name := name!"AreSame", hasThis := false, genericArity := 1,
    methodArguments := [word], returnType := .primitive .boolean,
    parameters := [.byref word, .byref word] }
  name := "AreSame", target := .managed 23, typeArguments := [word],
  parameterCount := 2, returnsValue := true }

/-- A managed lookalike retains its operand and the direct link to its instantiated method. -/
theorem local_reference_helper_name :
    let instruction := RawInstruction.mk 0 40 (.call localAreSame)
    let emitted := Instruction.call localAreSame.method {}
    let callee : SpecializedMethod := {
      assembly := ⟨fixtureAssembly⟩
      arguments := [word], closed := { raw localAreSame with
        token := 23, owner := fixtureScope ++ "::System.Runtime.CompilerServices.Unsafe",
        parameters := localAreSame.parameterTypes, returnType := localAreSame.returnType } }
    let check := validateManagedCallWith 1 (fun i => if i == 0 then some callee else none)
      (fun _ => none) instruction true
    UnsafeCallsValid (raw localAreSame) [true] [emitted] ∧
      siteClaim {} (some (.direct 0)) instruction = .link ∧
      check (some (.direct 0)) emitted = true ∧ check (some (.direct 1)) emitted = false := by
  decide +kernel
#print axioms local_reference_helper_name

end Tests.UnsafeCallEvidence
