import CIL.Extraction.Generics
import CIL.Safety.SymbolicExecution

namespace Tests.ExtractionGenerics
open CIL CIL.Extraction

def word : TypeExpr := .atom "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64"
def raw : RawMethod := {
  token := 1, owner := "Test::Owner", hasThis := false, explicitThis := false,
  callingConvention := 16, attributes := 0, implementation := 0,
  returnType := .parameter 0, parameters := [.byref (.parameter 0)],
  locals := [.parameter 0], initLocals := true, maxStack := 2,
  genericParameters := [⟨24, []⟩],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type (.parameter 0)⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
def closed : RawMethod := { raw with
  callingConvention := 0, returnType := word, parameters := [.byref word],
  locals := [word], genericParameters := [],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
example : instantiateMethod [] raw [word] = some closed := by decide
example : instantiateMethod [] raw [] = none := by decide
example : instantiateMethod [] raw [.byref word] = none := by decide
example : instantiateMethod [] { raw with genericParameters := [⟨4, []⟩] } [word] = none := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with locals := [] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with returnType := .void } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with code := [⟨0, 42, .none⟩] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with
    code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 1⟩, ⟨9, 42, .none⟩] } := by decide
example : typeStorage [] (.atom "attacker" "System.UInt64") = none := by decide
example : typeStorage [{
    identity := "A", explicit := false, packing := 0, declaredSize := 0, fields := []
  }] (.aggregate "B" 0) = none := by decide
example : substituteType [word] (.apply (.constructor "scope" "Box`1") (.parameter 0)) =
    some (.apply (.constructor "scope" "Box`1") word) := by decide

/-- A call whose scoped signature and generic arguments match the selected closed method. -/
def caller (parameter : TypeExpr) : RawMethod := { closed with code := [⟨0, 40, .call {
  declaringType := .atom "Test" "Owner", name := "Call", target := .managed 1,
  typeArguments := [word], parameterCount := 1, hasThis := false, returnsValue := true,
  returnType := word, parameterTypes := [.byref parameter] }⟩] }

/-- The emitted target and argument count are independently checked against the call site. -/
def callCode : Method := { locals := [], returnsValue := true, code := [.call 0 1] }

/-- Structural proof construction retains the complete managed-call predicate. -/
theorem structural_call : ManagedCallsValid [⟨[word], closed⟩] [] (caller word) [true]
    callCode := by
  cil_strict (cil_managed_calls [caller, closed, raw, word, callCode])
#print axioms structural_call

/-- Equal storage width does not permit substituting a signed parameter. -/
theorem signed_parameter_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] []
      (caller (.atom runtimeScope "System.Int64")) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] []
        (caller (.atom runtimeScope "System.Int64")) [true] callCode := by
      cil_managed_calls [caller, closed, raw, word, callCode]))
  decide +kernel
#print axioms signed_parameter_rejected

/-- A matching type name from another assembly remains a different parameter type. -/
theorem parameter_scope_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] []
      (caller (.atom "attacker" "System.UInt64")) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] []
        (caller (.atom "attacker" "System.UInt64")) [true] callCode := by
      cil_managed_calls [caller, closed, raw, word, callCode]))
  decide +kernel
#print axioms parameter_scope_rejected

/-- A closed signature cannot stand in for different method type arguments. -/
theorem generic_argument_rejected :
    ¬ ManagedCallsValid [⟨[.atom runtimeScope "System.Int64"], closed⟩] []
      (caller word) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[.atom runtimeScope "System.Int64"], closed⟩] []
        (caller word) [true] callCode := by
      cil_managed_calls [caller, closed, raw, word, callCode]))
  decide +kernel
#print axioms generic_argument_rejected

/-- Structural proof construction rejects a call with an altered argument count. -/
theorem argument_count_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] [] (caller word) [true]
      { callCode with code := [.call 0 2] } := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] [] (caller word) [true]
        { callCode with code := [.call 0 2] } := by
      cil_managed_calls [caller, closed, raw, word, callCode]))
  decide +kernel
#print axioms argument_count_rejected

end Tests.ExtractionGenerics
