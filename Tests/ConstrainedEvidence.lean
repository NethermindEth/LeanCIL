import CIL.Extraction.Constrained

/-! # Independently tampered constrained-call metadata and translations -/
namespace Tests.ConstrainedEvidence
open CIL CIL.Extraction

private def integer : TypeExpr := .atom runtimeScope "System.Int32"
private def receiver : TypeExpr := .aggregate "Fixture::Counter" 0
private def interface : TypeExpr := .atom "Fixture" "IValue"
private def slot : DispatchMethod := {
  token := 5, name := "Read", hasThis := true, isPublic := true, isAbstract := true,
  isVirtual := true, hasBody := false, genericArity := 0, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := integer, parameters := [], overrides := [] }
private def implementation : DispatchMethod := {
  slot with token := 21, isAbstract := false, hasBody := true }
private def concrete : DispatchType := {
  identity := receiver, valueType := true, interfaceType := false,
  interfaces := [interface], methods := [implementation] }
private def declared : DispatchType := {
  identity := interface, valueType := false, interfaceType := true,
  interfaces := [], methods := [slot] }
private def types := [concrete, declared]
private def site : CallSite := {
  declaringType := interface, name := "Read", target := .managed 5, typeArguments := [],
  parameterCount := 0, hasThis := true, returnsValue := true,
  returnType := integer, parameterTypes := [] }
private def raw : RawMethod := {
  token := 1, owner := "Fixture::Caller", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := integer, parameters := [.byref receiver], locals := [], initLocals := false,
  maxStack := 1, genericParameters := [], code :=
    [⟨0, 2, .none⟩, ⟨1, 65046, .type receiver⟩, ⟨7, 111, .call site⟩, ⟨12, 42, .none⟩] }
private def target : SpecializedMethod := ⟨[], { raw with
  token := 21, owner := "Fixture::Counter", hasThis := true, parameters := [],
  code := [⟨0, 23, .none⟩, ⟨1, 42, .none⟩] }⟩
private def methods := [⟨[], raw⟩, target]
private def emitted : Method := {
  locals := [], returnsValue := true, code := [.arg 0, .nop, .call 1 1, .ret] }

theorem concrete_call_valid :
    ConstrainedCallsValid types methods raw [true, true, true, true] emitted := by decide +kernel
#print axioms concrete_call_valid

theorem changed_target_rejected :
    ¬ ConstrainedCallsValid types methods raw [true, true, true, true]
      { emitted with code := emitted.code.set 2 (.call 0 1) } := by decide +kernel
#print axioms changed_target_rejected

theorem changed_arity_rejected :
    ¬ ConstrainedCallsValid types methods raw [true, true, true, true]
      { emitted with code := emitted.code.set 2 (.call 1 0) } := by decide +kernel
#print axioms changed_arity_rejected

theorem prefix_bypass_rejected :
    ¬ ConstrainedCallsValid types methods
      { raw with code := raw.code.set 0 ⟨0, 43, .target 2⟩ }
      [true, true, true, true] emitted := by decide +kernel
#print axioms prefix_bypass_rejected

theorem missing_prefix_rejected :
    ¬ ConstrainedCallsValid types methods
      { raw with code := raw.code.set 1 ⟨1, 0, .none⟩ }
      [true, true, true, true] emitted := by decide +kernel
#print axioms missing_prefix_rejected

theorem changed_signature_rejected :
    ¬ ConstrainedCallsValid types
      [⟨[], raw⟩, { target with closed := { target.closed with returnType := .void } }]
      raw [true, true, true, true] emitted := by decide +kernel
#print axioms changed_signature_rejected

theorem ambiguous_implementation_rejected :
    resolveConstrained
      [{ concrete with methods := [implementation, { implementation with token := 22 }] }, declared]
      receiver site = none := by decide +kernel
#print axioms ambiguous_implementation_rejected

theorem explicit_override_precedes_implicit :
    (resolveConstrained
      [{ concrete with methods := [implementation,
        { implementation with
          token := 22, name := "IValue.Read", isPublic := false, overrides := [5] }] }, declared]
      receiver site).map (·.token) = some 22 := by decide +kernel
#print axioms explicit_override_precedes_implicit

theorem missing_interface_rejected :
    resolveConstrained [{ concrete with interfaces := [] }, declared] receiver site = none := by
  decide +kernel
#print axioms missing_interface_rejected

theorem reference_receiver_rejected :
    resolveConstrained [{ concrete with valueType := false }, declared] receiver site = none := by
  decide +kernel
#print axioms reference_receiver_rejected

/-- Even an unreachable switch arm cannot bypass the constrained prefix. -/
theorem unreachable_switch_bypass_rejected :
    ¬ ConstrainedCallsValid types methods
      { raw with code := raw.code.set 0 ⟨0, 69, .targets [3, 2, 2]⟩ }
      [false, true, true, true] emitted := by decide +kernel
#print axioms unreachable_switch_bypass_rejected

/-- A missing reachability entry is not an unreachable instruction exemption. -/
theorem short_reachability_rejected :
    ¬ ConstrainedCallsValid types methods raw [true, true, true] emitted := by decide +kernel
#print axioms short_reachability_rejected

/-- A branch to the prefix is allowed; only entering after it bypasses the receiver check. -/
theorem prefix_target_valid :
    ConstrainedCallsValid types methods
      { raw with code := raw.code.set 0 ⟨0, 43, .target 1⟩ }
      [true, true, true, true] emitted := by decide +kernel
#print axioms prefix_target_valid
/-- Lowering retains byte offsets while replacing the prefix and resolved call target. -/
theorem lowered_call_exact :
    (lowerConstrainedRaw types raw).code =
      [⟨0, 2, .none⟩, ⟨1, 0, .none⟩,
        ⟨7, 40, .call { site with target := .managed 21, declaringType := receiver }⟩,
        ⟨12, 42, .none⟩] := by decide +kernel
#print axioms lowered_call_exact

/-- Index zero has no prefix; lowering must not invent one through truncated subtraction. -/
theorem lowering_first_call_unchanged :
    lowerConstrainedRaw types { raw with code := [⟨0, 111, .call site⟩] } =
      { raw with code := [⟨0, 111, .call site⟩] } := by decide +kernel
#print axioms lowering_first_call_unchanged

/-- Failure to resolve metadata retains the original call for the later validator to reject. -/
theorem lowering_unresolved_call_retained :
    (lowerConstrainedRaw [] raw).code[2]? = raw.code[2]? := by decide +kernel
#print axioms lowering_unresolved_call_retained
end Tests.ConstrainedEvidence
