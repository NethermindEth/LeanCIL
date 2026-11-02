import CIL.Extraction.Constrained

/-! # Independently tampered constrained-call metadata and translations -/
namespace Tests.ConstrainedEvidence
open CIL CIL.Extraction

/-- ASCII acceleration retains Unicode metadata and malformed-name rejection. -/
theorem named_metadata_decoding :
    namedType (.aggregate "Fixture::Counter" 0) =
      some ("Fixture".toList, "Counter".toList) ∧
    namedType (.aggregate "Σcope::Counter" 0) = some ("Σcope".toList, "Counter".toList) ∧
    namedType (.atom "Fixturé" "Counter") = some ("Fixturé".toList, "Counter".toList) ∧
    namedType (.atom "Fixture" "Countér") = none ∧
    namedType (.aggregate "Fixture:Counter" 0) = none ∧
    namedType (.aggregate "Fixture::Counter[]" 0) = none ∧
    namedType (.atom "" "Counter") = none := by decide +kernel
#print axioms named_metadata_decoding

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
          token := 22, name := "IValue.Read", isPublic := false, overrides := [(5, interface)] }] }, declared]
      receiver site).map (·.method.token) = some 22 := by decide +kernel
#print axioms explicit_override_precedes_implicit

private def staticSlot : DispatchMethod := { slot with token := 6, hasThis := false }
private def staticImplementation : DispatchMethod := {
  staticSlot with token := 31, isAbstract := false, isVirtual := false, hasBody := true }
private def staticTypes : List DispatchType :=
  [{ concrete with methods := [staticImplementation] }, { declared with methods := [staticSlot] }]
private def staticSite : CallSite := { site with target := .managed 6, hasThis := false }
private def staticRaw : RawMethod := { raw with
  parameters := [], code := [⟨0, 65046, .type receiver⟩, ⟨6, 40, .call staticSite⟩, ⟨11, 42, .none⟩] }
private def staticTarget : SpecializedMethod := ⟨[], { raw with
  token := 31, owner := "Fixture::Counter", parameters := [],
  code := [⟨0, 22, .none⟩, ⟨1, 42, .none⟩] }⟩
private def staticMethods := [⟨[], staticRaw⟩, staticTarget]
private def staticEmitted : Method := {
  locals := [], returnsValue := true, code := [.nop, .call 1 0, .ret] }

/-- A static interface slot (`constrained. T; call`) resolves to the receiver's static
    implementation, called without a receiver argument. -/
theorem static_call_valid :
    ConstrainedCallsValid staticTypes staticMethods staticRaw [true, true, true] staticEmitted := by
  decide +kernel
#print axioms static_call_valid

theorem static_call_with_receiver_rejected :
    ¬ ConstrainedCallsValid staticTypes staticMethods staticRaw [true, true, true]
      { staticEmitted with code := staticEmitted.code.set 1 (.call 1 1) } := by decide +kernel
#print axioms static_call_with_receiver_rejected

/-- `callvirt` never dispatches a static slot, and `call` never dispatches an instance slot. -/
theorem call_opcode_mismatch_rejected :
    ¬ ConstrainedCallsValid staticTypes staticMethods
      { staticRaw with code := staticRaw.code.set 1 ⟨6, 111, .call staticSite⟩ }
      [true, true, true] staticEmitted ∧
    ¬ ConstrainedCallsValid types methods
      { raw with code := raw.code.set 2 ⟨7, 40, .call site⟩ }
      [true, true, true, true] emitted := by decide +kernel
#print axioms call_opcode_mismatch_rejected

/-- A static slot is never implemented by an instance method or declared on the struct itself. -/
theorem static_slot_mismatches_rejected :
    resolveConstrained [concrete, { declared with methods := [staticSlot] }]
      receiver staticSite = none ∧
    resolveConstrained [{ concrete with methods := [{ staticImplementation with token := 6 }] }]
      receiver { staticSite with declaringType := receiver } = none := by decide +kernel
#print axioms static_slot_mismatches_rejected

/-- An instance default interface method slot is rejected even when the struct implements it:
    its body would run on a boxed receiver. -/
theorem default_interface_slot_rejected :
    resolveConstrained
      [concrete, { declared with methods := [{ slot with isAbstract := false, hasBody := true }] }]
      receiver site = none := by decide +kernel
#print axioms default_interface_slot_rejected

private def boolean : TypeExpr := .atom runtimeScope "System.Boolean"
private def allowance : TypeExpr := .aggregate "Fixture::Allowance" 0
private def price : TypeExpr := .aggregate "Fixture::Price" 1
private def allowanceOwner : TypeExpr := .constructor "Fixture" "IAllowance`1"
private def allowanceInterface : TypeExpr := .apply allowanceOwner allowance
/-- `static virtual bool Spend<TPrice>(ref TSelf self)` with a body, on `IAllowance<Allowance>`. -/
private def defaultSlot : DispatchMethod := {
  token := 40, name := "Spend", hasThis := false, isPublic := true, isAbstract := false,
  isVirtual := true, hasBody := true, genericArity := 1, explicitThis := false,
  callingConvention := 16, attributes := 0, implementation := 0,
  returnType := boolean, parameters := [.byref allowance], overrides := [],
  owner := allowanceOwner, ownerArguments := [allowance] }
/-- The struct's recorded generic implementation of the default slot. -/
private def genericOverride : DispatchMethod := {
  defaultSlot with
    token := 41, name := "IAllowance.Spend", isPublic := false, isVirtual := false,
    overrides := [(40, allowanceInterface)], owner := .void, ownerArguments := [] }
private def defaultConcrete : DispatchType := {
  identity := allowance, valueType := true, interfaceType := false,
  interfaces := [allowanceInterface], methods := [] }
private def defaultDeclared : DispatchType := {
  identity := allowanceInterface, valueType := false, interfaceType := true,
  interfaces := [], methods := [defaultSlot] }
private def defaultTypes := [defaultConcrete, defaultDeclared]
private def overrideTypes :=
  [{ defaultConcrete with methods := [genericOverride] }, defaultDeclared]
/-- `constrained. Allowance; call bool IAllowance<Allowance>::Spend<Price>(TSelf&)`. -/
private def defaultSite : CallSite := {
  declaringType := allowanceInterface, name := "Spend", target := .managed 40,
  typeArguments := [price, allowance], ownerArgumentCount := 1, parameterCount := 1,
  hasThis := false, returnsValue := true, returnType := boolean,
  parameterTypes := [.byref allowance] }
private def defaultRaw : RawMethod := { raw with
  parameters := [.byref allowance],
  code := [⟨0, 2, .none⟩, ⟨1, 65046, .type allowance⟩, ⟨7, 40, .call defaultSite⟩,
    ⟨12, 42, .none⟩] }
/-- The default body instantiated at `TPrice := Price` and `TSelf := Allowance`. -/
private def defaultTarget : SpecializedMethod := ⟨[price, allowance], { raw with
  token := 40, owner := "Fixture::IAllowance`1", ownerArgumentCount := 1,
  returnType := boolean, parameters := [.byref allowance],
  code := [⟨0, 2, .none⟩, ⟨1, 42, .none⟩] }⟩
/-- The recorded override instantiated at `TPrice := Price`. -/
private def overrideTarget : SpecializedMethod := ⟨[price], { defaultTarget.closed with
  token := 41, owner := "Fixture::Allowance", ownerArgumentCount := 0 }⟩
private def defaultEmitted : Method := {
  locals := [], returnsValue := true, code := [.arg 0, .nop, .call 1 1, .ret] }

/-- Without an implementation on the receiver, a generic static virtual slot runs its own body,
    instantiated at the site's method and interface arguments. -/
theorem static_default_valid :
    resolveConstrained defaultTypes allowance defaultSite = some (.interfaceDefault defaultSlot) ∧
    ConstrainedCallsValid defaultTypes [⟨[], defaultRaw⟩, defaultTarget] defaultRaw
      [true, true, true, true] defaultEmitted := by decide +kernel
#print axioms static_default_valid

/-- A recorded generic override wins over the default body, and only it may be emitted. -/
theorem static_override_precedes_default :
    (resolveConstrained overrideTypes allowance defaultSite).map (·.method.token) = some 41 ∧
    ConstrainedCallsValid overrideTypes [⟨[], defaultRaw⟩, overrideTarget] defaultRaw
      [true, true, true, true] defaultEmitted ∧
    ¬ ConstrainedCallsValid overrideTypes [⟨[], defaultRaw⟩, defaultTarget] defaultRaw
      [true, true, true, true] defaultEmitted ∧
    ¬ ConstrainedCallsValid defaultTypes [⟨[], defaultRaw⟩, overrideTarget] defaultRaw
      [true, true, true, true] defaultEmitted := by decide +kernel
#print axioms static_override_precedes_default

/-- An unrecorded public same-signature method beside a default body is ambiguous, and an
    abstract generic slot with no implementation has no target. -/
theorem static_default_ambiguity_rejected :
    resolveConstrained [{ defaultConcrete with methods := [{ genericOverride with
        name := "Spend", isPublic := true, overrides := [] }] }, defaultDeclared]
      allowance defaultSite = none ∧
    resolveConstrained [defaultConcrete, { defaultDeclared with methods :=
        [{ defaultSlot with isAbstract := true, hasBody := false }] }]
      allowance defaultSite = none := by decide +kernel
#print axioms static_default_ambiguity_rejected

/-- The emitted instance must carry the site's method type argument, the site must supply
    exactly the slot's method arity, closed, and instance slots take no method arguments. -/
theorem static_default_arguments_rejected :
    ¬ ConstrainedCallsValid defaultTypes
      [⟨[], defaultRaw⟩, { defaultTarget with arguments := [allowance, allowance] }]
      defaultRaw [true, true, true, true] defaultEmitted ∧
    resolveConstrained defaultTypes allowance
      { defaultSite with typeArguments := [allowance] } = none ∧
    resolveConstrained defaultTypes allowance
      { defaultSite with typeArguments := [price, price, allowance] } = none ∧
    resolveConstrained defaultTypes allowance
      { defaultSite with typeArguments := [.parameter 0, allowance] } = none ∧
    resolveConstrained
      [{ concrete with methods :=
          [{ implementation with genericArity := 1, callingConvention := 16 }] },
        { declared with methods := [{ slot with genericArity := 1, callingConvention := 16 }] }]
      receiver { site with typeArguments := [integer] } = none := by
  decide +kernel
#print axioms static_default_arguments_rejected

/-- A default body is never reached through another interface instantiation, a receiver that
    does not implement it, or a default declared with mismatched owner metadata. -/
theorem static_default_owner_rejected :
    resolveConstrained [{ defaultConcrete with interfaces := [] }, defaultDeclared]
      allowance defaultSite = none ∧
    resolveConstrained [defaultConcrete, { defaultDeclared with methods :=
        [{ defaultSlot with ownerArguments := [price] }] }] allowance defaultSite = none ∧
    resolveConstrained [defaultConcrete, { defaultDeclared with methods :=
        [{ defaultSlot with owner := .constructor "Other" "IAllowance`1" }] }]
      allowance defaultSite = none := by decide +kernel
#print axioms static_default_owner_rejected

private def derivedInterface : TypeExpr := .apply (.constructor "Fixture" "IRefund`1") allowance
/-- `IRefund<TSelf> : IAllowance<TSelf>` re-implementing `IAllowance<TSelf>.Spend<TPrice>`. -/
private def derivedDeclared : DispatchType := {
  identity := derivedInterface, valueType := false, interfaceType := true,
  interfaces := [allowanceInterface], methods := [{ genericOverride with
    token := 50, owner := .constructor "Fixture" "IRefund`1", ownerArguments := [allowance] }] }
private def derivedConcrete : DispatchType :=
  { defaultConcrete with interfaces := [allowanceInterface, derivedInterface] }

/-- A derived interface of the receiver that re-implements the slot is more specific than the
    default body, so the default is never selected; an interface missing from the catalog or an
    inherited interface the receiver does not list fails closed. -/
theorem static_default_shadowed_rejected :
    resolveConstrained [derivedConcrete, defaultDeclared, derivedDeclared]
      allowance defaultSite = none ∧
    ¬ ConstrainedCallsValid [derivedConcrete, defaultDeclared, derivedDeclared]
      [⟨[], defaultRaw⟩, defaultTarget] defaultRaw [true, true, true, true] defaultEmitted ∧
    resolveConstrained [derivedConcrete, defaultDeclared, { derivedDeclared with methods := [] }]
      allowance defaultSite = some (.interfaceDefault defaultSlot) ∧
    resolveConstrained [derivedConcrete, defaultDeclared] allowance defaultSite = none ∧
    resolveConstrained [defaultConcrete, { defaultDeclared with interfaces := [derivedInterface] }]
      allowance defaultSite = none := by decide +kernel
#print axioms static_default_shadowed_rejected

/-- Lowering keeps the default body's closed interface and method type argument, and moves an
    override to the receiver with only the method type argument. -/
theorem lowered_default_exact :
    (lowerConstrainedRaw defaultTypes defaultRaw).code[2]? =
      some ⟨7, 40, .call defaultSite⟩ ∧
    (lowerConstrainedRaw overrideTypes defaultRaw).code[2]? =
      some ⟨7, 40, .call { defaultSite with
        target := .managed 41, declaringType := allowance, typeArguments := [price],
        ownerArgumentCount := 0 }⟩ := by decide +kernel
#print axioms lowered_default_exact

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
/-- A trailing prefix cannot read a nonexistent next instruction from the streaming cursor. -/
theorem trailing_prefix_rejected :
    ¬ ConstrainedCallsValid types methods { raw with code := [⟨0, 65046, .type receiver⟩] }
      [true] { emitted with code := [.nop] } := by decide +kernel
#print axioms trailing_prefix_rejected

/-- Streaming completion still rejects extra emitted instructions. -/
theorem extra_emitted_rejected :
    ¬ ConstrainedCallsValid types methods raw [true, true, true, true]
      { emitted with code := emitted.code ++ [.nop] } := by decide +kernel
#print axioms extra_emitted_rejected
/-- Exact identities reject duplicates and distinguish aggregate indexes and assembly scopes. -/
theorem indexed_type_identity :
    (DispatchIndex.ofTypes [concrete, concrete, declared]).resolve receiver site = none ∧
    (DispatchIndex.ofTypes [concrete, declared]).resolve
      (.aggregate "Fixture::Counter" 1) site = none ∧
    (DispatchIndex.ofTypes [concrete, declared]).resolve receiver
      { site with declaringType := .atom "Other" "IValue" } = none := by decide +kernel
#print axioms indexed_type_identity

/-- Repeated override tokens do not duplicate one implementation; explicit still wins. -/
theorem indexed_override_precedence :
    ((DispatchIndex.ofTypes [{ concrete with methods := [implementation,
      { implementation with
        token := 22, name := "IValue.Read", isPublic := false, overrides := [(5, interface), (5, interface)] }] },
      declared]).resolve receiver site).map (·.method.token) = some 22 := by
  decide +kernel
#print axioms indexed_override_precedence

/-- Multiple matching methods remain ambiguous for token, explicit and implicit selection. -/
theorem indexed_method_ambiguity :
    (DispatchIndex.ofTypes [concrete, { declared with methods := [slot, slot] }]).resolve
      receiver site = none ∧
    (DispatchIndex.ofTypes [{ concrete with methods := [implementation, implementation] },
      declared]).resolve receiver site = none ∧
    (DispatchIndex.ofTypes [{ concrete with methods := [
      { implementation with overrides := [(5, interface)] },
      { implementation with token := 22, overrides := [(5, interface)] }] }, declared]).resolve
      receiver site = none := by decide +kernel
#print axioms indexed_method_ambiguity
private def genericOwner : TypeExpr := .constructor "Fixture" "Counter`1"
private def genericReceiver : TypeExpr :=
  .aggregate ("Fixture::Counter`1<" ++ runtimeScope ++ "::System.Int32>") 0
private def genericImplementation : DispatchMethod := {
  implementation with owner := genericOwner, ownerArguments := [integer] }
private def genericTypes : List DispatchType := [
  { concrete with identity := genericReceiver, methods := [genericImplementation] }, declared]
private def genericRaw : RawMethod := { raw with
  parameters := [.byref genericReceiver],
  code := raw.code.set 1 ⟨1, 65046, .type genericReceiver⟩ }
private def genericTarget : SpecializedMethod := ⟨[integer], {
  target.closed with owner := "Fixture::Counter`1", ownerArgumentCount := 1 }⟩

/-- Closed owner specialization composes with the existing exact constrained-call rule. -/
theorem generic_call_valid :
    ConstrainedCallsValid genericTypes [⟨[], genericRaw⟩, genericTarget]
      genericRaw [true, true, true, true] emitted := by decide +kernel
#print axioms generic_call_valid

/-- A different specialization of the same method token cannot satisfy the receiver. -/
theorem changed_owner_arguments_rejected :
    ¬ ConstrainedCallsValid genericTypes [⟨[], genericRaw⟩,
      { genericTarget with arguments := [.atom runtimeScope "System.Int64"] }]
      genericRaw [true, true, true, true] emitted := by decide +kernel
#print axioms changed_owner_arguments_rejected

/-- The owner arity cannot be dropped while retaining a selected generic method body. -/
theorem changed_owner_arity_rejected :
    ¬ ConstrainedCallsValid genericTypes [⟨[], genericRaw⟩,
      { genericTarget with closed := { genericTarget.closed with ownerArgumentCount := 0 } }]
      genericRaw [true, true, true, true] emitted := by decide +kernel
#print axioms changed_owner_arity_rejected

/-- Dispatch metadata cannot substitute a same-named owner from another assembly. -/
theorem changed_owner_scope_rejected :
    resolveConstrained [
      { concrete with identity := genericReceiver, methods := [
        { genericImplementation with owner := .constructor "Other" "Counter`1" }] }, declared]
      genericReceiver site = none := by decide +kernel
#print axioms changed_owner_scope_rejected

end Tests.ConstrainedEvidence
