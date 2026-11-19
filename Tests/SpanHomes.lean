import CIL.Extraction.Scalars
import CIL.Safety.ExecutionInvariants
import CIL.Safety.ValueRenaming
import Tests.Support

/-! # Span locals read through their homes

`ldloca` of a span local pushes a home that names the slot, and each consumer reads the slot when
it runs. These programs pin that reading against what the CLR returns: a store to the local after
`ldloca` is visible through the address, a callee that stores to its own slot 0 leaves the
caller's slot alone, an uninitialized slot faults where it is read, and no home crosses a frame
boundary. Admission refuses an address where a callee declares a span by value, so a call
projects a home only where the callee takes the span by reference. -/

namespace Tests.SpanHomes
open CIL CIL.Extraction CIL.Safety

set_option maxRecDepth 8192

/-- `System.Span<int>`, the type of every span local and parameter below. -/
private def intSpan : TypeExpr :=
  .apply (.constructor runtimeScope "System.Span`1") (.atom runtimeScope "System.Int32")

/-- `Span<int>.get_Length`, whose runtime model reads the view at its receiver. -/
private def getLength : MethodRef := {
  owner := intSpan, name := name!"get_Length", hasThis := true, genericArity := 0,
  returnType := .atom runtimeScope "System.Int32", parameters := [] }

/-- One live 16-byte caller allocation; the length getter reads no element bytes. -/
private def memory : Safety.Memory := { Memory.empty with
  allocations := fun identity => if identity == 0 then
    some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  nextIdentity := 1 }

/-- A writable int32 view of `length` elements at the start of allocation 0. -/
private def view (length : Nat) : Safety.Value := .bufferSpan ⟨.address ⟨0, 0⟩, length, 4, true⟩

/-- `local = first; ref local; local = second; return local.Length` through the saved address. -/
private def savedLength : Method := {
  code := [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .stloc 0, .call getLength {}, .ret]
  locals := [.nullRef], localKinds := [.span 4 true], returnsValue := true }

/-- The length is read when `get_Length` runs, after the second store, as the CLR reads it. -/
theorem saved_view_length :
    (invoke [savedLength] 16 0 [view 1, view 2] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] := rfl
#print axioms saved_view_length

/-- With the arguments swapped the same body returns the other length. -/
theorem saved_view_length_swapped :
    (invoke [savedLength] 16 0 [view 2, view 1] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] := rfl
#print axioms saved_view_length_swapped

/-- `Recurse(a, b, depth)` stores `a` in its slot 0 and, when `depth` is nonzero, leaves the
    address of that slot on the stack while it calls `Recurse(b, a, 0)`, which stores `b` in
    its own slot 0. The caller then reads the length through the address it kept. -/
private def recurse : Method := {
  code := [.ldarg 0, .stloc 0, .ldarg 2, .brfalse 12, .ldloca 0, .ldarg 1, .ldarg 0, .ldc_i4 0,
    .call (Tests.callee 3) {}, .pop, .call getLength {}, .ret,
    .ldloca 0, .call getLength {}, .ret]
  locals := [.nullRef], localKinds := [.span 4 true], returnsValue := true
  links := [(8, .direct 0)] }

/-- The address kept across the recursive call names the caller's own slot 0, which still holds
    `a`; the callee's store went to the callee's fresh slot. -/
theorem recursive_store_leaves_caller_slot :
    (invoke [recurse] 32 0 [view 1, view 2, .scalar (.i32 1)] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] ∧
    (invoke [recurse] 32 0 [view 2, view 1, .scalar (.i32 1)] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] := ⟨rfl, rfl⟩
#print axioms recursive_store_leaves_caller_slot

/-- A home passed to `invoke` names a slot of no frame, and entry refuses it. -/
theorem forged_home_refused_at_entry :
    (invoke [savedLength] 16 0 [.spanHome 0, view 2] memory).map Prod.snd =
      .error ⟨0, 0, .invalidState⟩ := rfl
#print axioms forged_home_refused_at_entry

/-- A span local of a method without `.locals init`. -/
private def uninitialized (code : List Instruction) : Method := {
  code, locals := [.unmodeled], localKinds := [.span 4 true], returnsValue := true }

/-- Taking the address of an uninitialized span local reads nothing; reading the slot through the
    address faults where the read runs, at the `get_Length` call. -/
theorem uninitialized_slot_read_through_home :
    (invoke [uninitialized [.ldloca 0, .pop, .ldc_i4 0, .ret]] 16 0 [] memory).map Prod.snd =
      .ok [.scalar (.i32 0)] ∧
    (invoke [uninitialized [.ldloca 0, .call getLength {}, .ret]] 16 0 [] memory).map
      Prod.snd = .error ⟨0, 1, .invalidState⟩ := ⟨rfl, rfl⟩
#print axioms uninitialized_slot_read_through_home

/-- `initobj` through the home of an uninitialized span local stores the empty view. -/
theorem initobj_through_home :
    (invoke [uninitialized [.ldloca 0, .initobj intSpan, .ldloca 0, .call getLength {}, .ret]]
      16 0 [] memory).map Prod.snd = .ok [.scalar (.i32 0)] := rfl
#print axioms initobj_through_home

/-- `Span<int>(ref int)`, the single-element constructor a call runs on a span home. -/
private def singleConstructor : MethodRef := {
  owner := intSpan, name := name!".ctor", hasThis := true, genericArity := 0,
  returnType := .void, parameters := [.byref (.atom runtimeScope "System.Int32")] }

/-- The address of the first int32 of allocation 0, the element a single-element span views. -/
private def element : Safety.Value := .reference (.address ⟨0, 0⟩)

/-- A constructor call on the home of a span local replaces the view in the slot: the local held
    a two-element view, or nothing, and the length read through the home afterwards is 1. -/
theorem constructor_through_local_home :
    (invoke [{ savedLength with
      code := [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .call singleConstructor {}, .ldloca 0,
        .call getLength {}, .ret] }] 16 0 [view 2, element] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] ∧
    (invoke [uninitialized [.ldloca 0, .ldarg 0, .call singleConstructor {}, .ldloca 0,
        .call getLength {}, .ret]] 16 0 [element] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] := ⟨rfl, rfl⟩
#print axioms constructor_through_local_home

/-- A home cannot leave its frame by `ret` or be stored as a value in another local. -/
theorem home_stays_in_frame :
    (invoke [{ savedLength with code := [.ldarg 0, .stloc 0, .ldloca 0, .ret] }] 16 0
      [view 1, view 2] memory).map Prod.snd = .error ⟨0, 3, .invalidState⟩ ∧
    (invoke [{ savedLength with
      code := [.ldarg 0, .stloc 0, .ldloca 0, .stloc 1, .ldc_i4 0, .ret],
      locals := [.nullRef, .nullRef], localKinds := [.span 4 true, .span 4 true] }] 16 0
      [view 1, view 2] memory).map Prod.snd = .error ⟨0, 3, .invalidState⟩ := ⟨rfl, rfl⟩
#print axioms home_stays_in_frame

/-- Returns the length of the span it receives. -/
private def reader : Method := {
  code := [.ldarg 0, .call getLength {}, .ret], locals := [], returnsValue := true }

/-- Passes the address of its span local to `reader` after storing the second view there. -/
private def passesHome : Method := {
  code := [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .stloc 0, .call (Tests.callee 1) {}, .ret]
  locals := [.nullRef], localKinds := [.span 4 true], returnsValue := true
  links := [(5, .direct 1)] }

/-- A linked call reads the home when the call runs, so the callee receives the second view. -/
theorem linked_call_receives_view :
    (invoke [passesHome, reader] 32 0 [view 1, view 2] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] ∧
    (invoke [passesHome, reader] 32 0 [view 2, view 1] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] := ⟨rfl, rfl⟩
#print axioms linked_call_receives_view

/-- Takes the address of its by-value span parameter, stores the second argument to it with
    `starg` and reads the length through the address. -/
private def homedParameter : Method := {
  code := [.ldarga 0, .ldarg 1, .starg 0, .call getLength {}, .ret]
  locals := [], parameterHomes := [(0, .span 4 true)], returnsValue := true }

/-- `ldarga` of a homed span parameter is a home, so the read sees the `starg`. -/
theorem parameter_home_sees_store :
    (invoke [homedParameter] 16 0 [view 1, view 2] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] := rfl
#print axioms parameter_home_sees_store

/-- A constructor call on the home of a by-value span parameter replaces the argument's view. -/
theorem constructor_through_parameter_home :
    (invoke [{ homedParameter with
      code := [.ldarga 0, .ldarg 1, .call singleConstructor {}, .ldarga 0, .call getLength {},
        .ret] }] 16 0 [view 2, element] memory).map Prod.snd = .ok [.scalar (.i32 1)] := rfl
#print axioms constructor_through_parameter_home



/-- A store of a span through a home faults: only `initobj` and a constructor write the slot. -/
theorem stobj_through_home_faults :
    (invoke [{ savedLength with
      code := [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .stobj intSpan, .ldc_i4 0, .ret] }] 16 0
      [view 1, view 2] memory).map Prod.snd =
      .error ⟨0, 4, .unsupported "Object transfer shape"⟩ := rfl
#print axioms stobj_through_home_faults

/-- `passesHome` with a dead local before its span local, as a local deletion map relates it. -/
private def passesHomeShifted : Method := {
  code := [.ldarg 0, .stloc 1, .ldloca 1, .ldarg 1, .stloc 1, .call (Tests.callee 1) {}, .ret]
  locals := [.nullRef, .nullRef], localKinds := [.span 4 true, .span 4 true]
  returnsValue := true, links := [(5, .direct 1)] }

/-- The deletion map that skips target slot 0 sends the home of source slot 0 to target slot 1,
    and the shifted program returns what `passesHome` returns through the linked call and the
    model call. -/
theorem shifted_home_renamed (mapping : AllocationRenaming) :
    (LocalIndexMap.skip (.keep .nil)).value mapping (.spanHome 0) = .spanHome 1 ∧
    (invoke [passesHomeShifted, reader] 32 0 [view 1, view 2] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] ∧
    (invoke [passesHomeShifted, reader] 32 0 [view 2, view 1] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] := ⟨rfl, rfl, rfl⟩
#print axioms shifted_home_renamed

/-- A method with one span parameter and one span local, in the raw form admission checks. -/
private def spanRaw : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .atom runtimeScope "System.Int32", parameters := [intSpan], locals := [intSpan],
  initLocals := true, maxStack := 2, genericParameters := [], code := [] }

/-- A managed call to a void method taking one argument of type `parameter`. -/
private def takes (parameter : TypeExpr) : RawInstruction := ⟨0, 40, .call {
  declared := { convention := 0, parameters := [parameter] },
  method := {
    owner := .atom "Fixture" "Helpers", name := name!"Use", hasThis := false,
    genericArity := 0, returnType := .void, parameters := [parameter] },
  name := "Use", target := .managed 2, typeArguments := [], parameterCount := 1,
  returnsValue := false }⟩

/-- `Span<int>.CopyTo(Span<int>)`, a framework call whose receiver is an address and whose
    destination is a span taken by value. -/
private def copyTo : RawInstruction := ⟨0, 40, .call {
  declared := { convention := 0x20, parameters := [intSpan] },
  method := {
    owner := intSpan, name := name!"CopyTo", hasThis := true, genericArity := 0,
    returnType := .void, parameters := [intSpan] },
  name := "CopyTo", target := .external (runtimeScope ++
    "::System.Void System.Span`1<System.Int32>::CopyTo(System.Span`1<!0>)"),
  typeArguments := [], parameterCount := 1, returnsValue := false }⟩

/-- `ldloca` and `ldarga` of a span leave an address, which admission accepts at a by-reference
    span parameter and refuses at a by-value one or as a value stored to a span local. A
    framework call is checked the same way: `CopyTo` takes its receiver by address and refuses
    an address as its by-value destination. -/
theorem home_refused_where_span_is_by_value :
    scalarTransfer spanRaw ⟨0, 18, .local 0⟩ [] = some [.reference] ∧
    scalarTransfer spanRaw ⟨0, 15, .argument 0⟩ [] = some [.reference] ∧
    scalarTransfer spanRaw (takes intSpan) [.reference] = none ∧
    scalarTransfer spanRaw ⟨0, 10, .none⟩ [.reference] = none ∧
    scalarTransfer spanRaw (takes intSpan) [scalarType intSpan] = some [] ∧
    scalarTransfer spanRaw (takes (.byref intSpan)) [.reference] = some [] ∧
    scalarTransfer spanRaw copyTo [scalarType intSpan, .reference] = some [] ∧
    scalarTransfer spanRaw copyTo [.reference, .reference] = none := by decide +kernel
#print axioms home_refused_where_span_is_by_value

/-- An address followed by `call Use(Span<int>)` and `ret`: the IL that would hand a home to a
    by-value span parameter. -/
private def byValueRaw (address : RawInstruction) : RawMethod :=
  { spanRaw with returnType := .void, code := [address, takes intSpan, ⟨0, 42, .none⟩] }

/-- No scalar certificate admits `byValueRaw address` when `address` pushes an address: pc 0
    must hand pc 1 exactly that address, and the call refuses it at the by-value parameter. -/
private theorem byValue_refused {address : RawInstruction}
    (roles : foldRoles (byValueRaw address).code =
      [none, none, none])
    (pushes : scalarTransfer (byValueRaw address) address [] = some [.reference])
    (calls : scalarTransfer (byValueRaw address) (takes intSpan) [.reference] = none)
    (successor : ∀ stack, featureSuccessors none 0 address stack = some [1])
    (notStore : ∀ stack emitted,
      scalarStoreFault (byValueRaw address) address stack emitted = false)
    (callNotStore : ∀ stack emitted,
      scalarStoreFault (byValueRaw address) (takes intSpan) stack emitted = false)
    (features : FeatureCertificate) (certificate : ScalarCertificate)
    (code : List Instruction) (decoded : Bool) :
    ¬ ScalarFlowValid (byValueRaw address) features certificate code decoded := by
  intro valid
  have lengths := valid
  obtain ⟨featureLength, scalarLength, codeLength, entry, _⟩ := lengths
  simp only [byValueRaw, List.length_cons, List.length_nil] at featureLength codeLength
  have siteAt (pc : Nat) (bound : pc < 3) :
      ∃ feature emitted, features[pc]? = some feature ∧ code[pc]? = some emitted :=
    ⟨features[pc]'(by omega), code[pc]'(by omega), List.getElem?_eq_getElem _,
      List.getElem?_eq_getElem _⟩
  obtain ⟨feature0, emitted0, featureAt0, emittedAt0⟩ := siteAt 0 (by omega)
  obtain ⟨feature1, emitted1, featureAt1, emittedAt1⟩ := siteAt 1 (by omega)
  obtain ⟨state0, _, first⟩ := valid.transfer_at rfl (by rw [roles]; rfl) featureAt0 entry
    emittedAt0
  rw [notStore] at first
  obtain ⟨after, successors, transferred, successorsAt, reached⟩ :=
    first.resolve_left Bool.false_ne_true
  rw [pushes, Option.some.injEq] at transferred
  rw [successor, Option.some.injEq] at successorsAt
  subst transferred successorsAt
  obtain ⟨_, _, second⟩ := valid.transfer_at rfl (by rw [roles]; rfl) featureAt1
    (reached 1 (List.mem_singleton_self 1)) emittedAt1
  rw [callNotStore] at second
  obtain ⟨_, _, refused, _⟩ := second.resolve_left Bool.false_ne_true
  rw [calls] at refused
  cases refused
#print axioms byValue_refused

/-- Admission refuses `ldloca` or `ldarga` of a span followed by a call that takes the span by
    value, for every certificate, so a linked call never receives a home at such a position. -/
theorem home_at_by_value_parameter_refused (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Instruction) (decoded : Bool) :
    ¬ ScalarFlowValid (byValueRaw ⟨0, 18, .local 0⟩) features certificate code decoded ∧
    ¬ ScalarFlowValid (byValueRaw ⟨0, 15, .argument 0⟩) features certificate code decoded :=
  ⟨byValue_refused (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) features certificate code decoded,
    byValue_refused (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) features certificate code decoded⟩
#print axioms home_at_by_value_parameter_refused

end Tests.SpanHomes
