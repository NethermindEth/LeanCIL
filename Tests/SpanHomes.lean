import CIL.Extraction.Scalars
import CIL.Safety.ExecutionInvariants
import CIL.Safety.ValueRenaming
import CIL.Safety.SpanHomeRenaming
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

/-- The deletion map that skips target slot 0 and keeps the span local. -/
private def shift : LocalIndexMap := .skip (.keep .nil)

/-- The frame of `passesHome` once its span local holds the two-element view. -/
private def sourceFrame : Frame :=
  { activation := 0, locals := [.span 4 true (some ⟨.address ⟨0, 0⟩, 2, 4, true⟩)], owned := [] }

/-- The frame of `passesHomeShifted` at the same point, with the dead slot first. -/
private def targetFrame : Frame :=
  { sourceFrame with locals := .span 4 true none :: sourceFrame.locals }

/-- `shift` relates the two frames under the identity allocation map of `memory`. -/
private theorem shiftedFrames :
    Frame.Renamed shift (.identity memory.nextIdentity) Eq sourceFrame targetFrame :=
  ⟨rfl, .skip _ (.keep ⟨fun _ held => by cases held; exact Nat.zero_lt_one, rfl⟩ .nil), .nil, rfl⟩

/-- `Frame.Renamed.spanView` reads the home of source slot 0 and its relocation, the home of
    target slot 1, as one renamed view; both reads give the view the slot holds, and the shifted
    program returns what `passesHome` returns through the linked call and the model call. -/
theorem shifted_home_renamed :
    ResultRenamed (.identity memory.nextIdentity)
      (fun left right => right = (AllocationRenaming.identity memory.nextIdentity).value left ∧
        left.Below (AllocationRenaming.identity memory.nextIdentity).sourceLimit)
      (spanView sourceFrame memory (.spanHome 0))
      (spanView targetFrame memory (shift.value (.identity memory.nextIdentity) (.spanHome 0))) ∧
    shift.value (.identity memory.nextIdentity) (.spanHome 0) = .spanHome 1 ∧
    spanView targetFrame memory (.spanHome 1) = .ok (view 2) ∧
    (invoke [passesHomeShifted, reader] 32 0 [view 1, view 2] memory).map Prod.snd =
      .ok [.scalar (.i32 2)] ∧
    (invoke [passesHomeShifted, reader] 32 0 [view 2, view 1] memory).map Prod.snd =
      .ok [.scalar (.i32 1)] :=
  ⟨shiftedFrames.spanView (Memory.Renamed.refl memory Eq fun _ member => nomatch member)
      (.spanHome 0) trivial, rfl, rfl, rfl, rfl⟩
#print axioms shifted_home_renamed

/-- `System.ReadOnlySpan<byte>`, whose pointer constructor views bytes. -/
private def byteSpan : TypeExpr :=
  .apply (.constructor runtimeScope "System.ReadOnlySpan`1") (.atom runtimeScope "System.Byte")

/-- `ReadOnlySpan<byte>(void*, int)`. -/
private def bytePointerConstructor : MethodRef := {
  owner := byteSpan, name := name!".ctor", hasThis := true, genericArity := 0,
  returnType := .void, parameters := [.pointer .void, .atom runtimeScope "System.Int32"] }

/-- `ReadOnlySpan<byte>.get_Length`. -/
private def byteLength : MethodRef := {
  owner := byteSpan, name := name!"get_Length", hasThis := true, genericArity := 0,
  returnType := .atom runtimeScope "System.Int32", parameters := [] }

/-- A method with one read-only byte span local. -/
private def byteLocal (code : List Instruction) : Method := {
  code, locals := [.nullRef], localKinds := [.span 1 false], returnsValue := true }

/-- In place, `ReadOnlySpan<byte>(void*, int)` views the bytes the pointer names, in the caller's
    storage or in `localloc` storage, and the length reads 3 or 8. `newobj` of the same
    constructor views only extracted static data, so over caller storage it faults. -/
theorem byte_pointer_constructor_in_place :
    (invoke [byteLocal [.ldloca 0, .ldarg 0, .ldc_i4 3, .call bytePointerConstructor {},
        .ldloca 0, .call byteLength {}, .ret]] 16 0 [element] memory).map Prod.snd =
      .ok [.scalar (.i32 3)] ∧
    (invoke [{ byteLocal [.ldc_i4 8, .localloc, .stloc 1, .ldloca 0, .ldloc 1, .ldc_i4 8,
        .call bytePointerConstructor {}, .ldloca 0, .call byteLength {}, .ret] with
        locals := [.nullRef, .nullRef], localKinds := [.span 1 false, .reference] }] 16 0 []
        { memory with stackLimit := 64 }).map Prod.snd = .ok [.scalar (.i32 8)] ∧
    (invoke [byteLocal [.ldarg 0, .ldc_i4 3, .newobj bytePointerConstructor, .stloc 0,
        .ldloca 0, .call byteLength {}, .ret]] 16 0 [element] memory).map Prod.snd =
      .error ⟨0, 2, .unsupported "Span pointer constructor outside extracted static data"⟩ :=
  ⟨rfl, rfl, rfl⟩
#print axioms byte_pointer_constructor_in_place

/-- Whether a step succeeds. -/
private def succeeds : ExecutionResult FrameAction → Bool
  | .ok _ => true
  | .error _ => false

/-- The step itself refuses a constructor whose spans differ from the home's slot in width or
    access, whatever admission decided: a byte or writable view into a read-only int32 slot. -/
theorem in_place_constructor_matches_slot :
    let frame : Frame := { activation := 0, locals := [.span 4 false none], owned := [] }
    let arguments := [.scalar (.i32 4), element, .spanHome 0]
    let mismatch : ExecutionResult FrameAction :=
      .error (.unsupported "Span constructor does not build the span of its home")
    spanInPlaceCall (.reference 1 false) 0 frame arguments memory = mismatch ∧
    spanInPlaceCall (.reference 4 true) 0 frame arguments memory = mismatch ∧
    succeeds (spanInPlaceCall (.reference 4 false) 0 frame arguments memory) := ⟨rfl, rfl, rfl⟩
#print axioms in_place_constructor_matches_slot

/-- `System.ReadOnlySpan<int>`. -/
private def readOnlyIntSpan : TypeExpr :=
  .apply (.constructor runtimeScope "System.ReadOnlySpan`1") (.atom runtimeScope "System.Int32")

/-- `ReadOnlySpan<int>(in int)`, the read-only single-element constructor. -/
private def readOnlySingleConstructor : MethodRef := {
  owner := readOnlyIntSpan, name := name!".ctor", hasThis := true, genericArity := 0,
  returnType := .void, parameters := [.byref (.atom runtimeScope "System.Int32")] }

/-- `ReadOnlySpan<int>.get_Length`. -/
private def readOnlyLength : MethodRef := { getLength with owner := readOnlyIntSpan }

/-- A read-only int32 view of two elements at the start of allocation 0. -/
private def readOnlyView : Safety.Value := .bufferSpan ⟨.address ⟨0, 0⟩, 2, 4, false⟩

/-- An `in` or `ref readonly` span parameter arrives as the view, which names no slot, so a
    constructor called on it faults. On the home of a homed read-only span parameter the
    writable constructor faults at the step and the read-only one replaces the view. -/
theorem constructor_on_read_only_parameter :
    (invoke [{ reader with
      code := [.ldarg 0, .ldarg 1, .call singleConstructor {}, .ldc_i4 0, .ret] }] 16 0
      [view 2, element] memory).map Prod.snd = .error ⟨0, 2, .invalidState⟩ ∧
    (invoke [{ homedParameter with
      code := [.ldarga 0, .ldarg 1, .call singleConstructor {}, .ldc_i4 0, .ret],
      parameterHomes := [(0, .span 4 false)] }] 16 0
        [readOnlyView, element] memory).map Prod.snd =
      .error ⟨0, 2, .unsupported "Span constructor does not build the span of its home"⟩ ∧
    (invoke [{ homedParameter with
      code := [.ldarga 0, .ldarg 1, .call readOnlySingleConstructor {}, .ldarga 0,
        .call readOnlyLength {}, .ret],
      parameterHomes := [(0, .span 4 false)] }] 16 0
        [readOnlyView, element] memory).map Prod.snd = .ok [.scalar (.i32 1)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms constructor_on_read_only_parameter

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

/-- An object type whose members take a span by value. -/
private def holder : TypeExpr := .object "Fixture" "Fixture.Holder"

/-- A managed instance call under `opcode` to `member` of `holder`, taking one `parameter`. -/
private def instanceTakes (opcode : Nat) (member : MetadataName) (name : String)
    (parameter : TypeExpr) : RawInstruction := ⟨0, opcode, .call {
  declared := { convention := 0x20, parameters := [parameter] },
  method := {
    owner := holder, name := member, hasThis := true, genericArity := 0,
    returnType := .void, parameters := [parameter] },
  name, target := .managed 2, typeArguments := [], parameterCount := 1,
  returnsValue := false }⟩

/-- `ldloca` and `ldarga` of a span leave an address, which admission accepts at a by-reference
    span parameter and refuses at a by-value one or as a value stored to a span local. A
    framework call is checked the same way: `CopyTo` takes its receiver by address and refuses
    an address as its by-value destination. `callvirt` and `newobj` refuse an address at a
    by-value span parameter as `call` does. -/
theorem home_refused_where_span_is_by_value :
    scalarTransfer spanRaw ⟨0, 18, .local 0⟩ [] = some [.reference] ∧
    scalarTransfer spanRaw ⟨0, 15, .argument 0⟩ [] = some [.reference] ∧
    scalarTransfer spanRaw (takes intSpan) [.reference] = none ∧
    scalarTransfer spanRaw ⟨0, 10, .none⟩ [.reference] = none ∧
    scalarTransfer spanRaw (takes intSpan) [scalarType intSpan] = some [] ∧
    scalarTransfer spanRaw (takes (.byref intSpan)) [.reference] = some [] ∧
    scalarTransfer spanRaw copyTo [scalarType intSpan, .reference] = some [] ∧
    scalarTransfer spanRaw copyTo [.reference, .reference] = none ∧
    scalarTransfer spanRaw (instanceTakes 111 name!"Use" "Use" intSpan) [scalarType intSpan,
      scalarType holder] = some [] ∧
    scalarTransfer spanRaw (instanceTakes 111 name!"Use" "Use" intSpan) [.reference,
      scalarType holder] = none ∧
    scalarTransfer spanRaw (instanceTakes 115 name!".ctor" ".ctor" intSpan) [scalarType intSpan] =
      some [scalarType holder] ∧
    scalarTransfer spanRaw (instanceTakes 115 name!".ctor" ".ctor" intSpan) [.reference] =
      none := by
  decide +kernel
#print axioms home_refused_where_span_is_by_value

/-- An address followed by `call` and `ret`: the IL that would hand a home to a by-value span
    parameter of `call`. -/
private def byValueRaw (address call : RawInstruction) : RawMethod :=
  { spanRaw with returnType := .void, code := [address, call, ⟨0, 42, .none⟩] }

/-- No scalar certificate admits `byValueRaw address call` when `address` pushes an address: pc 0
    must hand pc 1 exactly that address, and `call` refuses it at the by-value parameter. -/
private theorem byValue_refused {address call : RawInstruction}
    (roles : foldRoles (byValueRaw address call).code =
      [none, none, none])
    (pushes : scalarTransfer (byValueRaw address call) address [] = some [.reference])
    (calls : scalarTransfer (byValueRaw address call) call [.reference] = none)
    (successor : ∀ stack, featureSuccessors none 0 address stack = some [1])
    (notStore : ∀ stack emitted,
      scalarStoreFault (byValueRaw address call) address stack emitted = false)
    (callNotStore : ∀ stack emitted,
      scalarStoreFault (byValueRaw address call) call stack emitted = false)
    (features : FeatureCertificate) (certificate : ScalarCertificate)
    (code : List Instruction) (decoded : Bool) :
    ¬ ScalarFlowValid (byValueRaw address call) features certificate code decoded := by
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

/-- Admission refuses `ldloca` or `ldarga` of a span followed by a `call`, or `ldloca` followed by
    a `newobj`, that takes the span by value, for every certificate, so a linked call or
    construction never receives a home at such a position. -/
theorem home_at_by_value_parameter_refused (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Instruction) (decoded : Bool) :
    ¬ ScalarFlowValid (byValueRaw ⟨0, 18, .local 0⟩ (takes intSpan)) features certificate code
      decoded ∧
    ¬ ScalarFlowValid (byValueRaw ⟨0, 15, .argument 0⟩ (takes intSpan)) features certificate
      code decoded ∧
    ¬ ScalarFlowValid
      (byValueRaw ⟨0, 18, .local 0⟩ (instanceTakes 115 name!".ctor" ".ctor" intSpan))
      features certificate code decoded :=
  ⟨byValue_refused (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) features certificate code decoded,
    byValue_refused (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) features certificate code decoded,
    byValue_refused (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) features certificate code decoded⟩
#print axioms home_at_by_value_parameter_refused

end Tests.SpanHomes
