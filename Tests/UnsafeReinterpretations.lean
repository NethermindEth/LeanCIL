import CIL.Extraction.RuntimeModels
import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import Tests.Support.RawDecoding

/-! # Runtime model admission and execution of Unsafe reinterpretations

The fixtures exercise reference formation and each representation that BitCast can move.
-/

namespace Tests.UnsafeReinterpretations
open CIL CIL.Extraction CIL.Safety

/-- The primitive byte type used by the scalar casts. -/
private def byteType := TypeExpr.primitive .byte

/-- The Boolean result of the scalar BitCast overload. -/
private def boolean := TypeExpr.primitive .boolean

/-- The example packet occupies layout slot zero. -/
private def packet := TypeExpr.aggregate "Test::Packet" 0

/-- The packet has one unsigned 64-bit field per word. -/
private def environment (words : Nat) : LayoutEnvironment :=
  let layout : RawLayout :=
    { identity := "Test::Packet", explicit := false, packing := 0, declaredSize := 0,
      fields := List.replicate words { type := .unsigned64 } }
  let raw := [layout]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

/-- An intrinsic vector over the given runtime element type. -/
private def vector (width : Nat) (element := PrimitiveType.byte) : TypeExpr :=
  .apply (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{width}`1")
    (.primitive element)

/-- A closed static call together with the declaration and external identity of its member. -/
private def site (name : MetadataName) (text signature : String) (args : List TypeExpr)
    (parameters : List TypeExpr) (result : TypeExpr) (declared : OpenSignature) : CallSite :=
  let method : MethodRef :=
    { owner := unsafeOwner, name, hasThis := false, genericArity := args.length,
      parameters, returnType := result, methodArguments := args }
  { method, name := text, declared, target := .external (runtimeScope ++ "::" ++ signature),
    typeArguments := args, parameterCount := parameters.length, returnsValue := true }

/-- The open byref-to-byref cast closed over source and target. -/
private def asSite (source target : TypeExpr) :=
  site name!"As" "As" "!!1& System.Runtime.CompilerServices.Unsafe::As(!!0&)"
    [source, target] [.byref source] (.byref target)
    { convention := 16, parameters := [.byref (.parameter 0)],
      returnType := .byref (.parameter 1) }

/-- The byref and void-pointer overloads of AsRef. -/
private def asRefSite (element : TypeExpr) (pointer : Bool) :=
  let parameter := fun arg => if pointer then TypeExpr.pointer .void else .byref arg
  let operand := if pointer then "System.Void*" else "!!0&"
  site name!"AsRef" "AsRef" s!"!!0& System.Runtime.CompilerServices.Unsafe::AsRef({operand})"
    [element] [parameter element] (.byref element)
    (unsafeDeclaration (fun arg => [parameter arg]) TypeExpr.byref)

/-- The generic null reference and its Boolean observer. -/
private def nullSite (element : TypeExpr) (test : Bool) :=
  if test then
    site name!"IsNullRef" "IsNullRef" "System.Boolean System.Runtime.CompilerServices.Unsafe::\
      IsNullRef(!!0&)" [element] [.byref element] boolean
      (unsafeDeclaration (fun arg => [.byref arg]) (fun _ => boolean))
  else
    site name!"NullRef" "NullRef" "!!0& System.Runtime.CompilerServices.Unsafe::NullRef()"
      [element] [] (.byref element) (unsafeDeclaration (fun _ => []) TypeExpr.byref)

/-- The closed value cast from source to target. -/
private def cast (source target : TypeExpr) :=
  site name!"BitCast" "BitCast" "!!1 System.Runtime.CompilerServices.Unsafe::BitCast(!!0)"
    [source, target] [source] target
    { convention := 16, parameters := [.parameter 0], returnType := .parameter 1 }

/-- A span over an element; As refuses it as either type argument, as it refuses an array or
    class. -/
private def span (element : TypeExpr) : TypeExpr :=
  .apply (.constructor runtimeScope "System.Span`1") element

/-- The runtime model selected for a call with the supplied layouts. -/
private def model (call : CallSite) (env := environment 2) :=
  runtimeModel env .call call.method

/-- A one-instruction method whose call site is live. -/
private def caller (call : CallSite) : RawMethod :=
  { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := true, maxStack := 1, genericParameters := [], code := [⟨0, 40, .call call⟩] }

/-- The runtime-site check applies to a live call. -/
private def accepts (call : CallSite) (emitted : Instruction) : Bool :=
  runtimeCatalog.siteAgrees (environment 2) .scalar ⟨0, 40, .call call⟩ emitted none true

/-- One live call as the public raw-method decoder emits it. -/
private def decoded (call : CallSite) (env := environment 2) :=
  (decodeRaw .scalar env [] [true] (caller call) []).map Method.code

/-- A single mutation of a resolving operand leaves precisely its opcode's hole. -/
private def refuses (control changed : CallSite) : Bool :=
  decide (decoded control = .ok [.call control.method {}]) &&
    decide (decoded changed = liveHoleAt 0 40)

/-- Every pair of snapshot classes and the scalar overload, in a 16-byte layout. -/
private def values : List (CallSite × MemoryOp) :=
  [(cast byteType boolean, .bitcastByteBool),
   (cast packet packet, .bitcastValue (.aggregate 16) (.aggregate 16)),
   (cast (vector 128) (vector 128), .bitcastValue .vector128 .vector128),
   (cast packet (vector 128), .bitcastValue (.aggregate 16) .vector128),
   (cast (vector 128) packet, .bitcastValue .vector128 (.aggregate 16))]

/-- Scalar, vector and struct references, one for each storage As and AsRef admit, and the null
    helpers at every storage they admit. -/
private def references : List (CallSite × MemoryOp) :=
  [byteType, vector 128, packet].map (fun element => (asSite element byteType, .asRef)) ++
  [false, true].flatMap (fun pointer => [byteType, vector 128, packet].map
    (fun element => (asRefSite element pointer, .asRef))) ++
  [false, true].flatMap (fun test => [byteType, vector 256, packet, span byteType,
    .array byteType, .object "Test" "Class"].map
    (fun element => (nullSite element test, if test then .isNullRef else .nullRef)))

/-- Every admitted call runs its expected operation and keeps its operand at the live site. -/
theorem resolved : (references ++ values).all (fun (call, operation) =>
    model call == some (.memory operation) && accepts call (.call call.method {}) &&
      !accepts call (.call call.method { tail := true }) && !accepts call .nop) := by decide +kernel
#print axioms resolved

/-- A span, array or class on either side of As has no field or vector storage, so the live site
    decodes to the call hole, and a span over a type variable resolves no model. -/
theorem unsizedRefused : [span byteType, .apply (.constructor runtimeScope "System.ReadOnlySpan`1")
    byteType, .array byteType, .object "Test" "Class"].all (fun arg =>
      refuses (asSite byteType byteType) (asSite byteType arg) &&
        refuses (asSite byteType byteType) (asSite arg byteType)) &&
    (model (asSite byteType (span (.parameter 0)))).isNone := by decide +kernel
#print axioms unsizedRefused

/-- Both layouts compute successfully; BitCast reads their different snapshot sizes. -/
theorem checkedSizes : LayoutsValid (environment 2).rawLayouts (environment 2).layouts ∧
    LayoutsValid (environment 4).rawLayouts (environment 4).layouts ∧
    model (cast packet packet) (environment 4) =
      some (.memory (.bitcastValue (.aggregate 32) (.aggregate 32))) := by decide +kernel
#print axioms checkedSizes

/-- A root byref, pointer or variable excludes an As argument on either side. -/
theorem asExclusions : [TypeExpr.byref byteType, .pointer byteType, .parameter 0,
    .ownerParameter 0].all (fun arg => (model (asSite arg byteType)).isNone &&
      (model (asSite byteType arg)).isNone &&
      !accepts (asSite arg byteType) (.call (asSite arg byteType).method) &&
      !accepts (asSite byteType arg) (.call (asSite byteType arg).method)) := by decide +kernel
#print axioms asExclusions

/-- BitCast requires checked equal-width snapshots in both directions, or Byte to Boolean. -/
theorem bitCastExclusions :
    [vector 256, .aggregate "Other" 0, span byteType, .parameter 0, .pointer byteType,
     .object "Test" "Class", .array byteType, byteType].all (fun arg =>
      (model (cast arg packet)).isNone && (model (cast packet arg)).isNone) &&
    (model (cast boolean byteType)).isNone &&
    [(PrimitiveType.single, 2, 128), (.double, 4, 256),
     (.double, 2, 128), (.single, 4, 256)].all (fun (element, words, width) =>
      let arg := vector width element
      (model (cast arg packet) (environment words)).isNone &&
        (model (cast packet arg) (environment words)).isNone) := by decide +kernel
#print axioms bitCastExclusions

/-- The closed AsRef parameter picks both the open declaration and its exact external target. -/
theorem asRefStorage : [false, true].all (fun pointer =>
    let control := asRefSite byteType pointer
    let other := asRefSite byteType (!pointer)
    refuses control { control with declared := other.declared } &&
    refuses control { control with target := other.target } &&
    refuses control { control with declared := other.declared, target := other.target } &&
    [span byteType, TypeExpr.array byteType, .object "Test" "Class", .byref byteType,
     .aggregate "Other" 0].all (fun arg => refuses control (asRefSite arg pointer))) := by
  decide +kernel
#print axioms asRefStorage

/-- The void-pointer overload consumes a reference in the scalar flow certificate. -/
theorem asRefPointerStack :
    let call := asRefSite byteType true
    let transfer := scalarTransfer (caller call) ⟨0, 40, .call call⟩
    transfer [.reference] = some [.reference] ∧ transfer [.other] = none := by decide +kernel
#print axioms asRefPointerStack

/-- Missing computed size preserves a field's raw storage identity for all four overloads. -/
theorem indexedStorage :
    let env := { environment 2 with layouts := #[] }
    [asRefSite packet false, asRefSite packet true,
      nullSite packet false, nullSite packet true].all
      (fun call => decide (decoded call env = .ok [.call call.method {}])) := by decide +kernel
#print axioms indexedStorage

/-- Recognized reference storage and unsupported elements both refuse the two null helpers. -/
theorem nullStorage : [false, true].all (fun test =>
    [TypeExpr.byref byteType, .pointer byteType, .void, .aggregate "Other" 0].all
      (fun arg => refuses (nullSite byteType test) (nullSite arg test))) := by decide +kernel
#print axioms nullStorage

/-- Each closed type refusal differs from a kept reference or snapshot operand in one argument. -/
theorem excludedOperands :
    [TypeExpr.byref byteType, .pointer byteType].all (fun arg =>
      refuses (asSite byteType byteType) (asSite byteType arg) &&
      refuses (asSite byteType byteType) (asSite arg byteType)) &&
    [vector 256, vector 128 .single, vector 128 .double,
      .aggregate "Other" 0, span byteType, .pointer byteType, .object "Test" "Class",
      .array byteType, byteType].all (fun arg =>
      refuses (cast (vector 128) packet) (cast arg packet) &&
      refuses (cast packet (vector 128)) (cast packet arg)) &&
    refuses (cast byteType boolean) (cast byteType byteType) := by decide +kernel
#print axioms excludedOperands

/-- Closed operands for mutations that run through the method decoder. -/
private def controls := [(asSite byteType packet, MemoryOp.asRef), (cast byteType boolean,
  MemoryOp.bitcastByteBool), (cast (vector 128) packet, .bitcastValue .vector128 (.aggregate 16)),
  (asRefSite packet false, .asRef), (asRefSite packet true, .asRef),
  (nullSite byteType false, .nullRef), (nullSite byteType true, .isNullRef)]

/-- The owner, receiver, generic arity and closed types identify each overload. -/
theorem exactReference : controls.all (fun (call, _) =>
    let method := call.method
    [ { method with owner := .apply unsafeOwner byteType },
      { method with owner := .atom "Other" "System.Runtime.CompilerServices.Unsafe" .classType },
      { method with hasThis := true }, { method with genericArity := method.genericArity + 1 },
      { method with parameters := method.parameters ++ [byteType] },
      { method with returnType := .void } ].all
      (fun other => (runtimeModel (environment 2) .call other).isNone &&
        refuses call { call with method := other })) &&
    refuses (nullSite byteType true) { (nullSite byteType true) with
      method.returnType := .atom "Other" "System.Boolean" .valueType } &&
    (runtimeModel {} .call { (asSite byteType packet).method with
      genericArity := 1, methodArguments := [byteType], parameters := [.object runtimeScope
        "System.Object"], returnType := byteType }).isNone := by decide +kernel
#print axioms exactReference

/-- A forged open return type or convention rejects both the original call and a tail-prefixed call. -/
theorem exactDeclaration : controls.all (fun (call, _) =>
    let altered := { call with declared.returnType := .void }
    refuses call altered &&
      refuses call { call with target := .external "Other" } &&
      refuses call { call with parameterCount := call.parameterCount + 1 } &&
      refuses call { call with returnsValue := false } &&
      refuses call { call with typeArguments := [] } &&
      refuses call { call with name := "Other" } &&
      refuses call { call with declared.parameters := [.ownerParameter 0] } &&
      !accepts altered (.call call.method {}) &&
      !accepts altered (.call call.method { tail := true }) &&
      [0x00, 0x11, 0x30, 0x50, 0x70].all (fun convention =>
        refuses call { call with declared.convention := convention })) := by
  decide +kernel
#print axioms exactDeclaration

/-- A failed layout or unknown member has only a hole, which cannot certify a live site. -/
theorem unadmitted :
    let control := cast (vector 128) packet
    let unknown := { control with name := "Unknown", method.name := name!"Unknown" }
    [(control, cast (vector 256) packet), (asSite byteType byteType, asSite (.pointer byteType)
      byteType), (control, unknown)].all (fun (original, call) =>
      refuses original call &&
        runtimeCatalog.siteAgrees (environment 2) .scalar ⟨0, 40, .call call⟩ (.unadmitted 40) &&
        !accepts call (.unadmitted 40) && !accepts call .nop) := by decide +kernel
#print axioms unadmitted

/-- On every stack and memory these calls step according to their bound runtime model. -/
theorem callSteps (call : CallSite) (operation : MemoryOp)
    (listed : (call, operation) ∈ references ++ values) (pc : Nat)
    (args stack : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    let body : Method :=
      { code := [], locals := [], returnsValue := true, environment := environment 2 }
    step body (.call call.method {}) pc args frame stack memory =
      modelStep (some (.memory operation)) body pc frame stack memory := by
  have found : (references ++ values).all
      (fun pair => model pair.1 == some (.memory pair.2)) := by decide +kernel
  have modelAt := List.all_eq_true.mp found _ listed
  dsimp only
  apply step_call_model <;> first | rfl | exact eq_of_beq modelAt

#print axioms callSteps

/-- Eight readable and writable caller bytes, all zero. -/
private def callerMemory : CIL.Safety.Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- Loads a span through its by-reference argument and returns it. -/
private def spanLoader : Method :=
  { code := [.ldarg 0, .ldobj (span byteType), .ret], locals := [], returnsValue := true,
    environment := environment 2 }

/-- The span load returns a view in place. An address, such as an As cast to a span type forms,
    is invalid there, and a null reference, such as NullRef forms, faults as a null dereference. -/
theorem spanLoads :
    let view : SpanView := ⟨.address ⟨0, 0⟩, 8, 1, true⟩
    let run := fun argument => (invoke [spanLoader] 4 0 [argument] callerMemory).map Prod.snd
    run (.bufferSpan view) = .ok [.bufferSpan view] ∧
      run (.reference (.address ⟨0, 0⟩)) = .error ⟨0, 1, .invalidState⟩ ∧
      run (.readOnlyReference (.address ⟨0, 0⟩)) = .error ⟨0, 1, .invalidState⟩ ∧
      run (.reference .null) = .error ⟨0, 1, .memory .nullDereference .null 0⟩ ∧
      run (.readOnlyReference .null) = .error ⟨0, 1, .memory .nullDereference .null 0⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms spanLoads

/-- Whether a step or memory operation stops with a fault rather than returning. -/
private def faults {α : Type} : ExecutionResult α → Bool
  | .error _ => true
  | .ok _ => false

/-- The receivers and operands NullRef and a plain address give a span or object type. -/
private def nullOrPlain : List CIL.Safety.Value :=
  [.reference .null, .readOnlyReference .null, .reference (.address ⟨0, 0⟩)]

/-- Every span member that takes its receiver by reference faults on a null or plain reference,
    so NullRef of a span type never yields a span value. -/
theorem spanReceiversFault : [(MemoryOp.spanLength, ([] : List CIL.Safety.Value)),
    (.spanItem 1, [.scalar (.i32 0)]), (.spanSlice false, [.scalar (.i32 0)]),
    (.spanSlice true, [.scalar (.i32 0), .scalar (.i32 0)]), (.observeView .spanEmpty, []),
    (.observeView .spanPinnable, []), (.spanReadOnly, []), (.spanReference, []),
    (.spanCopy 1 false, [.bufferSpan ⟨.address ⟨0, 0⟩, 8, 1, true⟩]),
    (.spanCopy 1 true, [.bufferSpan ⟨.address ⟨0, 0⟩, 8, 1, true⟩]),
    (.spanFill 1 false, [.scalar (.i32 0)]), (.spanFill 1 true, [])].all (fun (operation, above) =>
      nullOrPlain.all fun receiver =>
        faults (memoryInstruction operation (above ++ [receiver]) callerMemory)) := by
  decide +kernel
#print axioms spanReceiversFault

/-- Object instructions fault on a null or plain reference to span, array or class storage, and
    a native-integer load, which reads a method pointer, faults on a null reference, so a reference
    NullRef forms for them is never read as a value. -/
theorem objectOperandsFault :
    let body : Method :=
      { code := [], locals := [], returnsValue := true, environment := environment 2 }
    let frame : CIL.Safety.Frame := { activation := 0, locals := [], owned := [] }
    [span byteType, .array byteType, .object "Test" "Class"].all (fun type =>
      nullOrPlain.all fun target =>
        [(Instruction.ldobj type, [target]), (.stobj type, [.scalar (.i32 0), target]),
         (.cpobj type, [target, target]), (.initobj type, [target])].all fun (op, stack) =>
          faults (step body op 0 [] frame stack callerMemory)) ∧
    [CIL.Safety.Value.reference .null, .readOnlyReference .null].all (fun target =>
      faults (instruction (.ldind .i) [target] callerMemory)) := by
  decide +kernel
#print axioms objectOperandsFault

end Tests.UnsafeReinterpretations
