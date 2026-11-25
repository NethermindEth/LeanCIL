import Tests.Support.EnumIdentity
import CIL.Extraction.Features
import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import Tests.Support.RawDecoding

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.SpanEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .primitive .int32
private def span (scope : String) (element : PrimitiveType) : TypeExpr :=
  .apply (.constructor scope "System.ReadOnlySpan`1") (.primitive element)
private def words := span runtime .uint32

/-- The readonly indexer at the local receiver. -/
private def getItem : CallSite := {
  declared := {
    convention := 0x20, parameters := [intType],
    returnType := .modified true runtime "System.Runtime.InteropServices.InAttribute"
      (.byref (.ownerParameter 0)) },
  method := {
    owner := words, name := name!"get_Item", hasThis := true, genericArity := 0,
    returnType := .atom runtime "!0& modreq(System.Runtime.InteropServices.InAttribute)",
    parameters := [intType] },
  name := "get_Item",
  target := .external (runtime ++ "::!0& modreq(System.Runtime.InteropServices.InAttribute) \
    System.ReadOnlySpan`1<System.UInt32>::get_Item(System.Int32)"),
  typeArguments := [], parameterCount := 1, returnsValue := true }

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (locals : List TypeExpr) (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [words, intType], locals, initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

-- Only a primitive runtime span names a span local.
example : spanLocal words ∧ spanLocal (span runtime .byte) := by decide
example : ¬ spanLocal (span owner .uint32) ∧ ¬ spanLocal (span runtime .double) ∧
    ¬ spanLocal intType := by decide

/-- Native integers and the two small primitive types retain their physical element widths. -/
theorem primitive_span_widths :
    spanStorage (span runtime .intPtr) = some (.span 8 false) ∧
    spanStorage (span runtime .uintPtr) = some (.span 8 false) ∧
    spanStorage (span runtime .char) = some (.span 2 false) ∧
    spanStorage (span runtime .boolean) = some (.span 1 false) := by decide
#print axioms primitive_span_widths

/-- Each range has the MemberRef declaration of the corresponding array overload. -/
private def arraySpanCall (range : ArraySpanRange) (element : TypeExpr) : CallSite :=
  let bounds := match range with
    | .whole => [] | .fromStart => [intType] | .counted => [intType, intType]
  let targetParams := match range with
    | .whole => "!!0[]" | .fromStart => "!!0[],System.Int32"
    | .counted => "!!0[],System.Int32,System.Int32"
  let view := TypeExpr.apply (.constructor runtime "System.Span`1")
  { declared := ⟨0x10, view (.parameter 0), .array (.parameter 0) :: bounds⟩
    method := {
      owner := .atom spanMemoryScope "System.MemoryExtensions", name := name!"AsSpan",
      hasThis := false, genericArity := 1, returnType := view element,
      parameters := .array element :: bounds, methodArguments := [element] }
    name := "AsSpan"
    target := .external (spanMemoryScope ++
      s!"::System.Span`1<!!0> System.MemoryExtensions::AsSpan({targetParams})")
    typeArguments := [element], parameterCount := 1 + bounds.length, returnsValue := true }

/-- Decode a single live call under the production model table. -/
private def decodeArrayCall (site : CallSite) (layouts : LayoutEnvironment := {}) :=
  (decodeRaw .scalar layouts [] [true] (raw [] [i 40 (.call site)]) []).map Method.code

/-- Each range retains its call and rejects a mismatched raw or closed field. -/
theorem exact_array_span_call :
    [ArraySpanRange.whole, .fromStart, .counted].all (fun range =>
      let site := arraySpanCall range intType
      let method := site.method
      let wrongOpen := site.declared.parameters.set 0 (.array (.ownerParameter 0))
      let refused := [ { site with method.owner := .atom runtime "System.MemoryExtensions" },
        { site with name := "Another" }, { site with method.name := name!"Another" },
        { site with method.genericArity := 2 }, { site with method.hasThis := true },
        { site with method.parameters := method.parameters.set 0 intType },
        { site with method.returnType := .void }, { site with declared.convention := 0x20 },
        { site with declared.parameters := wrongOpen }, { site with target := .external "Another" },
        arraySpanCall range (.primitive .double),
        arraySpanCall range (.aggregate "Missing::Layout" 0) ]
      decide (decodeArrayCall site = .ok [.call method {}]) &&
        (runtimeModel {} .call method == some (.memory (.arraySpan .signed32 true range))) &&
        !runtimeCatalog.siteAgrees {} .scalar (i 40 (.call site))
          (.call method { tail := true }) none true &&
        refused.all (fun other => decide (decodeArrayCall other = liveHoleAt 0 40))) := by
  decide +kernel
#print axioms exact_array_span_call

/-- Aggregate strides come from each environment, and byref-like elements cannot form arrays. -/
theorem arraySpanLayouts :
    let element := TypeExpr.aggregate "Fixture::Words" 0
    let env := fun count byRefLike =>
      let rows : List RawLayout := [{
        identity := "Fixture::Words", explicit := false,
        packing := 0, declaredSize := 0, byRefLike,
        fields := List.replicate count ⟨.unsigned32, none⟩ }]
      ({ rawLayouts := rows, layouts := (computeLayouts rows).getD #[] } : LayoutEnvironment)
    [ArraySpanRange.whole, .fromStart, .counted].all (fun range =>
      let site := arraySpanCall range element
      decide (decodeArrayCall site (env 1 true) = liveHoleAt 0 40) &&
        [1, 3].all (fun count =>
          let storage := ArrayElement.aggregate "Fixture::Words" (count * 4)
          runtimeModel (env count false) .call site.method ==
            some (.memory (.arraySpan storage true range)))) := by
  decide +kernel
#print axioms arraySpanLayouts

/-- A kept array factory has the same result and faults as its checked memory operation. -/
theorem arraySpanStep (body : Method) (pc : Nat) (method : MethodRef) (range : ArraySpanRange)
    (element : ArrayElement) (args stack : List Safety.Value) (frame : Safety.Frame)
    (memory : Safety.Memory) (link : body.linkAt pc = none)
    (found : runtimeModel body.environment .call method = some (.memory (.arraySpan element true
      range))) :
    Safety.step body (.call method {}) pc args frame stack memory =
      Safety.modelStep (some (.memory (.arraySpan element true range))) body pc frame stack memory :=
  Safety.step_call_model body pc args frame memory link found rfl stack
#print axioms arraySpanStep

/-- Each fixture pairs a constructor declaration with the operation it must execute. -/
private def constructors (writable : Bool) (element : TypeExpr) (name : String) :
    List (CallSite × MemoryOp) := Id.run do
  let owner := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  let array := fun type => [TypeExpr.array type]
  let range := fun type => [TypeExpr.array type, intType, intType]
  let pointer := fun (_ : TypeExpr) => [TypeExpr.pointer .void, intType]
  let reference := fun type => [TypeExpr.byref type]
  let forms : List ((TypeExpr → List TypeExpr) × String × MemoryOp) :=
    [(array, "!0[]", .arraySpan .signed32 writable .whole),
     (range, "!0[],System.Int32,System.Int32", .arraySpan .signed32 writable .counted),
     (pointer, "System.Void*,System.Int32", .spanFromReference 4 writable),
     (reference, "!0&", .spanSingleReference 4 writable)]
  return forms.map fun (parameters, target, operation) =>
    let method : MethodRef := {
      owner := .apply (.constructor runtime owner) element, name := name!".ctor", hasThis := true,
      genericArity := 0, returnType := .void, parameters := parameters element }
    let site : CallSite := {
      declared := ⟨0x20, .void, parameters (.ownerParameter 0)⟩, method, name := ".ctor"
      target := .external s!"{runtime}::System.Void {owner}<{name}>::.ctor({target})"
      typeArguments := [], parameterCount := (parameters element).length, returnsValue := false }
    (site, operation)

/-- The production decoder keeps a resolving constructor in the method body. -/
private def decodeConstructor (site : CallSite) (layouts : LayoutEnvironment := {}) :=
  (decodeRaw .scalar layouts [] [true] (raw [] [i 115 (.call site)]) []).map Method.code

/-- A refused constructor leaves a newobj hole and prevents admission of the live method. -/
private def refusesConstructor (site : CallSite) (layouts : LayoutEnvironment := {}) : Bool :=
  let source := raw [] [i 115 (.call site)]
  methodCode .scalar layouts [] [true] source == [.unadmitted 115] &&
    decide (decodeConstructor site layouts = liveHoleAt 0 115)

/-- Both owners bind the eight declarations, the exact external target and the closed arguments. -/
theorem constructor_models :
    [true, false].all (fun writable =>
      (constructors writable intType "System.Int32").all (fun (site, op) =>
        let method := site.method
        let otherHead := TypeExpr.constructor owner
          (if writable then "System.Span`1" else "System.ReadOnlySpan`1")
        let refused := [{ site with method.owner := .apply otherHead intType },
          { site with name := "Other" }, { site with method.name := name!"Other" },
          { site with method.genericArity := 1 }, { site with method.hasThis := false },
          { site with parameterCount := 0 }, { site with returnsValue := true },
          { site with method.returnType := intType }, { site with method.parameters := [intType] },
          { site with declared.parameters := [] }, { site with declared.convention := 0 },
          { site with target := .external "Other" }]
        decide (decodeConstructor site = .ok [.newobj method]) &&
          (runtimeModel {} .newobj method == some (.memory op)) &&
          (method.parameters.length == op.argumentCount) &&
          !runtimeCatalog.siteAgrees {} .scalar (i 115 (.call site)) (.call method) none true &&
          refused.all (fun other => refusesConstructor other)) &&
      [(TypeExpr.primitive .double, "System.Double"),
       (.aggregate "Missing::Layout" 0, "Layout")].all (fun (element, name) =>
        (constructors writable element name).all (fun (site, _) =>
          refusesConstructor site))) := by
  decide +kernel
#print axioms constructor_models

/-- Both array overloads reject a byref-like element even when its aggregate layout has a size. -/
theorem constructor_array_storage :
    let element := TypeExpr.aggregate "Fixture::Words" 0
    let rows : List RawLayout := [{
      identity := "Fixture::Words", explicit := false, packing := 0, declaredSize := 0,
      byRefLike := true, fields := [⟨.unsigned32, none⟩] }]
    let env : LayoutEnvironment := { rawLayouts := rows, layouts := (computeLayouts rows).getD #[] }
    [true, false].all (fun writable =>
      ((constructors writable element "Words").take 2).all (fun (site, _) =>
        refusesConstructor site env)) := by
  decide +kernel
#print axioms constructor_array_storage

/-- The readonly byte pointer overload uses the checked byte-span construction. -/
theorem byte_pointer_constructor :
    ((constructors false (.primitive .byte) "System.Byte")[2]?).any (fun (site, _) =>
      runtimeModel {} .newobj site.method == some (.memory .spanCreate)) := by
  decide +kernel
#print axioms byte_pointer_constructor

-- 0: ldarg.0; 1: stloc.0; 2: ldloca.s 0; 3: ldarg.1; 4: get_Item; 5: ldind.i4; 6: ret
private def itemCode := [i 2, i 10, i 18 (.local 0), i 3, i 40 (.call getItem), i 74, i 42]
private def itemStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none, none], state [none], state [none]]
private def itemOps : List Instruction :=
  [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .call getItem.method {}, .ldind .i4, .ret]

/-- Storing and addressing a span receiver leaves every instruction outside a fold. -/
theorem length_receiver_roles :
    foldRoles [i 10, i 18 (.local 0), i 40 (.call {
      declared := { convention := 0x20, returnType := intType },
      method := {
        owner := words, name := name!"get_Length", hasThis := true, genericArity := 0,
        returnType := intType, parameters := [] },
      name := "get_Length",
      target := .external (runtime ++
        "::System.Int32 System.ReadOnlySpan`1<System.UInt32>::get_Length()"),
      typeArguments := [], parameterCount := 0, returnsValue := true })] =
        [none, none, none] := by decide +kernel
#print axioms length_receiver_roles

/-- Indexed span receivers retain every raw instruction outside a fold. -/
theorem item_receiver_roles : foldRoles itemCode = List.replicate 7 none := by
  decide +kernel
#print axioms item_receiver_roles

example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [words] itemCode) .scalar
    itemStates
    (List.replicate 7 true) itemOps := by decide
-- Erasing either receiver instruction fails its raw opcode check.
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [words] itemCode) .scalar
    itemStates
    (List.replicate 7 true)
    (itemOps.set 1 .nop) := by decide
example : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [words] itemCode) .scalar
    itemStates
    (List.replicate 7 true)
    (itemOps.set 2 .nop) := by decide

-- Span locals retain ordinary load/store flow.
private def loadCode := [i 2, i 10, i 6, i 42]
private def loadOps : List Instruction := [.ldarg 0, .stloc 0, .ldloc 0, .ret]
private def loadStates : FeatureCertificate := [state [], state [none], state [], state [none]]
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [intType] loadCode) .scalar
    loadStates
    (List.replicate 4 true) loadOps := by decide
example : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [words] loadCode) .scalar
    loadStates
    (List.replicate 4 true) loadOps := by decide

-- `ldtoken` of a field is static data; only a type handle belongs to a type test.
example : ¬ typeTestInstruction
      (i 208 (.field (.atom owner "<PrivateImplementationDetails>") 0 intType name!"Data" true)) ∧
    typeTestInstruction (i 208 (.type intType)) := by decide

/-- The eight bulk declarations instantiated at the named element type. -/
private def bulkSites (element : TypeExpr) (elementName : String) : List CallSite := Id.run do
  let writable := spanHead true
  let boolean := TypeExpr.primitive .boolean
  let var := TypeExpr.ownerParameter 0
  let row (owner : TypeExpr) (ownerName name : String) (key : MetadataName)
      (result : TypeExpr) (resultName params : String) (closed openParams : List TypeExpr)
      (array := false) : CallSite :=
    let args := if array then [element] else []
    { method := ⟨owner, key, !array, if array then 1 else 0, result, closed, args⟩
      declared := ⟨if array then 0x10 else 0x20, result, openParams⟩
      name, typeArguments := args, parameterCount := closed.length,
      returnsValue := result != .void
      target := .external s!"{runtime}::{resultName} {ownerName}::{name}({params})" }
  let owner := TypeExpr.apply writable element
  let spelling := s!"System.Span`1<{elementName}>"
  let copies := [true, false].flatMap fun writableSource =>
    let source := TypeExpr.apply (spanHead writableSource) element
    let head := if writableSource then "System.Span`1" else "System.ReadOnlySpan`1"
    let sourceName := s!"{head}<{elementName}>"
    [row source sourceName "CopyTo" name!"CopyTo" .void "System.Void" "System.Span`1<!0>"
       [owner] [.apply writable var],
     row source sourceName "TryCopyTo" name!"TryCopyTo" boolean "System.Boolean"
       "System.Span`1<!0>" [owner] [.apply writable var]]
  let arrays := [false, true].map fun counted =>
    let tail := if counted then [intType, intType] else []
    let params := if counted then "!!0[],!!0,System.Int32,System.Int32" else "!!0[],!!0"
    row (.atom runtime "System.Array") "System.Array" "Fill" name!"Fill" .void "System.Void"
      params ([.array element, element] ++ tail) ([.array (.parameter 0), .parameter 0] ++ tail)
      true
  return [row owner spelling "Clear" name!"Clear" .void "System.Void" "" [] [],
    row owner spelling "Fill" name!"Fill" .void "System.Void" "!0" [element] [var]] ++
    copies ++ arrays

/-- The instruction at the sole reachable call in the fixture. -/
private def bulkCode (site : CallSite) : Except RawDecodeError (List Instruction) :=
  let body := { raw [] [i 40 (.call site)] with parameters := [] }
  (decodeRaw .scalar {} [] [true] body []).map Method.code

/-- Every genuine overload retains its call. One incorrect operand field refuses the method. -/
theorem bulk_call_operands :
    ((bulkSites intType "System.Int32").all fun site =>
      let method := site.method
      let wrongOwner := match method.owner with
        | .apply (.constructor _ name) element => .apply (.constructor owner name) element
        | _ => TypeExpr.atom owner "System.Array"
      let wrongResult := if method.returnType == .void then intType else .void
      let wrongParams := match method.parameters with
        | [] => [intType] | _ :: rest => TypeExpr.void :: rest
      decide (bulkCode site = .ok [.call method {}]) &&
        [{ site with method.owner := wrongOwner }, { site with method.name := name!"Other" },
         { site with method.genericArity := method.genericArity + 1 },
         { site with method.parameters := wrongParams },
         { site with method.hasThis := !method.hasThis },
         { site with method.returnType := wrongResult }, { site with declared.convention := 0 },
         { site with declared.parameters := .void :: site.declared.parameters },
         { site with name := "Other" }, { site with target := .external "Other" },
         { site with parameterCount := site.parameterCount + 1 },
         { site with returnsValue := !site.returnsValue },
         { site with ownerArgumentCount := 1 }, { site with typeArguments := [TypeExpr.void] }].all
          fun changed => decide (bulkCode changed = liveHoleAt 0 40)) := by
  decide +kernel

#print axioms bulk_call_operands

/-- A well-formed overload over a floating-point element has no bulk memory model. -/
theorem bulk_call_elements :
    ((bulkSites (.primitive .single) "System.Single").all fun site =>
      decide (bulkCode site = liveHoleAt 0 40)) := by
  decide +kernel

#print axioms bulk_call_elements

/-- The signed backing and nominal identity survive both array fill overloads. -/
theorem bulk_enum_models :
    let element := TypeExpr.enum (Tests.enumIdentity "Tag") .signed8
    let storage := ArrayElement.enumeration (Tests.enumIdentity "Tag") .signed8
    let operations : List MemoryOp := [.spanFill 1 true, .spanFill 1 false, .spanCopy 1 false,
      .spanCopy 1 true, .spanCopy 1 false, .spanCopy 1 true, .arrayFill storage false,
      .arrayFill storage true]
    ((bulkSites element "Tag").zip operations).all fun (site, operation) =>
      runtimeModel {} .call site.method == some (.memory operation) &&
        !(runtimeCatalog.siteAgrees {} .scalar (i 40 (.call site))
          (.call site.method { tail := true }) none true)
    := by decide +kernel

#print axioms bulk_enum_models

/-- Span copy and fill admit integer vectors. Both array fill overloads reject them. -/
theorem bulk_vector_models :
    let vector := TypeExpr.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1"
    let element := TypeExpr.apply vector intType
    (bulkSites element "System.Runtime.Intrinsics.Vector128`1<System.Int32>").all fun site =>
      let expected := if site.hasThis then .ok [.call site.method {}] else liveHoleAt 0 40
      decide (bulkCode site = expected)
    := by decide +kernel

#print axioms bulk_vector_models

/-- Span copy, clear and fill admit a laid-out struct. Both array fill overloads refuse it. -/
theorem bulk_aggregate_models :
    let element := TypeExpr.aggregate "Fixture::Words" 0
    let rows : List RawLayout := [{
      identity := "Fixture::Words", explicit := false,
      packing := 0, declaredSize := 0, byRefLike := false,
      fields := [⟨.unsigned32, none⟩] }]
    let layouts : LayoutEnvironment :=
      { rawLayouts := rows, layouts := (computeLayouts rows).getD #[] }
    (bulkSites element "Words").all fun site =>
      let body := { raw [] [i 40 (.call site)] with parameters := [] }
      let expected := if site.hasThis then .ok [.call site.method {}] else liveHoleAt 0 40
      decide ((decodeRaw .scalar layouts [] [true] body []).map Method.code = expected)
    := by decide +kernel

#print axioms bulk_aggregate_models

/-- `ReadOnlySpan<uint>(uint[])`, the array constructor a call runs on a span home. -/
private def localConstructor : CallSite := {
  declared := { convention := 0x20, parameters := [.array (.parameter 0)] },
  method := {
    owner := words, name := name!".ctor", hasThis := true, genericArity := 0, returnType := .void,
    parameters := [.array (.primitive .uint32)] },
  name := ".ctor",
  target := .external (runtime ++
    "::System.Void System.ReadOnlySpan`1<System.UInt32>::.ctor(!0[])"), typeArguments := [],
  parameterCount := 1, returnsValue := false }

/-- The address of span local 0, a null array and the constructor call. -/
private def constructorCode :=
  [i 18 (.local 0), i 20, i 40 (.call localConstructor), i 42]

/-- Whether object admission accepts the constructor windows and span resets of `source`, with
    every instruction live. -/
private def admitted (source : RawMethod) : Bool :=
  (objectSites source (source.code.map fun _ => true)
    { code := source.code.map fun _ => .nop, locals := [], returnsValue := false }).isSome

/-- A constructor call runs on the address of a local or parameter of the constructed span type
    followed by one pure push per parameter. -/
theorem constructor_window_admitted :
    admitted (raw [words] constructorCode) = true ∧
    admitted (raw [words, .array (.primitive .uint32)]
      [i 18 (.local 0), i 7, i 40 (.call localConstructor), i 42]) = true ∧
    admitted (raw [] [i 15 (.argument 0), i 20, i 40 (.call localConstructor), i 42]) = true := by
  decide +kernel
#print axioms constructor_window_admitted

/-- Admission refuses a constructor whose receiver is not a home of the constructed span type: a
    store or a duplicate inside the window, a local of another span type, an `in` parameter
    loaded by value, and a branch to an argument push or to the call. -/
theorem constructor_window_refused :
    admitted (raw [words, .array (.primitive .uint32)]
      [i 18 (.local 0), i 20, i 11, i 7, i 40 (.call localConstructor), i 42]) = false ∧
    admitted (raw [words] [i 18 (.local 0), i 37, i 20, i 40 (.call localConstructor)]) = false ∧
    admitted (raw [span runtime .int32] constructorCode) = false ∧
    admitted { raw [] [i 2, i 20, i 40 (.call localConstructor), i 42] with
      parameters := [.byref words] } = false ∧
    admitted (raw [words] (constructorCode ++ [i 43 (.target 1)])) = false ∧
    admitted (raw [words] (constructorCode ++ [i 43 (.target 2)])) = false := by decide +kernel
#print axioms constructor_window_refused

/-- A branch may enter at the address itself, since the window starts there. -/
theorem constructor_window_entry_at_address :
    admitted (raw [words] (constructorCode ++ [i 43 (.target 0)])) = true := by decide +kernel
#print axioms constructor_window_entry_at_address

/-- A span `initobj` resets the home its preceding raw instruction addresses, of its own type, and
    is not a branch target. -/
theorem span_reset_evidence :
    admitted (raw [words] [i 18 (.local 0), i 65045 (.type words), i 42]) = true ∧
    admitted (raw [] [i 15 (.argument 0), i 65045 (.type words), i 42]) = true ∧
    admitted (raw [words] [i 18 (.local 0), i 0, i 65045 (.type words), i 42]) = false ∧
    admitted (raw [span runtime .int32]
      [i 18 (.local 0), i 65045 (.type words), i 42]) = false ∧
    admitted (raw [words]
      [i 18 (.local 0), i 65045 (.type words), i 42, i 43 (.target 1)]) = false := by
  decide +kernel
#print axioms span_reset_evidence

/-- The byte-span constructor decodes to the address of its home and a model call, consumes its
    argument and returns with an empty stack. -/
theorem decoded_span_constructor_returns :
    let byte := TypeExpr.primitive .byte
    let bytes := TypeExpr.apply (.constructor runtimeScope "System.Span`1") byte
    let ctor := { localConstructor with
      method.owner := bytes,
      method.parameters := [.byref byte], declared.parameters := [.byref (.ownerParameter 0)],
      target := .external (runtimeScope ++
        "::System.Void System.Span`1<System.Byte>::.ctor(!0&)") }
    let source := { raw [bytes] [i 18 (.local 0), i 2, i 40 (.call ctor), i 42] with
      parameters := [.byref byte], returnType := .void }
    let method := Method.ofRaw? .scalar {} [] [true, true, true, true] source []
    let memory : Safety.Memory := { Safety.Memory.empty with
      allocations := fun id => if id == 0 then
        some ⟨.callerStack, ⟨1, 1, []⟩, true, []⟩ else none,
      views := [⟨0, 0, 1, true, true⟩], nextIdentity := 1 }
    method.map Method.code = some [.ldloca 0, .ldarg 0, .call ctor.method, .ret] ∧
      (method.bind fun body => (Safety.invoke [body] 5 0 [.reference (.address ⟨0, 0⟩)]
        memory).toOption.map (·.2)) = some [] := by
  exact ⟨rfl, rfl⟩

#print axioms decoded_span_constructor_returns

/-- Resetting an aggregate span decodes to `initobj` on its home and returns normally; without the
    element layout the method is refused. -/
theorem decoded_span_reset_returns :
    let identity := "Fixture::Word"
    let element := TypeExpr.aggregate identity 0
    let spanType := TypeExpr.apply (.constructor runtimeScope "System.Span`1") element
    let row : RawLayout := {
      identity, explicit := false, packing := 0, declaredSize := 0,
      fields := [⟨.unsigned64, none⟩] }
    let environment : LayoutEnvironment := {
      rawLayouts := [row], layouts := #[⟨⟨8, [⟨0, 8, false⟩]⟩, 8⟩] }
    let source := { raw [spanType] [i 18 (.local 0), i 65045 (.type spanType), i 42] with
      parameters := [], returnType := .void }
    let method := Method.ofRaw? .scalar environment [] [true, true, true] source []
    method.map Method.code = some [.ldloca 0, .initobj spanType, .ret] ∧
      (method.bind fun body => (Safety.invoke [body] 5 0 [] Safety.Memory.empty).toOption.map
        (·.2)) = some [] ∧
      Method.ofRaw? .scalar { environment with layouts := #[] } [] [true, true, true] source [] =
        none := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms decoded_span_reset_returns
/-- Runtime names omit scopes without discarding nested or adjacent generic arguments. -/
theorem closed_generic_element_names :
    spanElementName (.aggregate ("Examples::Pair`1<" ++ runtimeScope ++ "::System.UInt64>") 0) =
      some "Pair`1<System.UInt64>" ∧
    spanElementName (.aggregate ("Examples::Outer`2<Examples::Pair`1<" ++
      runtimeScope ++ "::System.UInt64>," ++ runtimeScope ++ "::System.UInt32>") 1) =
      some "Outer`2<Pair`1<System.UInt64>,System.UInt32>" ∧
    spanElementName (.aggregate
      "System.Runtime::System.ValueTuple`2<System.UInt64,System.UInt64>" 2) =
      some "System.ValueTuple`2<System.UInt64,System.UInt64>" := by decide +kernel
#print axioms closed_generic_element_names

end Tests.SpanEvidence
