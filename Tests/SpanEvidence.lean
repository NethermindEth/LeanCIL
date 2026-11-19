import CIL.Extraction.Features
import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.SpanEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def span (scope element : String) : TypeExpr :=
  .apply (.constructor scope "System.ReadOnlySpan`1") (.atom runtime element)
private def words := span runtime "System.UInt32"

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
example : spanLocal words ∧ spanLocal (span runtime "System.Byte") := by decide
example : ¬ spanLocal (span owner "System.UInt32") ∧ ¬ spanLocal (span runtime "System.Double") ∧
    ¬ spanLocal intType := by decide

/-- Native integers and the two small primitive types retain their physical element widths. -/
theorem primitive_span_widths :
    spanStorage (span runtime "System.IntPtr") = some (.span 8 false) ∧
    spanStorage (span runtime "System.UIntPtr") = some (.span 8 false) ∧
    spanStorage (span runtime "System.Char") = some (.span 2 false) ∧
    spanStorage (span runtime "System.Boolean") = some (.span 1 false) := by decide
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
  (Method.ofRaw? .scalar layouts [] [true] (raw [] [i 40 (.call site)]) []).map Method.code

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
        arraySpanCall range (.atom runtime "System.Double"),
        arraySpanCall range (.aggregate "Missing::Layout" 0) ]
      decide (decodeArrayCall site = some [.call method {}]) &&
        (runtimeModel {} .call method == some (.memory (.arraySpan .signed32 true range))) &&
        !runtimeCatalog.siteAgrees {} .scalar (i 40 (.call site))
          (.memory (.arraySpan .signed32 true range)) none none true &&
        refused.all (fun other => decide (decodeArrayCall other = some [.unadmitted 40]))) := by
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
      decide (decodeArrayCall site (env 1 true) = some [.unadmitted 40]) &&
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
      Safety.step body (.memory (.arraySpan element true range)) pc args frame stack memory :=
  Safety.step_call_memory body pc args frame memory link found rfl stack
#print axioms arraySpanStep

-- 0: ldarg.0; 1: stloc.0; 2: ldloca.s 0; 3: ldarg.1; 4: get_Item; 5: ldind.i4; 6: ret
private def itemCode := [i 2, i 10, i 18 (.local 0), i 3, i 40 (.call getItem), i 74, i 42]
private def itemStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none, none], state [none], state [none]]
private def itemOps : List Instruction :=
  [.ldarg 0, .stloc 0, .ldloca 0, .ldarg 1, .call getItem.method {}, .ldind .i4, .ret]

/-- Storing and addressing a span receiver leaves every instruction outside a fold. -/
theorem length_receiver_roles :
    foldRoles [words] [i 10, i 18 (.local 0), i 40 (.call {
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
theorem item_receiver_roles : foldRoles [words] itemCode = List.replicate 7 none := by
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

/-- The exact writable int32 span member used by whole-region initialization. -/
private def fillCall : CallSite := {
  declared := { convention := 0x20, parameters := [.parameter 0] },
  method := {
    owner := .apply (.constructor runtime "System.Span`1") intType, name := name!"Fill",
    hasThis := true, genericArity := 0, returnType := .void, parameters := [intType] },
  name := "Fill",
  target := .external (runtime ++ "::System.Void System.Span`1<System.Int32>::Fill(!0)"),
  typeArguments := [], parameterCount := 1, returnsValue := false }

/-- Whole-span stores bind the operation, element width, mutability and complete signature. -/
theorem exact_span_fill_call :
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 4 false)) = true ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 8 false)) = false ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 4 true)) = false ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanSlice false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with
      method.owner := .apply (.constructor runtime "System.ReadOnlySpan`1") intType }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with
      method.parameters := [.atom runtime "System.UInt32"] }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with method.hasThis := false }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with
      method.returnType := intType, returnsValue := true }))
      (.memory (.spanFill 4 false)) = false := by decide +kernel
#print axioms exact_span_fill_call

/-- Exact array constructor used by an in-place local initialization. -/
private def localConstructor : CallSite := {
  declared := { convention := 0x20, parameters := [.array (.parameter 0)] },
  method := {
    owner := words, name := name!".ctor", hasThis := true, genericArity := 0, returnType := .void,
    parameters := [.array (.atom runtime "System.UInt32")] },
  name := ".ctor",
  target := .external (runtime ++
    "::System.Void System.ReadOnlySpan`1<System.UInt32>::.ctor(!0[])"), typeArguments := [],
  parameterCount := 1, returnsValue := false }

private def constructorCode :=
  [i 18 (.local 0), i 2, i 40 (.call localConstructor), i 18 (.local 0)]

/-- Reused local addresses do not disable exact constructor folding. -/
theorem constructor_fold : foldRoles [words] constructorCode =
    [some .head, some .argument, some (.spanConstructor 0 (.array .unsigned32 false .whole)),
      none] := by decide +kernel
#print axioms constructor_fold

/-- The feature check binds the array constructor's null argument to its raw push. -/
theorem constructor_argument_exact :
    let source := raw [words] [i 18 (.local 0), i 20, i 40 (.call localConstructor), i 42]
    let role := (foldRoles source.locals source.code)[1]?.join
    role = some .argument ∧
      featureOpMatchesAt #[] source role (i 20) .ldnull = true ∧
      featureOpMatchesAt #[] source role (i 20) (.ldc_i4 1) = false := by decide +kernel
#print axioms constructor_argument_exact

/-- The folded byte-span constructor consumes its argument and returns with an empty stack. -/
theorem decoded_span_constructor_returns :
    let byte := TypeExpr.atom runtimeScope "System.Byte"
    let bytes := TypeExpr.apply (.constructor runtimeScope "System.Span`1") byte
    let ctor := { localConstructor with
      method.owner := bytes,
      method.parameters := [.byref byte], declared.parameters := [.byref (.ownerParameter 0)],
      target := .external (runtimeScope ++ "::System.Void System.Span`1<System.Byte>::.ctor(!0&)") }
    let source := { raw [bytes] [i 18 (.local 0), i 2, i 40 (.call ctor), i 42] with
      parameters := [.byref byte], returnType := .void }
    let method := Method.ofRaw? .scalar {} [] [true, true, true, true] source []
    let memory : Safety.Memory := { Safety.Memory.empty with
      allocations := fun id => if id == 0 then
        some ⟨.callerStack, ⟨1, 1, []⟩, true, []⟩ else none,
      views := [⟨0, 0, 1, true, true⟩], nextIdentity := 1 }
    method.map Method.code = some [.nop, .ldarg 0, .initializeSpanLocal 0
      (.singleReference 1 true), .ret] ∧
      (method.bind fun body => (Safety.invoke [body] 5 0 [.reference (.address ⟨0, 0⟩)]
        memory).toOption.map (·.2)) = some [] := by
  exact ⟨rfl, rfl⟩

#print axioms decoded_span_constructor_returns

/-- Resetting an aggregate span uses the frame's checked element width and returns normally. -/
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
    method.map Method.code = some [.nop, .initializeSpanLocal 0 (.empty 8 true), .ret] ∧
      (method.bind fun body => (Safety.invoke [body] 5 0 [] Safety.Memory.empty).toOption.map
        (·.2)) = some [] ∧
      (methodCode .scalar { environment with layouts := #[] } [] [true, true, true] source)[1]? =
        some (.unadmitted 65045) := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms decoded_span_reset_returns

/-- Constructor arguments and the constructor itself cannot be external branch targets. -/
theorem constructor_no_interior_entry :
    foldEntry (foldRoles [words] constructorCode)[0]? = true ∧
    foldEntry (foldRoles [words] constructorCode)[1]? = false ∧
    foldEntry (foldRoles [words] constructorCode)[2]? = false := by decide +kernel
#print axioms constructor_no_interior_entry

/-- Duplicating the local address or changing its declared span type prevents the fold. -/
theorem constructor_alias_rejected :
    foldRoles [words] [i 18 (.local 0), i 37, i 2, i 40 (.call localConstructor)] =
      List.replicate 4 none ∧
    foldRoles [span runtime "System.Int32"] constructorCode = List.replicate 4 none := by
  decide +kernel
#print axioms constructor_alias_rejected

/-- The emitted local and constructor capability are both bound by the raw sequence. -/
theorem constructor_forgery_rejected :
    featureOpMatchesAt #[] (raw [words] constructorCode)
      (some (.spanConstructor 0 (.array .unsigned32 false .whole)))
      (i 40 (.call localConstructor))
      (.initializeSpanLocal 1 (.array .unsigned32 false .whole)) = false ∧
    featureOpMatchesAt #[] (raw [words] constructorCode)
      (some (.spanConstructor 0 (.array .unsigned32 false .whole)))
      (i 40 (.call localConstructor))
      (.initializeSpanLocal 0 (.array .unsigned32 true .whole)) = false := by decide +kernel
#print axioms constructor_forgery_rejected
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
