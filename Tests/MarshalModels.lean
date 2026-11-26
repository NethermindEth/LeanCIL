import Tests.Support.EnumIdentity
import CIL.Extraction.DecodedMethod
import CIL.Extraction.BitModels
import CIL.Safety.StepComposition
import Tests.MetadataWorld
import Tests.Support.RawDecoding

/-! Call-site checks for the MemoryMarshal overloads in the example assembly. -/

namespace Tests.MarshalModels
open CIL CIL.Extraction

/-- One closed instantiation and the operation the extractor emits for it. -/
private structure Fixture where
  name : String
  result : TypeExpr
  parameters : List TypeExpr
  arguments : List TypeExpr
  operation : MemoryOp

/-- The writable or readonly view of one element. -/
private def view (writable : Bool) (element : TypeExpr) : TypeExpr :=
  let owner := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  .apply (.constructor runtimeScope owner) element

/-- All observed overloads, with the source and target elements supplied by the caller. -/
private def fixtures (source target : TypeExpr) (width targetWidth : Nat) (kind : TransferKind) :
    List Fixture :=
  let byte := TypeExpr.primitive .byte
  let span := view true
  let readOnly := view false
  [⟨"GetReference", .byref source, [span source], [source], .spanReference⟩,
   ⟨"GetReference", .byref source, [readOnly source], [source], .spanReference⟩,
   ⟨"GetArrayDataReference", .byref source, [.array source], [source],
     .observeView .arrayData⟩,
   ⟨"AsBytes", span byte, [span source], [source], .spanReinterpret width 1 true⟩,
   ⟨"AsBytes", readOnly byte, [readOnly source], [source], .spanReinterpret width 1 false⟩,
   ⟨"Cast", span target, [span source], [source, target],
     .spanReinterpret width targetWidth true⟩,
   ⟨"Cast", readOnly target, [readOnly source], [source, target],
     .spanReinterpret width targetWidth false⟩,
   ⟨"CreateSpan", span source, [.byref source, int32Type], [source],
     .spanFromReference width true⟩,
   ⟨"CreateReadOnlySpan", readOnly source, [.byref source, int32Type], [source],
     .spanFromReference width false⟩,
   ⟨"Read", source, [readOnly byte], [source], .marshalRead kind false⟩,
   ⟨"TryRead", booleanType, [readOnly byte, .byref source], [source], .marshalRead kind true⟩,
   ⟨"Write", .void, [span byte, .byref source], [source], .marshalWrite kind false⟩,
   ⟨"TryWrite", booleanType, [span byte, .byref source], [source], .marshalWrite kind true⟩]

/-- The actual open declarations, in fixture order. -/
private def declarations : List OpenSignature :=
  (fixtures (.parameter 0) (.parameter 1) 0 0 (.scalar 0 false)).map fun fixture =>
    { convention := 0x10, returnType := fixture.result, parameters := fixture.parameters }

/-- The closed method reference at a fixture's call. -/
private def Fixture.method (fixture : Fixture) : MethodRef :=
  { owner := .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" .classType,
    name := (MetadataName.ofBytes? (fixture.name.toList.map Char.toNat)).getD ⟨0⟩,
    hasThis := false, genericArity := fixture.arguments.length,
    methodArguments := fixture.arguments, parameters := fixture.parameters,
    returnType := fixture.result }

/-- A live call with a supplied declaration. -/
private def Fixture.raw (fixture : Fixture) (declared : OpenSignature) : RawInstruction :=
  let site : CallSite :=
    { method := fixture.method, declared, name := fixture.name, target := .external ""
      typeArguments := fixture.arguments
      parameterCount := fixture.parameters.length, returnsValue := fixture.result != .void }
  ⟨0, 40, .call site⟩

/-- Concrete 32-bit elements and 16-bit Cast targets. -/
private def scalarSites : List (Fixture × OpenSignature) :=
  (fixtures int32Type (.primitive .int16) 4 2 (.scalar 4 false)).zip declarations

/-- The same closed signature under a declaration with a different parameter list. -/
private def changed (declaration : OpenSignature) : OpenSignature :=
  { declaration with parameters := .void :: declaration.parameters.drop 1 }

/-- The struct type at layout index zero. -/
private def packet : TypeExpr := .aggregate "Fixture::Packet" 0

/-- A checked struct layout holding the given number of 64-bit fields. -/
private def sized (words : Nat) : LayoutEnvironment :=
  let layout : RawLayout :=
    { identity := "Fixture::Packet", explicit := false, packing := 0, declaredSize := 0
      fields := List.replicate words { type := .unsigned64 } }
  let raw := [layout]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

/-- A vector of the runtime's specified lane type. -/
private def vector (element : PrimitiveType) (bits : Nat := 128) : TypeExpr :=
  let owner := if bits == 128 then "System.Runtime.Intrinsics.Vector128`1"
    else if bits == 256 then "System.Runtime.Intrinsics.Vector256`1"
    else "System.Runtime.Intrinsics.Vector512`1"
  .apply (.constructor intrinsicsScope owner) (.primitive element)

/-- Every reference resolves to its expected operation. -/
private def resolves (environment : LayoutEnvironment) (cases : List Fixture) : Bool :=
  cases.all fun fixture =>
    runtimeModel environment .call fixture.method == some (.memory fixture.operation)

/-- Both overloads preserve mutability. Aggregate widths follow each environment's layout. -/
theorem marshal_resolutions :
    resolves {} (scalarSites.map Prod.fst) ∧
    resolves {} (fixtures (vector .byte) int32Type 16 4 (.snapshot .vector128)) ∧
    resolves (sized 1) (fixtures packet packet 8 8 (.snapshot (.aggregate 8))) ∧
    resolves (sized 3) (fixtures packet packet 24 24 (.snapshot (.aggregate 24))) := by
  decide +kernel

#print axioms marshal_resolutions

/-- Narrow signed integers and enums keep their sign. Boolean and Char use unsigned storage. -/
theorem marshal_scalar_storage :
    resolves {} (fixtures (.primitive .int16) int32Type 2 4 (.scalar 2 true)) ∧
    resolves {} (fixtures (.enum (Tests.enumIdentity "Kind") .signed8)
      int32Type 1 4 (.scalar 1 true)) ∧
    resolves {} (fixtures booleanType int32Type 1 4 (.scalar 1 false)) ∧
    resolves {} (fixtures (.primitive .char) int32Type 2 4 (.scalar 2 false)) := by
  decide +kernel

#print axioms marshal_scalar_storage

/-- The selected references must have the exact owner, shape, closed result and parameters. -/
theorem marshal_reference_shapes :
    scalarSites.all (fun (fixture, _) =>
      let method := fixture.method
      [{ method with owner := .apply method.owner int32Type },
       { method with
         owner := .atom "Other" "System.Runtime.InteropServices.MemoryMarshal" .classType },
       { method with hasThis := true }, { method with genericArity := method.genericArity + 1 },
       { method with methodArguments := [] }, { method with returnType := .pointer .void },
       { method with parameters := [] }].all fun changedMethod =>
        (runtimeModel {} .call changedMethod).isNone) = true := by decide +kernel

#print axioms marshal_reference_shapes

/-- Every member refuses types outside its checked element set, on either side of a Cast. -/
theorem marshal_excluded_elements :
    [view true int32Type, TypeExpr.parameter 0, .pointer int32Type, .byref int32Type,
     .object "Fixture" "Class", .apply (.objectConstructor "Fixture" "Box") int32Type,
     .primitive .single, vector .double, packet].all (fun element =>
      (fixtures element int32Type 0 4 (.scalar 4 false)).all (fun fixture =>
        (runtimeModel {} .call fixture.method).isNone) &&
      ((fixtures int32Type element 4 0 (.scalar 4 false)).filter
        (fun fixture => fixture.name == "Cast")).all (fun fixture =>
          (runtimeModel {} .call fixture.method).isNone)) = true := by decide +kernel

#print axioms marshal_excluded_elements

/-- A Cast result keeps the target element identity and the input span's capability. -/
theorem cast_result_identity :
    scalarSites.all (fun (fixture, _) => fixture.name != "Cast" ||
      let method := fixture.method
      let writable := method.parameters == [view true int32Type]
      let unsigned := view writable (.primitive .uint16)
      let flipped := view (!writable) (.primitive .int16)
      [unsigned, flipped].all fun result =>
        (runtimeModel {} .call { method with returnType := result }).isNone) = true := by
  decide +kernel

#print axioms cast_result_identity

/-- The token instantiates one Cast declaration with Int32 and Int16. -/
private def castToken (span : String) : MetadataSlice × Nat := open Tests.MetadataBuilder in
  build (do
    let _ ← Tests.MetadataWorld.ownWorld
    let owner ← row Table.typeRef
      [6, ← string "MemoryMarshal", ← string "System.Runtime.InteropServices"]
    let viewType ← row Table.typeRef [6, ← string span, ← string "System"]
    let viewOf := fun index => [0x15, 0x11, tokenRow viewType * 4 + 1, 1, 0x1e, index]
    let signature ← blob ([0x10, 2, 1] ++ viewOf 1 ++ viewOf 0)
    let member ← row Table.memberRef [tokenRow owner * 8 + 1, ← string "Cast", signature]
    row Table.methodSpec [tokenRow member * 2 + 1, ← blob [0x0a, 2, 0x08, 0x06]])
    (bytesOf "T")

/-- The token, external target and open declaration all name the same Cast overload. -/
private def castBinding (writable : Bool) : Bool := Id.run do
  let span := if writable then "Span`1" else "ReadOnlySpan`1"
  let (metadata, token) := castToken span
  let .ok index := metadata.index | return false
  let platform : PlatformTable := platform_table%
    [Tests.MetadataBuilder.runtimeType "Object" .objectRoot,
     Tests.MetadataBuilder.runtimeType "Span`1" (.genericValue 1),
     Tests.MetadataBuilder.runtimeType "ReadOnlySpan`1" (.genericValue 1),
     ⟨runtimeAssembly, [bytesOf "System.Runtime.InteropServices", bytesOf "MemoryMarshal"],
       .classType⟩]
  let env := MetadataEnv.ofSlices [index] (platform := platform)
  let .ok frame := env.frame 0 0 | return false
  let findCast := fun capability => scalarSites.find? fun (fixture, _) =>
    fixture.name == "Cast" && fixture.parameters == [view capability int32Type]
  let some (matching, declared) := findCast writable | return false
  let some (opposite, _) := findCast (!writable) | return false
  let owner := "System.Runtime.InteropServices.MemoryMarshal"
  let target := s!"{runtimeScope}::System.{span}<!!1> {owner}::Cast(System.{span}<!!0>)"
  let .call original := (matching.raw declared).operand | return false
  let control := { original with target := .external target }
  let crossed := { control with method := opposite.method }
  return (checkCallOperand env frame token control).isOk &&
    runtimeCatalog.siteAgrees {} .scalar ⟨0, 40, .call crossed⟩ (.call crossed.method {})
      none true &&
    (match checkCallOperand env frame token crossed with
     | .error (.operandMismatch found) => found == token
     | _ => false)

/-- The model row accepts either crossed Cast, but BodyDecodes refuses its closed reference
    through checkCallOperand for the token of the declared overload. -/
theorem crossed_cast_overloads : castBinding true ∧ castBinding false := by decide +kernel

#print axioms crossed_cast_overloads

/-- The caller contains one marshal call at pc zero. -/
private def marshalCaller (raw : RawInstruction) : RawMethod :=
  { token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
    callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
    parameters := [], locals := [],
    initLocals := false, maxStack := 0, genericParameters := [], code := [raw] }

/-- A refused method-token operand decodes to its opcode's hole, which must be dead. -/
private def refused (raw : RawInstruction) (alternative : Instruction) : Bool :=
  let required := runtimeCatalog.callRequirement (LayoutEnvironment.callLayouts {})
    .scalar none raw
  siteClaim {} none raw == .refused &&
    decide ((decodeRaw .scalar {} [] [true] (marshalCaller raw) []).map Method.code =
      liveHoleAt 0 40) &&
    required.accepts false (.unadmitted 40) && !required.accepts true (.unadmitted 40) &&
    !required.accepts true alternative && !required.accepts false alternative

/-- Floating vectors of every supported register width have no transfer or span model. -/
theorem floating_vectors_refused :
    [128, 256, 512].all (fun bits => [PrimitiveType.single, .double].all fun lane =>
      let element := vector lane bits
      let shape := if bits == 128 then SnapshotShape.vector128 else
        if bits == 256 then .vector256 else .vector512
      let cases := fixtures element int32Type (bits / 8) 4 (.snapshot shape)
      (cases.zip declarations).all (fun (fixture, sig) =>
        refused (fixture.raw sig) (.call fixture.method {})) &&
      ((fixtures int32Type element 4 (bits / 8) (.scalar 4 false)).zip declarations).all
        (fun (fixture, sig) => fixture.name != "Cast" ||
          refused (fixture.raw sig) (.call fixture.method {}))) = true := by decide +kernel

#print axioms floating_vectors_refused

/-- Missing layouts and unknown names both require the call's hole. -/
theorem unresolved_marshal_sites :
    ((fixtures packet packet 8 8 (.snapshot (.aggregate 8))).zip declarations).all
      (fun (fixture, sig) => refused (fixture.raw sig) (.call fixture.method {})) = true ∧
    scalarSites.all (fun (fixture, sig) =>
      refused ({ fixture with name := "Unknown" }.raw sig) (.call fixture.method {})) =
        true := by decide +kernel

#print axioms unresolved_marshal_sites

/-- ManagedCallsValid refuses a linked Write<Double> through import admission even when the
    slot has the exact signature and the decoder retains the call. -/
theorem linked_write_import_refused :
    let double := TypeExpr.primitive .double
    let bytes := view true (.primitive .byte)
    let owner := "System.Runtime.InteropServices.MemoryMarshal"
    let target := s!"{runtimeScope}::System.Void {owner}::Write(System.Span`1<System.Byte>,!!0&)"
    let method : MethodRef := {
      owner := .atom runtimeScope owner .classType, name := name!"Write", hasThis := false,
      genericArity := 1,
      methodArguments := [double], returnType := .void, parameters := [bytes, .byref double] }
    let site : CallSite := {
      method, name := "Write", target := .external target, typeArguments := [double],
      declared := { convention := 0x10, parameters := [bytes, .byref (.parameter 0)] },
      parameterCount := 2, returnsValue := false }
    let source := marshalCaller ⟨0, 40, .call site⟩
    let slot : ImportSlot := {
      identity := target, closureDigest := "digest", parameterCount := 2, hasThis := false,
      returnsValue := false, signature := some ⟨method.owner, site.name, site.typeArguments,
        method.returnType, method.parameters⟩ }
    (Method.ofRaw? .scalar {} [(0, .direct 0)] [true] source []).any (fun emitted =>
      decide (emitted.code = [.call method {}] ∧ emitted.links = [(0, .direct 0)] ∧
        runtimeModel {} .call method = none ∧ importSignatureMatches slot site = false ∧
        ¬ ManagedCallsValid [] [slot] (callModelled emitted) source [true] emitted)) = true := by
  decide +kernel

#print axioms linked_write_import_refused

/-- A live marshal site keeps the genuine call and requires its open declaration. -/
theorem marshal_site_emissions :
    scalarSites.all (fun (fixture, declaration) =>
      let site := fixture.raw declaration
      let agrees := fun raw emitted =>
        runtimeCatalog.siteAgrees {} .scalar raw emitted none true
      let call := Instruction.call fixture.method {}
      let wrongPrefix := Instruction.call fixture.method { tail := true }
      agrees site call && !agrees site wrongPrefix && !agrees site .nop &&
        !agrees (fixture.raw (changed declaration)) call &&
        !agrees (fixture.raw (changed declaration)) wrongPrefix &&
        [0x00, 0x11, 0x30, 0x50, 0x70].all (fun convention =>
          !agrees (fixture.raw { declaration with convention }) call)) = true := by decide +kernel

#print axioms marshal_site_emissions

/-- An external method whose span argument and reference result fit a unary stack effect. -/
private def unrelated : RawInstruction :=
  let method : MethodRef :=
    { owner := .atom "Fixture" "Methods" .classType, name := name!"First"
      hasThis := false, genericArity := 0, returnType := .byref int32Type
      parameters := [view true int32Type] }
  let site : CallSite :=
    { method, declared := method.signature 0, name := "First"
      target := .external "Fixture::System.Int32& Methods::First(System.Span`1<System.Int32>)"
      typeArguments := [], parameterCount := 1, returnsValue := true }
  ⟨0, 40, .call site⟩

/-- An unrelated call cannot observe array data, construct these spans or transfer their bytes. -/
theorem unrelated_marshal_emissions :
    scalarSites.all (fun (fixture, _) =>
      !runtimeCatalog.siteAgrees {} .scalar unrelated (.call fixture.method {}) none true) =
      true := by decide +kernel

#print axioms unrelated_marshal_emissions

/-- Each resolved overload executes its bound memory model on every execution state. -/
private theorem marshal_model_steps (fixture : Fixture)
    (member : fixture ∈ scalarSites.map Prod.fst) (body : Method) (pc : Nat)
    (environment : body.environment = {}) (link : body.linkAt pc = none)
    (args stack : List Safety.Value) (frame : Safety.Frame) (memory : Safety.Memory) :
    Safety.step body (.call fixture.method {}) pc args frame stack memory =
      Safety.modelStep (some (.memory fixture.operation)) body pc frame stack memory := by
  have found := List.all_eq_true.mp marshal_resolutions.1 fixture member
  apply Safety.step_call_model body pc args frame memory link _ rfl stack
  rw [environment]
  exact beq_iff_eq.mp found

#print axioms marshal_model_steps

end Tests.MarshalModels
