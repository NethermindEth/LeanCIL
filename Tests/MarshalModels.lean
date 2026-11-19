import CIL.Extraction.DecodedMethod
import CIL.Extraction.BitModels
import CIL.Safety.StepComposition

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
  let byte := TypeExpr.atom runtimeScope "System.Byte"
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
  { owner := .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal",
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
  (fixtures int32Type (.atom runtimeScope "System.Int16") 4 2 (.scalar 4 false)).zip declarations

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
private def vector (element : String) (bits : Nat := 128) : TypeExpr :=
  let owner := if bits == 128 then "System.Runtime.Intrinsics.Vector128`1"
    else if bits == 256 then "System.Runtime.Intrinsics.Vector256`1"
    else "System.Runtime.Intrinsics.Vector512`1"
  .apply (.constructor intrinsicsScope owner)
    (.atom runtimeScope element)

/-- Every reference resolves to its expected operation. -/
private def resolves (environment : LayoutEnvironment) (cases : List Fixture) : Bool :=
  cases.all fun fixture =>
    runtimeModel environment .call fixture.method == some (.memory fixture.operation)

/-- Both overloads preserve mutability. Aggregate widths follow each environment's layout. -/
theorem marshal_resolutions :
    resolves {} (scalarSites.map Prod.fst) ∧
    resolves {} (fixtures (vector "System.Byte") int32Type 16 4 (.snapshot .vector128)) ∧
    resolves (sized 1) (fixtures packet packet 8 8 (.snapshot (.aggregate 8))) ∧
    resolves (sized 3) (fixtures packet packet 24 24 (.snapshot (.aggregate 24))) := by
  decide +kernel

#print axioms marshal_resolutions

/-- Narrow signed integers and enums keep their sign. Boolean and Char use unsigned storage. -/
theorem marshal_scalar_storage :
    resolves {} (fixtures (.atom runtimeScope "System.Int16") int32Type 2 4 (.scalar 2 true)) ∧
    resolves {} (fixtures (.enum "Fixture::Kind" (.atom runtimeScope "System.SByte"))
      int32Type 1 4 (.scalar 1 true)) ∧
    resolves {} (fixtures booleanType int32Type 1 4 (.scalar 1 false)) ∧
    resolves {} (fixtures (.atom runtimeScope "System.Char") int32Type 2 4 (.scalar 2 false)) := by
  decide +kernel

#print axioms marshal_scalar_storage

/-- The selected references must have the exact owner, shape, closed result and parameters. -/
theorem marshal_reference_shapes :
    scalarSites.all (fun (fixture, _) =>
      let method := fixture.method
      [{ method with owner := .apply method.owner int32Type },
       { method with owner := .atom "Other" "System.Runtime.InteropServices.MemoryMarshal" },
       { method with hasThis := true }, { method with genericArity := method.genericArity + 1 },
       { method with methodArguments := [] }, { method with returnType := .pointer .void },
       { method with parameters := [] }].all fun changedMethod =>
        (runtimeModel {} .call changedMethod).isNone) = true := by decide +kernel

#print axioms marshal_reference_shapes

/-- Every member refuses types outside its checked element set, on either side of a Cast. -/
theorem marshal_excluded_elements :
    [view true int32Type, TypeExpr.parameter 0, .pointer int32Type, .byref int32Type,
     .object "Fixture" "Class", .apply (.objectConstructor "Fixture" "Box") int32Type,
     .atom runtimeScope "System.Single", vector "System.Double", packet].all (fun element =>
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
      let unsigned := view writable (.atom runtimeScope "System.UInt16")
      let flipped := view (!writable) (.atom runtimeScope "System.Int16")
      [unsigned, flipped].all fun result =>
        (runtimeModel {} .call { method with returnType := result }).isNone) = true := by
  decide +kernel

#print axioms cast_result_identity

/-- A refused method-token operand decodes to its opcode's hole, which must be dead. -/
private def refused (raw : RawInstruction) (alternative : Instruction) : Bool :=
  let source : RawMethod := {
    token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
    callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
    parameters := [], locals := [],
    initLocals := false, maxStack := 0, genericParameters := [], code := [raw] }
  let required := runtimeCatalog.callRequirement (LayoutEnvironment.callLayouts {})
    .scalar none none raw
  siteClaim loweredCallFamily {} none raw == .refused &&
    decide ((Method.ofRaw? .scalar {} [] [true] source []).map Method.code =
      some [.unadmitted 40]) &&
    required.accepts false (.unadmitted 40) && !required.accepts true (.unadmitted 40) &&
    !required.accepts true alternative && !required.accepts false alternative

/-- Floating vectors of every supported register width have no transfer or span model. -/
theorem floating_vectors_refused :
    [128, 256, 512].all (fun bits => ["System.Single", "System.Double"].all fun lane =>
      let element := vector lane bits
      let shape := if bits == 128 then SnapshotShape.vector128 else
        if bits == 256 then .vector256 else .vector512
      let cases := fixtures element int32Type (bits / 8) 4 (.snapshot shape)
      (cases.zip declarations).all (fun (fixture, sig) =>
        refused (fixture.raw sig) (.memory fixture.operation)) &&
      ((fixtures int32Type element 4 (bits / 8) (.scalar 4 false)).zip declarations).all
        (fun (fixture, sig) => fixture.name != "Cast" ||
          refused (fixture.raw sig) (.memory fixture.operation))) = true := by decide +kernel

#print axioms floating_vectors_refused

/-- Missing layouts and unknown names both require the call's hole. -/
theorem unresolved_marshal_sites :
    ((fixtures packet packet 8 8 (.snapshot (.aggregate 8))).zip declarations).all
      (fun (fixture, sig) => refused (fixture.raw sig) (.memory fixture.operation)) = true ∧
    scalarSites.all (fun (fixture, sig) =>
      refused ({ fixture with name := "Unknown" }.raw sig) (.memory fixture.operation)) =
        true := by decide +kernel

#print axioms unresolved_marshal_sites

/-- A live marshal site keeps the genuine call and requires its open declaration. -/
theorem marshal_site_emissions :
    scalarSites.all (fun (fixture, declaration) =>
      let site := fixture.raw declaration
      let agrees := fun raw emitted =>
        runtimeCatalog.siteAgrees {} .scalar raw emitted none none true
      let call := Instruction.call fixture.method {}
      let operation := Instruction.memory fixture.operation
      agrees site call && !agrees site operation && !agrees site (.memory .spanReadOnly) &&
        !agrees (fixture.raw (changed declaration)) call &&
        !agrees (fixture.raw (changed declaration)) operation &&
        [0x00, 0x11, 0x30, 0x50, 0x70].all (fun convention =>
          !agrees (fixture.raw { declaration with convention }) call)) = true := by decide +kernel

#print axioms marshal_site_emissions

/-- An external method whose span argument and reference result fit a unary stack effect. -/
private def unrelated : RawInstruction :=
  let method : MethodRef :=
    { owner := .atom "Fixture" "Methods", name := name!"First"
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
      !runtimeCatalog.siteAgrees {} .scalar unrelated (.memory fixture.operation) none none true) =
      true := by decide +kernel

#print axioms unrelated_marshal_emissions

/-- Each resolved overload runs its lowered memory instruction on every execution state. -/
private theorem marshal_model_steps (fixture : Fixture)
    (member : fixture ∈ scalarSites.map Prod.fst) (body : Method) (pc : Nat)
    (environment : body.environment = {}) (link : body.linkAt pc = none)
    (args stack : List Safety.Value) (frame : Safety.Frame) (memory : Safety.Memory) :
    Safety.step body (.call fixture.method {}) pc args frame stack memory =
      Safety.step body (.memory fixture.operation) pc args frame stack memory := by
  have found := List.all_eq_true.mp marshal_resolutions.1 fixture member
  apply Safety.step_call_memory body pc args frame memory link _ rfl stack
  rw [environment]
  exact beq_iff_eq.mp found

#print axioms marshal_model_steps

end Tests.MarshalModels
