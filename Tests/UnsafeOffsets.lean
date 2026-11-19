import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition

/-! Decoder evidence and checked execution of Unsafe reference offsets. -/

namespace Tests.UnsafeOffsets
open CIL CIL.Safety
section
open CIL.Extraction

/-- The signed native result of the byte displacement call. -/
private def native := TypeExpr.atom runtimeScope "System.IntPtr"

/-- The closed reference whose arguments are two references to the same element. -/
private def byteOffset (element : TypeExpr) : MethodRef :=
  { owner := unsafeOwner, name := name!"ByteOffset", hasThis := false, genericArity := 1,
    methodArguments := [element], returnType := native,
    parameters := [.byref element, .byref element] }

/-- The genuine MemberRef over the open method parameter. -/
private def byteSite (method : MethodRef) : CallSite :=
  { method, name := "ByteOffset", typeArguments := method.methodArguments, parameterCount := 2,
    returnsValue := true, declared :=
      { convention := 0x10, returnType := native,
        parameters := [.byref (.parameter 0), .byref (.parameter 0)] },
    target := .external (runtimeScope ++ "::System.IntPtr " ++
      "System.Runtime.CompilerServices.Unsafe::ByteOffset(!!0&,!!0&)") }

/-- The single call in a live raw body. -/
private def operand (site : CallSite) : RawInstruction := ⟨0, 40, .call site⟩

/-- The code the method decoder reconstructs at this call. -/
private def decoded (site : CallSite) (environment : LayoutEnvironment := {}) :=
  let raw : RawMethod :=
    { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
      attributes := 0, implementation := 0, returnType := native, parameters := [], locals := [],
      initLocals := true, maxStack := 2, genericParameters := [], code := [operand site] }
  (Method.ofRaw? .scalar environment [] [true] raw []).map Method.code

/-- The decoder keeps a well-formed ByteOffset and refuses either competing live emission. -/
theorem byteOffset_emission :
    let method := byteOffset native
    let site := byteSite method
    decoded site = some [.call method {}] ∧
      runtimeCatalog.siteAgrees {} .scalar (operand site) (.memory .byteOffset) none true =
        false ∧
      runtimeCatalog.siteAgrees {} .scalar (operand site) .sub none true = false := by
  decide +kernel

#print axioms byteOffset_emission

/-- Changing a single identity, signature or convention field yields the call opcode's hole. -/
theorem byteOffset_bad_site :
    let method := byteOffset native
    let site := byteSite method
    let invalid := [byteSite { method with owner := .apply unsafeOwner native },
      byteSite { method with owner := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe" },
      byteSite { method with hasThis := true }, byteSite { method with genericArity := 2 },
      { site with target := .external "Fixture" },
      { site with declared.returnType := .parameter 0 }]
    let conventions := [0x00, 0x11, 0x30, 0x50, 0x70].map fun convention =>
      { site with declared.convention := convention }
    (invalid ++ conventions).all (fun changed => decoded changed == none) =
      true := by decide +kernel

#print axioms byteOffset_bad_site

/-- Closed elements without a checked size decode to the call opcode's hole. -/
theorem byteOffset_unsized :
    let elements : List TypeExpr := [.apply (.constructor runtimeScope "System.Span`1") native,
      .pointer native, .byref native, .array native,
      .object runtimeScope "System.String", .atom runtimeScope "System.Single",
      .aggregate "Fixture::Pair" 0]
    elements.all (fun element => decoded (byteSite (byteOffset element)) ==
      none) = true := by decide +kernel

#print axioms byteOffset_unsized

/-- A free method parameter has no model and prevents the raw body from closing. -/
theorem byteOffset_free_parameter :
    let method := byteOffset (.parameter 0)
    runtimeModel {} .call method = none ∧ decoded (byteSite method) = none := by decide +kernel

#print axioms byteOffset_free_parameter

/-- ByteOffset accepts scalars, vectors and structs with checked storage. -/
theorem byteOffset_sized :
    let layout : RawLayout :=
      { identity := "Fixture::Pair", explicit := false, packing := 0, declaredSize := 0,
        fields := [{ type := .unsigned64 }], byRefLike := false }
    let environment : LayoutEnvironment :=
      { rawLayouts := [layout], layouts := (computeLayouts [layout]).getD #[] }
    let elements : List TypeExpr := [native, .aggregate layout.identity 0,
      .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
        (.atom runtimeScope "System.Byte")]
    elements.all (fun element => decoded (byteSite (byteOffset element)) environment ==
      some [.call (byteOffset element) {}]) = true := by decide +kernel

#print axioms byteOffset_sized

/-- A retained ByteOffset computes the same checked displacement as the memory instruction. -/
theorem byteOffset_step (body : Method) (pc : Nat) (args stack : List Safety.Value)
    (frame : Safety.Frame) (memory : Safety.Memory) (link : body.linkAt pc = none) :
    step body (.call (byteOffset native) {}) pc args frame stack memory =
      step body (.memory .byteOffset) pc args frame stack memory := by
  exact step_call_memory body pc args frame memory link (by rfl) rfl stack

#print axioms byteOffset_step

/-- A stored runtime integer or native integer. -/
private def atom (name : String) := TypeExpr.atom runtimeScope name

/-- The runtime types of the signed 32-bit, signed native and unsigned native offsets. -/
private def int := atom "System.Int32"
/-- The unsigned native offset. -/
private def unsigned := atom "System.UIntPtr"

/-- A checked aggregate at index zero, sized by the number of its 64-bit fields. -/
private def environment (words : Nat) : LayoutEnvironment :=
  let raw : List RawLayout := [{
    identity := "Fixture::Packet", explicit := false, packing := 0, declaredSize := 0,
    fields := List.replicate words { type := .unsigned64 } }]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

/-- One closed reference at a static arity-one helper. -/
private def reference (name : MetadataName) (element result : TypeExpr)
    (parameters : List TypeExpr) : MethodRef :=
  { owner := unsafeOwner, name, hasThis := false, genericArity := 1,
    methodArguments := [element], parameters, returnType := result }

/-- The closed reference and checked operation for each of the thirteen offset overloads. -/
private def overloads (element : TypeExpr) (width : Nat) : List (MethodRef × RuntimeModel) :=
  let source := TypeExpr.byref element
  let pointer := TypeExpr.pointer .void
  let closed := fun name type offset => reference name element type [type, offset]
  let elements : List (MethodRef × RuntimeModel) := [int, native, unsigned].flatMap fun offset =>
    let signed := offset != unsigned
    [(closed name!"Add" source offset, .memory (.add width signed)),
     (closed name!"Subtract" source offset, .memory (.add (subtractionStride width) signed))]
  let bytes : List (MethodRef × RuntimeModel) := [native, unsigned].flatMap fun offset =>
    [(closed name!"AddByteOffset" source offset, .memory (.add 1 (offset != unsigned))),
     (closed name!"SubtractByteOffset" source offset, .referenceSubtract)]
  elements ++ bytes ++ [
    (closed name!"Add" pointer int, .memory (.add width true)),
    (closed name!"Subtract" pointer int, .memory (.add (subtractionStride width) true)),
    (reference name!"ByteOffset" element native [source, source], .memory .byteOffset)]

/-- Each reference resolves to the operation of its checked width. -/
private def resolves (layouts : LayoutEnvironment) (element : TypeExpr) (width : Nat) : Bool :=
  (overloads element width).all fun (method, model) =>
    runtimeModel layouts .call method == some model

example : LayoutsValid (environment 1).rawLayouts (environment 1).layouts := by decide +kernel
example : LayoutsValid (environment 3).rawLayouts (environment 3).layouts := by decide +kernel
example : resolves {} int 4 := by decide +kernel
example : resolves {}
    (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1") int) 32 := by
  decide +kernel
example : resolves (environment 1) (.aggregate "Fixture::Packet" 0) 8 := by decide +kernel
example : resolves (environment 3) (.aggregate "Fixture::Packet" 0) 24 := by decide +kernel

/-- An offset helper refuses an unsupported element even when its result reads no element size. -/
private def excludes (element : TypeExpr) : Bool :=
  (overloads element 0).all fun (method, _) => (runtimeModel {} .call method).isNone

example : [TypeExpr.apply (.constructor runtimeScope "System.Span`1") int, .parameter 0,
    .pointer int, .byref int, .object runtimeScope "System.String", .aggregate "Fixture::Packet" 0,
    .array int, atom "System.Single", .void].all excludes := by decide +kernel


/-- The printed MemberRef name for the declared address or displacement type in this fixture. -/
private def memberType : TypeExpr → String
  | .byref (.parameter 0) => "!!0&"
  | .pointer .void => "System.Void*"
  | .atom _ name => name
  | _ => "unsupported"

/-- A MemberRef with the external target written by Cecil and its independently closed operand. -/
private def memberSite (method declared : MethodRef) : CallSite :=
  let name := if method.name == name!"Add" then "Add"
    else if method.name == name!"Subtract" then "Subtract"
    else if method.name == name!"AddByteOffset" then "AddByteOffset" else "SubtractByteOffset"
  let result := memberType declared.returnType
  let parameters := String.intercalate "," (declared.parameters.map memberType)
  let owner := "System.Runtime.CompilerServices.Unsafe"
  { method, name, declared :=
      { convention := 0x10, returnType := declared.returnType, parameters := declared.parameters }
    target := .external s!"{runtimeScope}::{result} {owner}::{name}({parameters})"
    typeArguments := method.methodArguments, parameterCount := 2, returnsValue := true }

/-- Each closed overload and its generic declaration occupy the same position in the fixture. -/
private def offsetSites (element : TypeExpr) (width : Nat) : List (CallSite × RuntimeModel) :=
  ((overloads element width).zip (overloads (.parameter 0) width)).filterMap
    fun ((method, model), (declared, _)) =>
      if method.name == name!"ByteOffset" then none else some (memberSite method declared, model)

/-- The stack operation executed by a retained displacement call. -/
private def loweredOffset : RuntimeModel → Instruction
  | .memory operation => .memory operation
  | .referenceSubtract => .sub
  | _ => .nop

/-- All twelve declarations retain their exact closed call and reject competing emissions. -/
theorem displacement_emissions :
    (offsetSites int 4).all (fun (site, model) =>
      decoded site == some [.call site.method {}] &&
      !runtimeCatalog.siteAgrees {} .scalar (operand site) (loweredOffset model) none true &&
      !runtimeCatalog.siteAgrees {} .scalar (operand site) .add none true) = true := by
  decide +kernel

#print axioms displacement_emissions

/-- An altered operand produces the call opcode's hole and refuses the former live lowering. -/
private def refusesOffset (site : CallSite) (model : RuntimeModel) : Bool :=
  decoded site == none &&
    !runtimeCatalog.siteAgrees {} .scalar (operand site) (loweredOffset model) none true

/-- Forging the open signature, convention, identity or receiver invalidates a resolving site. -/
theorem displacement_binding :
    (offsetSites int 4).all (fun (site, model) =>
      let method := site.method
      let closedAddress := method.returnType
      let forged := if closedAddress == .pointer .void then
          { site with declared.parameters := [closedAddress, .parameter 0] }
        else { site with declared.returnType := closedAddress }
      let changed := [forged, { site with method.owner := .apply unsafeOwner int },
        { site with method.owner := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe" },
        { site with method.hasThis := true }, { site with method.genericArity := 2 },
        { site with target := .external "Fixture" }]
      let conventions := [0x00, 0x11, 0x30, 0x50, 0x70].map fun convention =>
        { site with declared.convention := convention }
      (changed ++ conventions).all (refusesOffset · model)) = true := by decide +kernel

#print axioms displacement_binding

/-- Substituting another genuine overload's operand for the selected overload produces a hole. -/
theorem displacement_crossed_overloads :
    [name!"Add", name!"Subtract", name!"AddByteOffset", name!"SubtractByteOffset"].all (fun name =>
      let family := (offsetSites int 4).filter fun (site, _) => site.method.name == name
      match family with
      | (one, model) :: (other, _) :: _ =>
        refusesOffset { one with target := other.target } model &&
          refusesOffset { one with declared := other.declared } model
      | _ => false) = true := by decide +kernel

#print axioms displacement_crossed_overloads

/-- Replacing the element by a span leaves only the hole, including at an owned, linked call. -/
theorem span_displacements_refused :
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1") int
    (offsetSites span 0).all (fun (site, model) => refusesOffset site model &&
      !runtimeCatalog.siteAgrees {} .scalar (operand site) (.call site.method {})
        (some (.direct 0)) true) = true := by decide +kernel

#print axioms span_displacements_refused

/-- An unsized closed argument yields a hole and an unbound method parameter fails closure. -/
theorem unsized_displacement_code :
    let excluded : List TypeExpr := [.pointer int, .byref int, .array int, .void,
      .atom runtimeScope "System.Single", .object runtimeScope "System.String",
      .aggregate "Fixture::Absent" 0]
    excluded.all (fun element => (offsetSites element 0).all fun (site, model) =>
      refusesOffset site model) = true ∧
      (offsetSites (.parameter 0) 0).all (fun (site, _) => (decoded site).isNone) = true := by
  decide +kernel

#print axioms unsized_displacement_code

/-- An unknown Unsafe member can occupy a dead hole only and cannot retain a live call. -/
theorem unknown_offset_name :
    let control := byteSite (byteOffset native)
    let unknown := { control with method.name := name!"UnknownOffset", name := "UnknownOffset" }
    decoded control = some [.call control.method {}] ∧
      siteClaim {} none (operand unknown) = .refused ∧
      decoded unknown = none ∧
      runtimeCatalog.siteAgrees {} .scalar (operand unknown) (.unadmitted 40) = true ∧
      runtimeCatalog.siteAgrees {} .scalar (operand unknown) (.call unknown.method {})
        none true = false := by decide +kernel

#print axioms unknown_offset_name

/-- A direct call at pc zero with empty links. -/
private def body : CIL.Method := { code := [], locals := [], returnsValue := true }

/-- Each memory overload executes its checked offset operation on the caller's stack. -/
theorem memoryOverloadStep (method : MethodRef) (op : MemoryOp)
    (member : (method, RuntimeModel.memory op) ∈ overloads int 4) (frame : Safety.Frame)
    (stack : List CIL.Safety.Value) (memory : Safety.Memory) :
    step body (.call method {}) 0 [] frame stack memory =
      step body (.memory op) 0 [] frame stack memory := by
  apply step_call_memory (link := rfl) (direct := rfl)
  exact beq_iff_eq.mp (List.all_eq_true.mp (show resolves {} int 4 from by decide +kernel)
    (method, RuntimeModel.memory op) member)

#print axioms memoryOverloadStep

/-- SubtractByteOffset takes a native displacement under both signedness declarations. -/
private def byteSubtract (offset : TypeExpr) :=
  reference name!"SubtractByteOffset" int (.byref int) [.byref int, offset]

example (frame : Safety.Frame) (bits : W64) (base : ManagedReference) (memory : Safety.Memory)
    (rest : List CIL.Safety.Value) :
    let stack := .scalar (.i64 bits) :: .reference base :: rest
    step body (.call (byteSubtract native) {}) 0 [] frame stack memory =
      step body .sub 0 [] frame stack memory := by
  dsimp only
  rw [step_call_model (model := .referenceSubtract) (link := rfl) (found := by decide +kernel)
    (direct := rfl)]
  rfl

example (frame : Safety.Frame) (bits : W64) (base : ManagedReference) (memory : Safety.Memory)
    (rest : List CIL.Safety.Value) :
    let stack := .scalar (.i64 bits) :: .readOnlyReference base :: rest
    step body (.call (byteSubtract unsigned) {}) 0 [] frame stack memory =
      step body .sub 0 [] frame stack memory := by
  dsimp only
  rw [step_call_model (model := .referenceSubtract) (link := rfl) (found := by decide +kernel)
    (direct := rfl)]
  rfl

end

/-- Signed and unsigned native offsets both arrive as 64-bit words. The model and CIL sub
    move the same reference and preserve its readonly restriction for every word. -/
theorem subtractByteOffset_step (body : Method)
    (pc : Nat) (args : List Safety.Value) (frame : Frame) (rest : List Safety.Value)
    (memory : Safety.Memory) (base : ManagedReference) (offset : W64) (readOnly : Bool) :
    let reference := if readOnly then Safety.Value.readOnlyReference base else .reference base
    let stack := .scalar (.i64 offset) :: reference :: rest
    modelStep (some .referenceSubtract) body pc frame stack memory =
      step body .sub pc args frame stack memory := by
  cases readOnly <;> rfl

#print axioms subtractByteOffset_step

end Tests.UnsafeOffsets
