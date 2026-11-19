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
      runtimeCatalog.siteAgrees {} .scalar (operand site) (.memory .byteOffset) none none true =
        false ∧
      runtimeCatalog.siteAgrees {} .scalar (operand site) .sub none none true = false := by
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
    (invalid ++ conventions).all (fun changed => decoded changed == some [.unadmitted 40]) =
      true := by decide +kernel

#print axioms byteOffset_bad_site

/-- Closed elements without a checked size decode to the call opcode's hole. -/
theorem byteOffset_unsized :
    let elements : List TypeExpr := [.apply (.constructor runtimeScope "System.Span`1") native,
      .pointer native, .byref native, .array native,
      .object runtimeScope "System.String", .atom runtimeScope "System.Single",
      .aggregate "Fixture::Pair" 0]
    elements.all (fun element => decoded (byteSite (byteOffset element)) ==
      some [.unadmitted 40]) = true := by decide +kernel

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
