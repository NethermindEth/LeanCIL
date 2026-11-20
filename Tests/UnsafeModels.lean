import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import CIL.Safety.ResolutionFacts
import Tests.Support.RawDecoding

/-!
# Unsafe helper model tests

Each modelled `Unsafe` helper (`SizeOf`, the three reference comparisons and `SkipInit`)
resolves from its closed reference and checked layouts. Each resolving site retains its
call. A missing layout, a different layout identity or a forged declaration produces a hole.
-/

namespace Tests.UnsafeModels
open CIL CIL.Extraction CIL.Safety

/-- The `System.Runtime` type `name`. -/
private def runtimeType (name : String) : TypeExpr := .atom runtimeScope name
/-- `System.Int32`. -/
private def int32 : TypeExpr := runtimeType "System.Int32"

/-- `int Unsafe.SizeOf<element>()` as a call site instantiates it. -/
private def sizeOf (element : TypeExpr) : MethodRef :=
  { owner := unsafeOwner, name := name!"SizeOf", hasThis := false, genericArity := 1,
    returnType := int32, parameters := [], methodArguments := [element] }

/-- The struct `Fixture::Packet`, read from layout index 0. -/
private def packet : TypeExpr := .aggregate "Fixture::Packet" 0

/-- A sequential struct under `identity` of `words` 64-bit fields, `8 * words` bytes. -/
private def rawPacket (identity : String) (words : Nat) (byRefLike : Bool) : RawLayout :=
  { identity, explicit := false, packing := 0, declaredSize := 0,
    fields := List.replicate words { type := .unsigned64 }, byRefLike }

/-- Layouts whose entry 0 is `rawPacket identity words`, as `computeLayouts` computes it. -/
private def sized (words : Nat) (identity := "Fixture::Packet") (byRefLike := false) :
    LayoutEnvironment :=
  let raw := [rawPacket identity words byRefLike]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

-- Every fixture environment holds checked layouts, so a size the tests read is one
-- `layouts_validated` would admit.
example : LayoutsValid (sized 1).rawLayouts (sized 1).layouts := by decide +kernel
example : LayoutsValid (sized 3).rawLayouts (sized 3).layouts := by decide +kernel
example : LayoutsValid (sized 2 (byRefLike := true)).rawLayouts
    (sized 2 (byRefLike := true)).layouts := by decide +kernel
example : LayoutsValid (sized 3 "Fixture::Other").rawLayouts
    (sized 3 "Fixture::Other").layouts := by decide +kernel

/-- `Vector256<ulong>`, whose size is its width under every profile. -/
private def vector256 : TypeExpr :=
  .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1")
    (runtimeType "System.UInt64")

-- The size is the checked layout's: one reference, two environments, two sizes.
example : runtimeModel (sized 3) .call (sizeOf packet) = some (.constant 24) := by
  decide +kernel
example : runtimeModel (sized 1) .call (sizeOf packet) = some (.constant 8) := by
  decide +kernel
-- A by-ref-like struct inside the layouts has its checked size, as `sizeof` gives it.
example : runtimeModel (sized 2 (byRefLike := true)) .call (sizeOf packet) =
    some (.constant 16) := by decide +kernel
-- Primitive and vector widths are the element's own, in any environment.
example : runtimeModel {} .call (sizeOf int32) = some (.constant 4) := by decide +kernel
example : runtimeModel {} .call (sizeOf (runtimeType "System.UIntPtr")) = some (.constant 8) := by
  decide +kernel
example : runtimeModel {} .call (sizeOf (runtimeType "System.Char")) = some (.constant 2) := by
  decide +kernel
example : runtimeModel {} .call (sizeOf (runtimeType "System.Boolean")) = some (.constant 1) := by
  decide +kernel
example : runtimeModel {} .call (sizeOf vector256) = some (.constant 32) := by decide +kernel
-- The model reads no profile: a 256-bit element has its size and model under the scalar profile.
example : (runtimeModel {} .call (sizeOf vector256)).any (·.available .scalar) = true := by
  decide +kernel

-- Another owner, assembly or shape of the reference has no model.
example : runtimeModel {} .call { sizeOf int32 with
    owner := .atom "Other, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
      "System.Runtime.CompilerServices.Unsafe" } = none := by decide +kernel
example : runtimeModel {} .call { sizeOf int32 with owner := runtimeType "System.Unsafe" } =
    none := by decide +kernel
example : runtimeModel {} .call { sizeOf int32 with owner := .apply unsafeOwner int32 } =
    none := by decide +kernel
example : runtimeModel {} .call { sizeOf int32 with hasThis := true } = none := by decide +kernel
example : runtimeModel {} .call { sizeOf int32 with genericArity := 2 } = none := by
  decide +kernel
example : runtimeModel {} .call { sizeOf int32 with methodArguments := [int32, int32] } =
    none := by decide +kernel
example : runtimeModel {} .call { sizeOf int32 with parameters := [int32] } = none := by
  decide +kernel
example : runtimeModel {} .call { sizeOf int32 with returnType := runtimeType "System.Int64" } =
    none := by decide +kernel
example : runtimeModel {} .newobj (sizeOf int32) = none := by decide +kernel

-- An element without a size has no model: a generic parameter, a pointer, a class, a generic
-- class instance, a span, a floating-point type, a struct outside the layouts, and a struct
-- whose index holds another identity.
example : runtimeModel {} .call (sizeOf (.parameter 0)) = none := by decide +kernel
example : runtimeModel {} .call (sizeOf (.pointer int32)) = none := by decide +kernel
example : runtimeModel {} .call (sizeOf (.object runtimeScope "System.String")) = none := by
  decide +kernel
example : runtimeModel {} .call
    (sizeOf (.apply (.objectConstructor runtimeScope "System.Collections.Generic.List`1") int32)) =
    none := by decide +kernel
example : runtimeModel {} .call
    (sizeOf (.apply (.constructor runtimeScope "System.Span`1") int32)) = none := by
  decide +kernel
example : runtimeModel {} .call (sizeOf (runtimeType "System.Single")) = none := by
  decide +kernel
example : runtimeModel {} .call (sizeOf packet) = none := by decide +kernel
example : runtimeModel (sized 3 "Fixture::Other") .call (sizeOf packet) = none := by
  decide +kernel

/-- The open declaration of `int Unsafe.SizeOf<T>()`. -/
private def sizeOfDeclared : OpenSignature := { convention := 0x10, returnType := int32 }

/-- A call of `method` whose member declares `declared`. -/
private def site (method : MethodRef) (declared : OpenSignature := sizeOfDeclared) :
    RawInstruction :=
  let (name, result, parameters) :=
    if method.name == name!"SizeOf" then ("SizeOf", "System.Int32", "")
    else if method.name == name!"SkipInit" then ("SkipInit", "System.Void", "!!0&")
    else
      let name := if method.name == name!"AreSame" then "AreSame"
        else if method.name == name!"IsAddressLessThan" then "IsAddressLessThan"
        else "IsAddressGreaterThan"
      (name, "System.Boolean", "!!0&,!!0&")
  let owner := "System.Runtime.CompilerServices.Unsafe"
  ⟨0, 40, .call {
    method, name, declared,
    target := .external s!"{runtimeScope}::{result} {owner}::{name}({parameters})",
    typeArguments := method.methodArguments, parameterCount := method.parameters.length,
    returnsValue := method.returnType != .void }⟩

-- A SizeOf call retains its typed reference and refuses a literal of the same width.
example : runtimeCatalog.siteAgrees (sized 3) .scalar (site (sizeOf packet))
    (.call (sizeOf packet) {}) = true := by decide +kernel
example : runtimeCatalog.siteAgrees (sized 3) .scalar (site (sizeOf packet)) (.ldc_i4 24) =
    false := by decide +kernel

-- A member declared with another convention or result has no SizeOf model, so its call is refused.
example : [0x00, 0x11, 0x30, 0x50, 0x70].all (fun convention =>
    !runtimeCatalog.siteAgrees (sized 3) .scalar
      (site (sizeOf packet) { sizeOfDeclared with convention }) (.call (sizeOf packet) {})) =
    true := by decide +kernel
example : runtimeCatalog.siteAgrees (sized 3) .scalar
    (site (sizeOf packet) { sizeOfDeclared with returnType := .parameter 0 })
    (.call (sizeOf packet) {}) = false := by decide +kernel
example : runtimeCatalog.siteAgrees (sized 3) .scalar
    (site (sizeOf packet) { sizeOfDeclared with parameters := [.parameter 0] })
    (.call (sizeOf packet) {}) = false := by decide +kernel

/-- A method whose only instruction is `instruction`. -/
private def method (instruction : RawInstruction) : RawMethod :=
  { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [int32],
    initLocals := true, maxStack := 3, genericParameters := [], code := [instruction] }

/-- A body under 24-byte layouts whose only instruction is `emitted`, with no link. -/
private def emitting (emitted : CIL.Instruction) : CIL.Method :=
  { code := [emitted], locals := [], returnsValue := true, environment := sized 3 }

/-- A double vector has a runtime SizeOf call, while its raw object load decodes to a hole. -/
theorem double_vector_size_and_load :
    let head := TypeExpr.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1"
    let vector := TypeExpr.apply head (runtimeType "System.Double")
    let called := sizeOf vector
    let load := method ⟨0, 0x71, .type vector⟩
    runtimeModel {} .call called = some (.constant 16) ∧
      runtimeCatalog.siteAgrees {} .scalar (site called) (.call called {}) = true ∧
      methodCode .scalar {} [] [true] (method (site called)) = [.call called {}] ∧
      methodCode .scalar {} [] [true] load = [.unadmitted 0x71] ∧
      methodCode .scalar {} [] [true, false] { load with code := load.code ++ [⟨5, 0, .none⟩] } =
        [.unadmitted 0x71, .unadmitted 0] ∧
      ¬ ObjectOperandsValid load [true] (emitting (.ldobj vector)) := by decide +kernel
#print axioms double_vector_size_and_load

-- The body validator requires the modelled call at the SizeOf site.
example : RuntimeModelsAgree (method (site (sizeOf packet))) [true]
    (emitting (.call (sizeOf packet) {})) := by decide +kernel
example : ¬ RuntimeModelsAgree (method (site (sizeOf packet))) [true] (emitting (.ldc_i4 24)) := by
  decide +kernel

/-- `bool Unsafe.<name><element>(ref element, ref element)` as a call site instantiates it. -/
private def comparison (name : MetadataName) (element : TypeExpr) : MethodRef :=
  { owner := unsafeOwner, name, hasThis := false, genericArity := 1,
    returnType := runtimeType "System.Boolean", parameters := [.byref element, .byref element],
    methodArguments := [element] }

/-- `void Unsafe.SkipInit<element>(out element)` as a call site instantiates it. -/
private def skipInitOf (element : TypeExpr) : MethodRef :=
  { owner := unsafeOwner, name := name!"SkipInit", hasThis := false, genericArity := 1,
    returnType := .void, parameters := [.byref element], methodArguments := [element] }

/-- `Unsafe.AreSame`, which compares two references for identity. -/
private def areSame := comparison name!"AreSame"
/-- `Unsafe.IsAddressLessThan`, which orders two references by address. -/
private def isLess := comparison name!"IsAddressLessThan"
/-- `Unsafe.IsAddressGreaterThan`, which orders two references by address. -/
private def isGreater := comparison name!"IsAddressGreaterThan"

-- Each comparison resolves its relation, and SkipInit its model, for an element with a size.
example : runtimeModel {} .call (areSame int32) = some (.referenceCompare .same) := by
  decide +kernel
example : runtimeModel {} .call (isLess int32) = some (.referenceCompare .less) := by
  decide +kernel
example : runtimeModel {} .call (isGreater int32) = some (.referenceCompare .greater) := by
  decide +kernel
example : runtimeModel (sized 3) .call (areSame packet) = some (.referenceCompare .same) := by
  decide +kernel
example : runtimeModel {} .call (skipInitOf vector256) = some .skipInit := by decide +kernel
example : runtimeModel (sized 3) .call (skipInitOf packet) = some .skipInit := by decide +kernel

-- Another result, a parameter of another element, another arity or an element without a size
-- has no model; neither does SkipInit with a result or a second parameter.
example : runtimeModel {} .call { areSame int32 with returnType := int32 } = none := by
  decide +kernel
example : runtimeModel {} .call
    { isLess int32 with parameters := [.byref int32, .byref (runtimeType "System.Int64")] } =
    none := by decide +kernel
example : runtimeModel {} .call { isGreater int32 with genericArity := 2 } = none := by
  decide +kernel
example : runtimeModel {} .call (areSame (.parameter 0)) = none := by decide +kernel
-- The owner applied to a type argument names no helper, for every entry.
example : runtimeModel {} .call { areSame int32 with owner := .apply unsafeOwner int32 } =
    none := by decide +kernel
example : runtimeModel {} .call { isLess int32 with owner := .apply unsafeOwner int32 } =
    none := by decide +kernel
example : runtimeModel {} .call { isGreater int32 with owner := .apply unsafeOwner int32 } =
    none := by decide +kernel
example : runtimeModel {} .call { skipInitOf int32 with owner := .apply unsafeOwner int32 } =
    none := by decide +kernel
example : runtimeModel {} .call (areSame packet) = none := by decide +kernel
example : runtimeModel {} .call
    (skipInitOf (.apply (.constructor runtimeScope "System.Span`1") int32)) = none := by
  decide +kernel
example : runtimeModel {} .call
    { skipInitOf int32 with returnType := runtimeType "System.Boolean" } = none := by
  decide +kernel
example : runtimeModel {} .call
    { skipInitOf int32 with parameters := [.byref int32, .byref int32] } = none := by
  decide +kernel

/-- The open declaration of `void Unsafe.SkipInit<T>(out T)`. -/
private def skipInitDeclared : OpenSignature :=
  unsafeDeclaration (fun element => [.byref element]) (fun _ => .void)

/-- The comparison and SkipInit sites over `packet`, each with its member's declaration. -/
private def sameSite := site (areSame packet) unsafeComparisonDeclaration
/-- The less-than comparison at the packet type. -/
private def lessSite := site (isLess packet) unsafeComparisonDeclaration
/-- The greater-than comparison at the packet type. -/
private def greaterSite := site (isGreater packet) unsafeComparisonDeclaration
/-- The SkipInit call at the packet type. -/
private def skipSite := site (skipInitOf packet) skipInitDeclared

-- A comparison or SkipInit whose member declares another convention or signature has no model.
example : [0x00, 0x11, 0x30, 0x50, 0x70].all (fun convention =>
    !runtimeCatalog.siteAgrees (sized 3) .scalar
      (site (areSame packet) { unsafeComparisonDeclaration with convention })
      (.call (areSame packet) {})) = true := by decide +kernel
example : runtimeCatalog.siteAgrees (sized 3) .scalar
    (site (isLess packet)
      { unsafeComparisonDeclaration with parameters := [.byref (.parameter 0)] })
    (.call (isLess packet) {}) = false := by decide +kernel
example : runtimeCatalog.siteAgrees (sized 3) .scalar
    (site (skipInitOf packet) { skipInitDeclared with returnType := .parameter 0 })
    (.call (skipInitOf packet) {}) = false := by decide +kernel

-- Each helper must retain its call at a live site.
example : RuntimeModelsAgree (method sameSite) [true]
    (emitting (.call (areSame packet) {})) := by decide +kernel
example : ¬ RuntimeModelsAgree (method sameSite) [true] (emitting .ceq) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method lessSite) [true] (emitting .clt_un) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method greaterSite) [true] (emitting .cgt_un) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method skipSite) [true]
    (emitting .pop) := by decide +kernel

/-- The real decoder keeps the control call and emits the opcode's hole for the changed site.
    The live site also rejects the supplied instruction with the same stack effect. -/
private def refuses (control changed : RawInstruction) (reference : MethodRef)
    (layouts : LayoutEnvironment) (replacement : Instruction) : Bool :=
  let decode := fun environment raw =>
    (decodeRaw .scalar environment [] [true] (method raw) []).map Method.code
  decide (decode (sized 3) control = .ok [.call reference {}]) &&
    decide (siteClaim layouts none changed = .model) &&
    decide (decode layouts changed = liveHoleAt 0 changed.opcode) &&
    !runtimeCatalog.siteAgrees layouts .scalar changed replacement none true

/-- Substituting a method parameter for the declared Int32 result refuses SizeOf. -/
theorem forged_sizeOf_refused :
    let reference := sizeOf int32
    refuses (site reference) (site reference { sizeOfDeclared with returnType := .parameter 0 })
      reference (sized 3) (.call reference {}) = true := by decide +kernel

#print axioms forged_sizeOf_refused

/-- At Boolean, a generic result closes to the correct type but refuses the AreSame call. -/
theorem forged_areSame_refused :
    let reference := areSame (runtimeType "System.Boolean")
    let control := site reference unsafeComparisonDeclaration
    let forged := { unsafeComparisonDeclaration with returnType := .parameter 0 }
    refuses control (site reference forged) reference (sized 3) (.call reference {}) = true := by
  decide +kernel

#print axioms forged_areSame_refused

/-- An absent layout or a different identity at the same index refuses a local load at SizeOf. -/
theorem unsized_sizeOf_load_refused :
    let reference := sizeOf packet
    let missing := refuses (site reference) (site reference) reference
    missing {} (.ldloc 0) = true ∧
      missing { sized 3 with layouts := #[] } (.ldloc 0) = true ∧
      missing (sized 3 "Fixture::Other") (.ldloc 0) = true := by
  decide +kernel

#print axioms unsized_sizeOf_load_refused

/-- Removing the element's layout refuses a local store at SkipInit. -/
theorem unsized_skipInit_store_refused :
    refuses skipSite skipSite (skipInitOf packet) {} (.stloc 0) = true := by decide +kernel

#print axioms unsized_skipInit_store_refused

/-- A method that calls `Unsafe.SizeOf<packet>` under 24-byte layouts, with no link. -/
private def sizeBody : CIL.Method :=
  { code := [.call (sizeOf packet) {}], locals := [], returnsValue := true,
    environment := sized 3 }

/-- The frame of a call with no locals and no owned objects. -/
private def frame : Safety.Frame := { activation := 0, locals := [], owned := [] }

-- The call steps as `ldc.i4` of the checked size.
example (memory : CIL.Safety.Memory) :
    step sizeBody (.call (sizeOf packet) {}) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 24)] frame memory) := by
  rw [step_call_model (model := .constant 24) (link := rfl) (found := by decide +kernel)
    (direct := rfl)]
  rfl

cil_runtime_models Tests.UnsafeModels.sizeBody

-- The model fact states the size as the numeral `ldc.i4 24` pushes, so a branch on the result
-- simplifies as a branch on that literal does.
/--
info: Tests.UnsafeModels.sizeBody_model0 :
  runtimeModel sizeBody.environment CallOpcode.call (sizeOf packet) =
    some (RuntimeModel.constant 24)
-/
#guard_msgs (whitespace := lax) in #check sizeBody_model0

/-- A method that calls `Unsafe.SkipInit<int>`, with no link. -/
private def skipInitBody : CIL.Method :=
  { code := [.call (skipInitOf int32) {}], locals := [], returnsValue := false }

-- SkipInit pops a reference that forms and writes nothing; a scalar operand faults.
example (memory : CIL.Safety.Memory) :
    step skipInitBody (.call (skipInitOf int32) {}) 0 [] frame [.reference .null] memory =
      .ok (.next 1 [] frame memory) := by
  rw [step_call_model (model := .skipInit) (link := rfl) (found := by decide +kernel)
    (direct := rfl)]
  rfl
example (memory : CIL.Safety.Memory) :
    step skipInitBody (.call (skipInitOf int32) {}) 0 [] frame [.scalar (.i32 0)] memory =
      .error (.unsupported "Not a memory instruction") := by
  rw [step_call_model (model := .skipInit) (link := rfl) (found := by decide +kernel)
    (direct := rfl)]
  rfl

/-- Every single-overload Unsafe entry checks the same raw fields as its exact member binding. -/
theorem singleton_binding (key : MetadataName) (name result parameters : String)
    (declared : OpenSignature) (resolve : CallLayouts → MethodRef → Option RuntimeModel)
    (site : CallSite) :
    let owner := "System.Runtime.CompilerServices.Unsafe"
    (unsafeEntry key name result parameters declared resolve).bindsSite site =
      (site.declared == declared &&
        (site.name == name &&
         site.target == .external
           s!"{runtimeScope}::{result} {owner}::{name}({parameters})"
           && site.ownerArgumentCount == 0 && site.typeArguments == site.method.methodArguments &&
         site.parameterCount == site.method.parameters.length &&
         site.returnsValue == (site.returnType != .void))) := by
  simp [unsafeEntry, unsafeOperand, ModelEntry.single, ModelEntry.bindsSite, ModelEntry.select?,
    ModelEntry.select?.select, ModelOperand.bindsSite, Bool.and_assoc]

#print axioms singleton_binding

/-- A synthetic overload returns its parameter count as a distinguishable execution result. -/
private def countedOverload (parameters : List TypeExpr) (target : String) : ModelOverload :=
  { operand := .external (fun _ => { sizeOfDeclared with parameters }) "Count"
      (fun _ => some target),
    accepts := fun method => method.parameters == parameters,
    resolve := fun _ _ => some (.constant (BitVec.ofNat 32 parameters.length)) }

/-- A single reserved slot owns the zero- and one-parameter declarations. -/
private def countedEntry : ModelEntry :=
  { opcode := .call, owner := unsafeOwner, name := name!"Count", ownsName := true,
    overloads := [countedOverload [] "Count()", countedOverload [int32] "Count(Int32)"] }

/-- The raw call to one of the two Count overloads. -/
private def countedSite (parameters : List TypeExpr) (target : String) : CallSite :=
  let method := { sizeOf int32 with name := name!"Count", parameters }
  { method, name := "Count", declared := { sizeOfDeclared with parameters },
    target := .external target, returnsValue := true, parameterCount := parameters.length,
    typeArguments := method.methodArguments }

/-- Both signatures resolve. Crossing a target, a declaration or both refuses the closed call. -/
theorem overload_binding :
    let catalog : ModelCatalog := ⟨model_table% [countedEntry]⟩
    let zero := countedSite [] "Count()"
    let one := countedSite [int32] "Count(Int32)"
    let raw := fun site => RawInstruction.mk 0 40 (.call site)
    let needs := fun site => catalog.callRequirement (LayoutEnvironment.callLayouts {})
      .scalar none (raw site)
    let unknown := countedSite [int32, int32] "Count(Int32,Int32)"
    catalog.table.find {} .call zero.method = some (.constant 0) ∧
      catalog.table.find {} .call one.method = some (.constant 1) ∧
      needs zero = .instruction (.call zero.method {}) ∧
      needs one = .instruction (.call one.method {}) ∧
      needs { one with target := zero.target } = .hole 40 ∧
      needs { one with declared := zero.declared } = .hole 40 ∧
      needs { one with target := zero.target, declared := zero.declared } = .hole 40 ∧
      catalog.table.claims {} .call unknown.method = true ∧ needs unknown = .hole 40 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms overload_binding

/-- When two open declarations accept the same closed type, neither can supply its semantics. -/
theorem ambiguous_overload_refused :
    let site := countedSite [] "Count()"
    let entry := { countedEntry with overloads :=
      [countedOverload [] "Count()", countedOverload [] "Other()"] }
    entry.bindsSite site = false ∧ entry.resolve (LayoutEnvironment.callLayouts {}) site.method =
      none := by decide +kernel

#print axioms ambiguous_overload_refused

/-- Packing changes alignment independently of size. Raw storage survives a missing computed
    layout, and another identity at the same index supplies neither storage nor alignment. -/
theorem indexed_layout_reads :
    let packed := [{ rawPacket "Fixture::Packet" 1 false with packing := 1 }]
    let environment : LayoutEnvironment :=
      { rawLayouts := packed, layouts := (computeLayouts packed).getD #[] }
    let reader := environment.callLayouts
    let natural := (sized 1).callLayouts
    let rawOnly := LayoutEnvironment.callLayouts { rawLayouts := packed }
    reader.valueShape packet = .aggregate 8 ∧ natural.valueShape packet = .aggregate 8 ∧
      reader.alignment? packet = some 1 ∧ natural.alignment? packet = some 8 ∧
      rawOnly.storage packet = some (.field (.aggregate 0)) ∧ rawOnly.alignment? packet = none ∧
      reader.storage (.aggregate "Other" 0) = none ∧
      reader.alignment? (.aggregate "Other" 0) = none := by
  decide +kernel

#print axioms indexed_layout_reads

end Tests.UnsafeModels
