import CIL.Extraction.RuntimeModels
import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition

/-! # Runtime model admission and execution of Unsafe reinterpretations

The fixtures exercise reference formation and each representation that BitCast can move.
-/

namespace Tests.UnsafeReinterpretations
open CIL CIL.Extraction CIL.Safety

/-- The primitive byte type used by the scalar casts. -/
private def byteType := TypeExpr.atom runtimeScope "System.Byte"

/-- The Boolean result of the scalar BitCast overload. -/
private def boolean := TypeExpr.atom runtimeScope "System.Boolean"

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
private def vector (width : Nat) (element := "System.Byte") : TypeExpr :=
  .apply (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{width}`1")
    (.atom runtimeScope element)

/-- A closed static call together with the declaration and external identity of its member. -/
private def site (name : MetadataName) (text signature : String) (args : List TypeExpr)
    (parameter result : TypeExpr) (declared : OpenSignature) : CallSite :=
  let method : MethodRef :=
    { owner := unsafeOwner, name, hasThis := false, genericArity := args.length,
      parameters := [parameter], returnType := result, methodArguments := args }
  { method, name := text, declared, target := .external (runtimeScope ++ "::" ++ signature),
    typeArguments := args, parameterCount := 1, returnsValue := true }

/-- The open byref-to-byref cast closed over source and target. -/
private def asSite (source target : TypeExpr) :=
  site name!"As" "As" "!!1& System.Runtime.CompilerServices.Unsafe::As(!!0&)"
    [source, target] (.byref source) (.byref target)
    { convention := 16, parameters := [.byref (.parameter 0)],
      returnType := .byref (.parameter 1) }

/-- The byref and void-pointer overloads of AsRef. -/
private def asRefSite (element : TypeExpr) (pointer : Bool) :=
  let parameter := fun arg => if pointer then TypeExpr.pointer .void else .byref arg
  let operand := if pointer then "System.Void*" else "!!0&"
  site name!"AsRef" "AsRef" s!"!!0& System.Runtime.CompilerServices.Unsafe::AsRef({operand})"
    [element] (parameter element) (.byref element)
    (unsafeDeclaration (fun arg => [parameter arg]) TypeExpr.byref)

/-- The closed value cast from source to target. -/
private def cast (source target : TypeExpr) :=
  site name!"BitCast" "BitCast" "!!1 System.Runtime.CompilerServices.Unsafe::BitCast(!!0)"
    [source, target] source target
    { convention := 16, parameters := [.parameter 0], returnType := .parameter 1 }

/-- A span can be a target of As even when its element is a type variable. -/
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
  runtimeCatalog.siteAgrees (environment 2) .scalar ⟨0, 40, .call call⟩ emitted none none true

/-- One live call as the public raw-method decoder emits it. -/
private def decoded (call : CallSite) (env := environment 2) :=
  (Method.ofRaw? .scalar env [] [true] (caller call) []).map Method.code

/-- A single mutation of a resolving operand leaves precisely its opcode's hole. -/
private def refuses (control changed : CallSite) : Bool :=
  decide (decoded control = some [.call control.method {}]) &&
    decide (decoded changed = some [.unadmitted 40])

/-- Every pair of snapshot classes and the scalar overload, in a 16-byte layout. -/
private def values : List (CallSite × MemoryOp) :=
  [(cast byteType boolean, .bitcastByteBool),
   (cast packet packet, .bitcastValue (.aggregate 16) (.aggregate 16)),
   (cast (vector 128) (vector 128), .bitcastValue .vector128 .vector128),
   (cast packet (vector 128), .bitcastValue (.aggregate 16) .vector128),
   (cast (vector 128) packet, .bitcastValue .vector128 (.aggregate 16))]

/-- Scalar, vector and struct references as well as the unsized targets of As. -/
private def references : List (CallSite × MemoryOp) :=
  [byteType, vector 128, packet].map (fun element => (asSite element byteType, .asRef)) ++
  [span byteType, .array byteType, .object "Test" "Class", span (.parameter 0)].map
    (fun target => (asSite byteType target, .asRef))

/-- Every admitted call runs its expected operation and keeps its operand at the live site. -/
theorem resolved : (references ++ values).all (fun (call, operation) =>
    model call == some (.memory operation) && accepts call (.call call.method {}) &&
      !accepts call (.memory operation) && !accepts call .nop) := by decide +kernel
#print axioms resolved

/-- Both unsized As targets survive closing and decoding at a live site. -/
theorem unsizedTargets : [span byteType, TypeExpr.array byteType].all (fun target =>
    let call := asSite byteType target
    decide (decoded call = some [.call call.method {}])) := by decide +kernel
#print axioms unsizedTargets

/-- Both layouts compute successfully; BitCast reads their different snapshot sizes. -/
theorem checkedSizes : LayoutsValid (environment 2).rawLayouts (environment 2).layouts ∧
    LayoutsValid (environment 4).rawLayouts (environment 4).layouts ∧
    model (cast packet packet) (environment 4) =
      some (.memory (.bitcastValue (.aggregate 32) (.aggregate 32))) := by decide +kernel
#print axioms checkedSizes

/-- Only a root byref, pointer or variable excludes an As argument on either side. -/
theorem asExclusions : [TypeExpr.byref byteType, .pointer byteType, .parameter 0,
    .ownerParameter 0].all (fun arg => (model (asSite arg byteType)).isNone &&
      (model (asSite byteType arg)).isNone &&
      !accepts (asSite arg byteType) (.memory .asRef) &&
      !accepts (asSite byteType arg) (.memory .asRef)) := by decide +kernel
#print axioms asExclusions

/-- BitCast requires checked equal-width snapshots in both directions, or Byte to Boolean. -/
theorem bitCastExclusions :
    [vector 256, .aggregate "Other" 0, span byteType, .parameter 0, .pointer byteType,
     .object "Test" "Class", .array byteType, byteType].all (fun arg =>
      (model (cast arg packet)).isNone && (model (cast packet arg)).isNone) &&
    (model (cast boolean byteType)).isNone &&
    [("System.Single", 2, 128), ("System.Double", 4, 256),
     ("System.Double", 2, 128), ("System.Single", 4, 256)].all (fun (element, words, width) =>
      let arg := vector width element
      (model (cast arg packet) (environment words)).isNone &&
        (model (cast packet arg) (environment words)).isNone) := by decide +kernel
#print axioms bitCastExclusions

/-- The public decoder keeps both AsRef overloads' field and vector storage checks. -/
theorem asRefStorage : [false, true].all (fun pointer =>
    [byteType, vector 128, packet].all (fun arg =>
      decide (decoded (asRefSite arg pointer) = some [.memory .asRef])) &&
    [span byteType, TypeExpr.array byteType, .object "Test" "Class"].all (fun arg =>
      decide (decoded (asRefSite arg pointer) = some [.unadmitted 40]))) := by decide +kernel
#print axioms asRefStorage

/-- Each closed type refusal differs from a kept reference or snapshot operand in one argument. -/
theorem excludedOperands :
    [TypeExpr.byref byteType, .pointer byteType].all (fun arg =>
      refuses (asSite byteType byteType) (asSite byteType arg) &&
      refuses (asSite byteType byteType) (asSite arg byteType)) &&
    [vector 256, vector 128 "System.Single", vector 128 "System.Double",
      .aggregate "Other" 0, span byteType, .pointer byteType, .object "Test" "Class",
      .array byteType, byteType].all (fun arg =>
      refuses (cast (vector 128) packet) (cast arg packet) &&
      refuses (cast packet (vector 128)) (cast packet arg)) &&
    refuses (cast byteType boolean) (cast byteType byteType) := by decide +kernel
#print axioms excludedOperands

/-- Closed operands for mutations that run through the method decoder. -/
private def controls := [(asSite byteType packet, MemoryOp.asRef), (cast byteType boolean,
  MemoryOp.bitcastByteBool), (cast (vector 128) packet, .bitcastValue .vector128 (.aggregate 16))]

/-- The owner, receiver, generic arity and closed types identify each overload. -/
theorem exactReference : controls.all (fun (call, _) =>
    let method := call.method
    [ { method with owner := .apply unsafeOwner byteType },
      { method with owner := .atom "Other" "System.Runtime.CompilerServices.Unsafe" },
      { method with hasThis := true }, { method with genericArity := method.genericArity + 1 },
      { method with parameters := [] }, { method with returnType := .void } ].all
      (fun other => (runtimeModel (environment 2) .call other).isNone &&
        refuses call { call with method := other })) &&
    (runtimeModel {} .call { (asSite byteType packet).method with
      genericArity := 1, methodArguments := [byteType], parameters := [.object runtimeScope
        "System.Object"], returnType := byteType }).isNone := by decide +kernel
#print axioms exactReference

/-- A forged open return type or convention invalidates both the kept and the lowered form. -/
theorem exactDeclaration : controls.all (fun (call, operation) =>
    let altered := { call with declared.returnType := .void }
    refuses call altered &&
      refuses call { call with target := .external "Other" } &&
      refuses call { call with declared.parameters := [.ownerParameter 0] } &&
      !accepts altered (.call call.method {}) &&
      !accepts altered (.memory operation) &&
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

/-- On every stack and memory these calls step as the memory instruction they implement. -/
theorem callSteps (call : CallSite) (operation : MemoryOp)
    (listed : (call, operation) ∈ references ++ values) (pc : Nat)
    (args stack : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    let body : Method :=
      { code := [], locals := [], returnsValue := true, environment := environment 2 }
    step body (.call call.method {}) pc args frame stack memory =
      step body (.memory operation) pc args frame stack memory := by
  have found : (references ++ values).all
      (fun pair => model pair.1 == some (.memory pair.2)) := by decide +kernel
  have modelAt := List.all_eq_true.mp found _ listed
  dsimp only
  apply step_call_memory <;> first | rfl | exact eq_of_beq modelAt

#print axioms callSteps

end Tests.UnsafeReinterpretations
