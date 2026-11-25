import CIL.Extraction.DecodedDefinition
import CIL.InstructionEquations
import CIL.Safety.ResolutionFacts
import CIL.Safety.SymbolicExecution
import Tests.BodyDecoding
import Tests.Support.ModelOperands

/-!
# Decoded method tests

Bodies built by `Tests.BodyEncoding.encodeBody` and by hand over `Tests.MetadataWorld` must
decode through `Method.ofBody?` to the method their bytes denote: the code `Instruction.ofRaw`
gives, locals initialized by the flag in the bytes rather than the definition's, and the code of
the bytes rather than the definition's. A stored argument takes a home. An instruction outside
the admitted families at a live site prevents method construction. A body the
check refuses, or one with an argument instruction naming an undeclared argument, gives no
method, and neither does a program with such a body. A method defined by `cil_decoded_method`
is the decoder's method, written as literals its facts and stepping read, with a zero-initialized
struct local written as `List.replicate size 0` so frame entry gives the term a caller's
hypothesis about making that local names. A call decodes to the method its operand names, with
the target the supplied link table gives its pc, and the call check rejects a link that names
another method.
-/

namespace Tests.DecodedMethod

open CIL CIL.Extraction Tests.BodyEncoding Tests.BodyDecoding Tests.MetadataWorld

/-- The mask for a fixture whose entire body is live. -/
def allLive (raw : RawMethod) : List Bool := raw.code.map fun _ => true

/-- The method of the bytes of `body` against the definition `original`, with no layouts. -/
private def decoded (body : Option BodyEvidence) (original : RawMethod) : Option Method :=
  body.bind fun body => Method.ofBody? .scalar {} [] (allLive original) body original []

/-- `ldc.i4.1; ldc.i4.2; add; ret`. -/
private def addRaw : RawMethod :=
  method 8 false [] [instr 0 0x17, instr 1 0x18, instr 2 0x58, instr 3 0x2A]

/-- `ldc.i4.1; ldc.i4.2; sub; ret`. -/
private def subRaw : RawMethod :=
  method 8 false [] [instr 0 0x17, instr 1 0x18, instr 2 0x59, instr 3 0x2A]

/-- The frame both bodies declare: no locals, no homes, no arguments, no return value. -/
private def frame (code : List Instruction) : Method :=
  { code := code, locals := [],
    declared := { parameters := [], returnType := .void, initLocals := false },
    returnsValue := false }

/-- The tiny add body decodes to its code and its declared frame. -/
theorem add_decodes :
    decoded (encodeBody pin addRaw) addRaw = some (frame [.ldc_i4 1, .ldc_i4 2, .add, .ret]) := by
  cil_kernel_rfl
#print axioms add_decodes

/-- The unsafe-call certificate requires a mask entry for every instruction. -/
theorem decoded_missing_mask :
    let source := { addRaw with code := [instr 0 0] }
    ¬ UnsafeCallsValid source [] (methodCode .scalar {} [] [] source) := by decide +kernel
#print axioms decoded_missing_mask

/-- A span reset decodes to `initobj`, and object admission refuses it without the address of a
    local or parameter of its type before it. -/
theorem decoded_unbound_span_reset :
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1") uint32
    let source := { addRaw with code := [instr 0 0xfe15 (.type span)] }
    let code := methodCode .scalar {} [] [true] source
    code = [.initobj span] ∧ objectSites source [true] (frame code) = none := by
  exact ⟨rfl, rfl⟩
#print axioms decoded_unbound_span_reset

/-- A raw static access uses the owner, slot, held type and name encoded by its token. -/
private def fieldSite (opcode : Nat) (field : FieldRef) : RawInstruction :=
  instr 0 opcode (.field field.owner field.index field.type field.name true)

/-- The decoder binds a single field instruction under its profile and RVA evidence. -/
private def fieldCode (opcode : Nat) (field : FieldRef)
    (sites : List (Nat × StaticFieldSite) := []) (profile := FeatureProfile.scalar) :
    Except RawDecodeError (List Instruction) :=
  let source := { addRaw with code := [fieldSite opcode field], staticFields := sites }
  (decodeRaw profile {} [] [true] source []).map Method.code

/-- The constant requires the exact runtime field and a little-endian profile. -/
theorem endianFieldDecodes :
    let field := littleEndianField
    let wrong := [{ field with owner := .atom "Foreign" "System.BitConverter" },
      { field with owner := .atom runtimeScope "System.Other" },
      { field with name := name!"Other" }, { field with type := int32 }]
    fieldCode 126 field = .ok [.ldc_i4 1] ∧
      wrong.all (fun other => decide (fieldCode 126 other = liveHoleAt 0 126)) ∧
      fieldCode 126 field [] { littleEndian := false } = liveHoleAt 0 126 := by
  decide +kernel

#print axioms endianFieldDecodes

/-- Both RVA opcodes bind the descriptor's field and require its complete declared storage. -/
theorem rvaFieldsDecode :
    let field : FieldRef := ⟨.object "Fixture" "Tables", 1, .atom "Fixture" "Data", name!"Words"⟩
    let data : StaticFieldSite :=
      ⟨{ identity := 3, field, bytes := [1, 2, 3, 4], alignment := 4 }, some 4⟩
    [(127, Instruction.ldsflda field), (208, .ldtoken (.field field))].all (fun (opcode, op) =>
      let sites := [(0, data)]
      let wrong := [{ field with owner := .object "Other" "Tables" },
        { field with owner := .object "Fixture" "Other" }, { field with name := name!"Other" },
        { field with type := int32 }, { field with index := 0 }]
      decide (fieldCode opcode field sites = .ok [op]) &&
      wrong.all (fun other => decide (fieldCode opcode other sites = liveHoleAt 0 opcode)) &&
      decide (fieldCode opcode field [] = liveHoleAt 0 opcode) &&
      decide (fieldCode opcode field [(0, { data with rvaSize := some 3 })] =
        liveHoleAt 0 opcode)) = true := by
  decide +kernel

#print axioms rvaFieldsDecode

/-- The fixture's unsigned word field is initialized to seven. -/
private def bias : StaticDescriptor :=
  { identity := 9, field := ⟨.object ownIdentity "Statics", 1, uint32, name!"Bias"⟩,
    bytes := [7, 0, 0, 0], scalar := some false,
    initializer := some { method := 0, arguments := [], literal := some (.i32 7) } }

/-- The checked inputs of a static access retain its descriptor in the resulting method. -/
private def staticResult (opcode : Nat) (operand : FieldRef) (descriptor : StaticDescriptor)
    (hasVolatilePrefix := false) (owner := addRaw.owner) (environment : LayoutEnvironment := {}) :
    Except MethodDecodeError Method :=
  let value := if opcode == 128 then [instr 0 0x17] else []
  let prefixes := if hasVolatilePrefix then [instr value.length 0xfe13] else []
  let offset := value.length + 2 * prefixes.length
  let access := { fieldSite opcode operand with offset }
  let code := value ++ prefixes ++ [access, instr (offset + 5) 0x2a]
  let result : TypeExpr := match opcode with
    | 127 => .byref operand.type
    | 128 => .void
    | _ => operand.type
  let source := { addRaw with
    code, owner, returnType := result,
    staticFields := [(value.length + prefixes.length, ⟨descriptor, none⟩)] }
  let arguments : RawArguments :=
    { arguments := [], locals := [], code := code.map fun _ => .other }
  Method.ofClosed? .scalar environment [] (allLive source) source arguments

/-- A load and an address use their exact field, and the method retains its initializer. -/
theorem ordinaryStaticsDecode :
    let field := bias.field
    let descriptor := bias
    [(126, Instruction.ldsfld field), (127, .ldsflda field)].all
      (fun (opcode, op) =>
        match staticResult opcode field descriptor with
        | .ok method => method.code == [op, .ret] && method.staticSites == [(0, descriptor)]
        | .error _ => false) = true := by
  decide +kernel

#print axioms ordinaryStaticsDecode

/-- A reachable store to a static field is refused at the store, with a matching descriptor. -/
theorem ordinaryStaticStoreRefused :
    (match staticResult 128 bias.field bias with
     | .error (.liveHole pc opcode) => pc == 1 && opcode == 128
     | _ => false) = true := by
  decide +kernel

#print axioms ordinaryStaticStoreRefused

/-- A mismatched value leaves a hole at the access. A volatile prefix is itself a live hole. -/
theorem ordinaryStaticRefusals :
    let field := bias.field
    let descriptor := bias
    let init := bias.initializer.getD { method := 0, arguments := [] }
    let changed := { init with literal := some (.i32 8) }
    let wrongLiteral := { descriptor with initializer := some changed }
    let wrongCallee := { descriptor with initializer := some { init with method := 1 } }
    let other := { field with owner := .object "Foreign" "Statics" }
    [126, 127, 128].all (fun opcode =>
      let pc := if opcode == 128 then 1 else 0
      let wrong := [{ field with name := name!"Other" }, { field with index := 0 },
        { field with owner := .object ownIdentity "Other" }, { field with type := int32 }]
      let errorAt := fun (result : Except MethodDecodeError Method) pc =>
        match result with
        | .error error => error == .liveHole pc opcode
        | .ok _ => false
      wrong.all (fun operand => errorAt (staticResult opcode operand descriptor) pc) &&
      errorAt (staticResult opcode other { descriptor with field := other }) pc &&
      errorAt (staticResult opcode field wrongLiteral) pc &&
      errorAt (staticResult opcode field wrongCallee) pc &&
      (match staticResult opcode field descriptor true with
       | .error (.liveHole index 0xfe13) => index == pc
       | _ => false)) = true := by
  decide +kernel

#print axioms ordinaryStaticRefusals

/-- The load operand names exactly the field in the descriptor under test. -/
private def ordinaryLoad (descriptor : StaticDescriptor) (owner := addRaw.owner)
    (environment : LayoutEnvironment := {}) : Except RawDecodeError (List Instruction) :=
  (staticResult 126 descriptor.field descriptor (owner := owner) (environment := environment))
    |>.map Method.code |>.mapError .method

/-- Ordinary static storage requires byte alignment. -/
theorem ordinaryStaticAlignmentRefused :
    ordinaryLoad { bias with alignment := 2 } = liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticAlignmentRefused

/-- A non-opaque static load requires an initializer for its bytes. -/
theorem ordinaryStaticMissingInitializerRefused :
    ordinaryLoad { bias with initializer := none } = liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticMissingInitializerRefused

/-- Seven fits in one byte, but the declared unsigned word requires four. -/
theorem ordinaryStaticWidthRefused :
    ordinaryLoad { bias with bytes := [7] } = liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticWidthRefused

/-- The unsigned word field refuses a descriptor that requests signed extension. -/
theorem ordinaryStaticSignednessRefused :
    ordinaryLoad { bias with scalar := some true } = liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticSignednessRefused

/-- A static field on an aggregate owner requires that aggregate's assembly to match. -/
theorem ordinaryStaticAggregateOwnerRefused :
    let localSite := { bias with field.owner := .aggregate (ownIdentity ++ "::Statics") 0 }
    let foreignSite := { localSite with field.owner := .aggregate "Foreign::Statics" 0 }
    ordinaryLoad localSite = .ok [.ldsfld localSite.field, .ret] ∧
      ordinaryLoad foreignSite = liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticAggregateOwnerRefused

/-- Matching empty assembly names cannot establish ownership of a static field. -/
theorem ordinaryStaticEmptyScopeRefused :
    ordinaryLoad { bias with field.owner := .object "" "Statics" } "::Caller" =
      liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticEmptyScopeRefused

/-- A caller-bound field supports a load with zero placeholder bytes and no address or store. -/
theorem opaqueStaticAccess :
    let field := bias.field
    let site := { bias with bytes := [0, 0, 0, 0], initializer := none, opaqueValue := true }
    let refusal := fun opcode (descriptor : StaticDescriptor) =>
      match staticResult opcode field descriptor with
      | .error (.liveHole pc raw) => pc == (if opcode == 128 then 1 else 0) && raw == opcode
      | _ => false
    ((staticResult 126 field site).isOk &&
      refusal 126 { site with bytes := [1, 0, 0, 0] } && refusal 127 site && refusal 128 site) =
      true := by
  decide +kernel

#print axioms opaqueStaticAccess

/-- The decoder preserves a call initializer's index so the program check executes that callee. -/
theorem staticInitializerCallee :
    let check := fun callee =>
      let site := { bias with initializer := some { method := callee, arguments := [] } }
      match staticResult 126 bias.field site with
      | .ok method =>
        let seven : Method := { code := [.ldc_i4 7, .ret], locals := [], returnsValue := true }
        some (method.staticSites == [(0, site)], decide (StaticValuesValid [method, seven]))
      | .error _ => none
    check 1 = some (true, true) ∧ check 0 = some (true, false) := by
  decide +kernel

#print axioms staticInitializerCallee

/-- The decoder's code for `code` with RVA `sites`, reachable pcs and the link table. -/
private def staticCode (code : List RawInstruction) (sites : List (Nat × StaticFieldSite))
    (reachable : List Bool) (links : List (Nat × Link) := []) :
    Except RawDecodeError (List Instruction) :=
  (decodeRaw .scalar {} links reachable { addRaw with code, staticFields := sites } []).map Method.code

/-- A volatile prefix makes the following ordinary load a hole even when only the load is live. -/
theorem ordinaryStaticVolatileLoadRefused :
    let sites := [(1, ⟨bias, none⟩)]
    let load := { fieldSite 126 bias.field with offset := 2 }
    staticCode [instr 0 0, load] sites [false, true] = .ok [.unadmitted 0, .ldsfld bias.field] ∧
      staticCode [instr 0 0xfe13, load] sites [false, true] = liveHoleAt 1 126 := by decide +kernel
#print axioms ordinaryStaticVolatileLoadRefused

/-- Each RVA guard refuses on its own: data at a platform field, an empty, misaligned,
    initialized, scalar or opaque blob, another field opcode, a prefix and a link at the pc. -/
theorem rvaGuardsRefuse :
    let field : FieldRef := ⟨.object "Fixture" "Tables", 1, .atom "Fixture" "Data", name!"Words"⟩
    let data : StaticFieldSite :=
      { descriptor := { identity := 3, field, bytes := [1, 2, 3, 4], alignment := 4 },
        rvaSize := some 4 }
    let refused : List StaticFieldSite :=
      [{ descriptor := { data.descriptor with bytes := [] }, rvaSize := some 0 },
      { data with descriptor.alignment := 3 }, { data with descriptor.alignment := 16 },
      { data with descriptor.initializer := some { method := 0, arguments := [] } },
      { data with descriptor.scalar := some false }, { data with descriptor.opaqueValue := true }]
    let load := { fieldSite 127 field with offset := 2 }
    fieldCode 126 littleEndianField [(0, data)] = liveHoleAt 0 126 ∧
      refused.all (fun other => decide (fieldCode 127 field [(0, other)] = liveHoleAt 0 127)) ∧
      [126, 128].all (fun opcode =>
        decide (fieldCode opcode field [(0, data)] = liveHoleAt 0 opcode)) ∧
      staticCode [instr 0 0x00, load] [(1, data)] [false, true] =
        .ok [.unadmitted 0, .ldsflda field] ∧
      staticCode [instr 0 0xFE13, load] [(1, data)] [false, true] = liveHoleAt 1 127 ∧
      staticCode [fieldSite 127 field] [(0, data)] [true] [(0, .direct 0)] = liveHoleAt 0 127 := by
  decide +kernel

#print axioms rvaGuardsRefuse

/-- A field handle produces a span only at the open declaration and the matching closed width. -/
theorem staticSpanDecodes :
    let owner := "System.Runtime.CompilerServices.RuntimeHelpers"
    let name := "CreateSpan"
    let handle := "System.RuntimeFieldHandle"
    let span := TypeExpr.apply (.constructor runtimeScope "System.ReadOnlySpan`1")
    let site : CallSite := {
      method := {
        owner := .atom runtimeScope owner, name := name!"CreateSpan", hasThis := false,
        genericArity := 1, returnType := span int32, parameters := [.atom runtimeScope handle],
        methodArguments := [int32] },
      name, typeArguments := [int32], parameterCount := 1, returnsValue := true,
      declared := {
        convention := 16, returnType := span (.parameter 0),
        parameters := [.atom runtimeScope handle] },
      target := .external
        s!"{runtimeScope}::System.ReadOnlySpan`1<!!0> {owner}::{name}({handle})" }
    let wide := TypeExpr.primitive .uint64
    Tests.ModelOperands.checks site ∧
      runtimeModel {} .call site.method = some (.memory (.createSpan 4)) ∧
      Tests.ModelOperands.decoded { site with method.methodArguments := [wide] } =
        liveHoleAt 0 40 := by
  decide +kernel

#print axioms staticSpanDecodes

/-- The argument check requires one mask entry for every raw instruction. -/
theorem mismatched_mask_refused :
    (Method.ofRaw? .scalar {} [] [true, true, true] addRaw []).isNone &&
      (Method.ofRaw? .scalar {} [] [true, true, true, true, false] addRaw []).isNone := by
  decide +kernel
#print axioms mismatched_mask_refused

/-- A dead constrained call whose target is an ordinary static method. -/
private def ordinaryStaticRaw := method 8 false [] [instr 0 42, instr 1 22,
  instr 2 0xFE16 (.type objectType), instr 8 40 (.call writeLineSite), instr 13 42]

/-- A dead tail call returning an integer in a void method. -/
private def wrongTailRaw := method 8 false [] [instr 0 42, instr 1 0xFE14,
  instr 3 40 (.call getSite), instr 8 42]

/-- An unreachable indirect tail call returning an integer from a void method. -/
private def wrongIndirectTailRaw := method 8 false [] [instr 0 42, instr 1 0xFE14,
  instr 3 41 (.indirectCall int32 [] false false 0), instr 8 42]

/-- A static method without a virtual interface slot cannot take a constrained receiver. -/
theorem ordinary_static_prefix_refused :
    (Method.ofRaw? .scalar {} [] [true, false, false, false, false] ordinaryStaticRaw []).isNone &&
      !decide (MethodShapeValid ordinaryStaticRaw (frame [])) := by
  decide +kernel
#print axioms ordinary_static_prefix_refused

/-- An unreachable tail transfer still returns the enclosing method's declared result. -/
theorem tail_result_mismatch_refused :
    (Method.ofRaw? .scalar {} [] [true, false, false, false] wrongTailRaw []).isNone &&
      !decide (MethodShapeValid wrongTailRaw (frame [])) := by
  decide +kernel
#print axioms tail_result_mismatch_refused

/-- Refusal by the closed method shape excludes every full evidence record for these bodies. -/
theorem dead_call_evidence_refused (item : MethodEvidence) (emitted : Method)
    (layouts : List RawLayout) (computed : Array ComputedLayout) (pins : List AssemblyPin)
    (platform : PlatformTable) (items : List MethodEvidence) (imports : List ImportSlot)
    (body : item.closed = ordinaryStaticRaw ∨ item.closed = wrongTailRaw ∨
      item.closed = wrongIndirectTailRaw) :
    ¬ MethodEvidenceValid layouts computed pins platform items imports item emitted := by
  intro valid
  have prefixes := valid.2.2.2.2.2.2.1.2.2.2.2
  rcases body with invalid | invalid | invalid <;> rw [invalid] at prefixes <;>
    exact absurd prefixes (by decide +kernel)
#print axioms dead_call_evidence_refused

/-- Bytes that decode to either invalid body cannot construct a method. -/
theorem dead_call_bytes_refused {pins : List AssemblyPin} {platform : PlatformTable}
    {assembly : AssemblyPin} {imports : BodyImports}
    {body : BodyEvidence} {raw : RawMethod} {signature : String}
    (decodes : BodyDecodes pins platform assembly body raw [] signature imports)
    (invalid : raw = ordinaryStaticRaw ∨ raw = wrongTailRaw) :
    Method.ofBody? .scalar {} [] (raw.code.mapIdx fun pc _ => pc == 0) body raw [] = none := by
  rw [Method.ofBody?_of_decodes decodes]
  rcases invalid with rfl | rfl <;> decide +kernel
#print axioms dead_call_bytes_refused

/-- Branch entry must include the readonly modifier when constructing a method from raw code. -/
theorem raw_prefix_entry_refused :
    let raw := method 8 false [] [instr 0 20, instr 1 22, instr 2 43 (.target 4),
      instr 4 0xFE1E, instr 6 143 (.type int32), instr 11 38, instr 12 42]
    (Method.ofRaw? .scalar {} [] (allLive raw) raw []).isNone = true := by
  decide +kernel
#print axioms raw_prefix_entry_refused

/-- An unordered switch may target the prefix and return, but cannot enter the element address. -/
theorem raw_switch_prefix_entry :
    let raw := fun targets => [instr 0 69 (.targets targets), instr 16 0xFE1E,
      instr 18 143 (.type int32), instr 23 42]
    rawPrefixesValid .void (raw [3, 1, 3, 2^128]) && !rawPrefixesValid .void (raw [3, 2, 3]) := by
  decide +kernel
#print axioms raw_switch_prefix_entry

/-- A malformed prefix anywhere in a method precludes both decoding and shape evidence. -/
theorem invalid_prefix_sequences_refused :
    let modifier := instr 0 0xFE12 (.integer 1)
    let load := instr 3 0x4A
    let add := instr 3 0x58
    let readOnly := instr 0 0xFE1E
    let owner := TypeExpr.object "T" "Account"
    let field := instr 3 123 (.field owner 0 (.primitive .int32) name!"n" false)
    let address := instr 4 143 (.type owner)
    let ret := instr 8 42
    let cases := [[modifier, add], [instr 0 0xFE12 (.integer 3), field], [instr 0 0xFE12, load],
      [instr 0 0xFE13, load], [instr 0 0xFE14, add], [instr 0 0xFE16 (.type owner), add],
      [instr 0 0xFE19 (.integer 7), add], [instr 0 0xFE19 (.integer 255), field],
      [instr 0 0xFE1E (.integer 3), address], [readOnly, ret], [readOnly, readOnly, address],
      [modifier, instr 3 0xFE13, load], [ret, readOnly], [ret, instr 1 0xFE19 (.integer 4), field],
      [modifier, instr 3 0xFE17 (.integer 1)], [modifier, instr 3 0x4A (.integer 1)]]
    cases.all (fun code =>
      let raw := { addRaw with code }
      (Method.ofRaw? .scalar {} [] (allLive raw) raw []).isNone &&
        !decide (MethodShapeValid raw (frame []))) = true := by
  decide +kernel
#print axioms invalid_prefix_sequences_refused

/-- An explicit receiver cannot be decoded as an additional implicit argument. -/
theorem explicit_this_has_no_raw_method :
    let raw := { addRaw with explicitThis := true }
    (Method.ofRaw? .scalar {} [] (allLive raw) raw []).isNone = true := by
  decide +kernel
#print axioms explicit_this_has_no_raw_method

/-- Matching EXPLICITTHIS metadata is refused even when the body bytes are valid. -/
theorem explicit_this_has_no_body :
    ((encodeBody pin { addRaw with explicitThis := true }).map fun body =>
      (checkBody body { addRaw with explicitThis := true } []).toBool) = some false := by
  decide +kernel
#print axioms explicit_this_has_no_body

/-- The method of the sub bytes against the add definition is the sub method: `Method.ofBody?`
    reads no instruction of the definition. -/
theorem code_read_from_bytes :
    decoded (encodeBody pin subRaw) addRaw = some (frame [.ldc_i4 1, .ldc_i4 2, .sub, .ret]) := by
  cil_kernel_rfl
#print axioms code_read_from_bytes

/-- `ldarg.0; ldarg.1; add; ret` over two `uint64` parameters, returning `uint64`. -/
def addArgumentsRaw : RawMethod :=
  { method 8 false [] [instr 0 0x02, instr 1 0x03, instr 2 0x58, instr 3 0x2A] with
    parameters := [uint64, uint64], returnType := uint64 }

/-- The bytes `12 02 03 58 2A` decode to the two argument loads, the add and the return. -/
theorem add_arguments_decode :
    (encodeBody pin addArgumentsRaw).map (·.bytes) = some [0x12, 0x02, 0x03, 0x58, 0x2A] ∧
      decoded (encodeBody pin addArgumentsRaw) addArgumentsRaw = some
        { code := [.ldarg 0, .ldarg 1, .add, .ret], locals := [],
          declared :=
            { parameters := [uint64, uint64], returnType := uint64, initLocals := false },
          returnsValue := true } := by
  constructor <;> cil_kernel_rfl
#print axioms add_arguments_decode

/-- `ldc.i4.1; stloc.0; ldloc.0; ret` over one `uint32` local, with the given init flag. -/
private def localRaw (initLocals : Bool) : RawMethod :=
  method 8 initLocals [uint32] [instr 0 0x17, instr 1 0x0A, instr 2 0x06, instr 3 0x2A]

/-- The locals start at zero exactly when the bytes set the init flag, whatever the definition
    says. -/
theorem locals_initialized_by_the_bytes :
    (decoded (encodeBody pin (localRaw true)) (localRaw false)).map (·.locals) =
        some [.i32 0] ∧
      (decoded (encodeBody pin (localRaw false)) (localRaw true)).map (·.locals) =
        some [.unmodeled] := by
  constructor <;> cil_kernel_rfl
#print axioms locals_initialized_by_the_bytes

/-- `ldc.i4.8; localloc; pop; ret` with no locals and the given init flag. -/
private def allocationRaw (initLocals : Bool) : RawMethod :=
  method 8 initLocals [] [instr 0 0x1E, instr 1 0xFE0F, instr 3 0x26, instr 4 0x2A]

/-- Bytes without localsinit decode `localloc` under a declared signature whose init flag is
    false, whichever flag the definition carries, so the allocation is not zeroed. -/
theorem localloc_flag_read_from_the_bytes :
    (decoded (encodeBody pin (allocationRaw false)) (allocationRaw false)).map
        (fun method => (method.code, method.declared.initLocals)) =
      some ([.ldc_i4 8, .localloc, .pop, .ret], false) ∧
    (decoded (encodeBody pin (allocationRaw false)) (allocationRaw true)).map
        (fun method => (method.code, method.declared.initLocals)) =
      some ([.ldc_i4 8, .localloc, .pop, .ret], false) := by
  constructor <;> cil_kernel_rfl
#print axioms localloc_flag_read_from_the_bytes

/-- `ldc.i4.1; starg.s index; ret` over one `uint32` parameter. -/
private def storeRaw (index : Nat) : RawMethod :=
  { method 8 false [] [instr 0 0x17, instr 1 0x10 (.argument index), instr 3 0x2A] with
    parameters := [uint32] }

/-- A stored argument takes a home after the locals, so its `starg` writes a frame slot. -/
theorem stored_argument_homed :
    (decoded (encodeBody pin (storeRaw 0)) (storeRaw 0)).map
        (fun method => (method.code, method.parameterHomes)) =
      some ([.ldc_i4 1, .starg 0, .ret], [(0, .word32)]) := by
  cil_kernel_rfl
#print axioms stored_argument_homed

/-- `opcode index; pop; ret` over one `uint32` parameter, for an argument load or address. -/
private def argumentRaw (opcode index : Nat) : RawMethod :=
  { method 8 false [] [instr 0 opcode (.argument index), instr 2 0x26, instr 3 0x2A] with
    parameters := [uint32] }

/-- An argument load, store or address of the one declared argument decodes, and one naming a
    second argument gives no method: no frame holds it, and a store or address has no home. -/
theorem undeclared_argument_has_no_method :
    (Method.ofRaw? .scalar {} [] [true, true, true] (argumentRaw 0x0E 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] [true, true, true] (storeRaw 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] [true, true, true] (argumentRaw 0x0F 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] [true, true, true] (argumentRaw 0x0E 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} [] [true, true, true] (storeRaw 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} [] [true, true, true] (argumentRaw 0x0F 1) []).isNone = true := by
  decide +kernel
#print axioms undeclared_argument_has_no_method

/-- The add bytes against the add definition with one parameter, and the local body against its
    definition with a `uint64` local, fail the body check, so neither has a method. -/
theorem refused_body_has_no_method :
    ((encodeBody pin addArgumentsRaw).map fun body =>
        (checkBody body { addArgumentsRaw with parameters := [uint64] } []).toBool) = some false ∧
      (decoded (encodeBody pin addArgumentsRaw)
        { addArgumentsRaw with parameters := [uint64] }).isNone = true ∧
      ((encodeBody pin (localRaw true)).map fun body =>
        (checkBody body { localRaw true with locals := [uint64] } []).toBool) = some false ∧
      (decoded (encodeBody pin (localRaw true)) { localRaw true with locals := [uint64] }).isNone =
        true := by
  decide +kernel
#print axioms refused_body_has_no_method

/-- A class outside the metadata world, as a type argument. -/
private def dogClass : TypeExpr := .object "Fixture" "Fixture.Dog"

/-- `ldnull; castclass !!0; pop; ret`, generic over one method type parameter. -/
private def genericCastRaw : RawMethod :=
  { method 8 false [] [instr 0 0x14, instr 1 0x74 (.type (.parameter 0)), instr 6 0x26,
      instr 7 0x2A] with genericParameters := [{ flags := 0, types := [] }] }

/-- The code is decoded from the instantiated definition, so the cast tests the type argument
    rather than the open parameter. -/
theorem generic_cast_tests_its_argument :
    (Method.ofRaw? .scalar {} [] (allLive genericCastRaw) genericCastRaw [dogClass]).map (·.code) =
      some [.ldnull, .castclass dogClass, .pop, .ret] := by
  cil_kernel_rfl
#print axioms generic_cast_tests_its_argument

/-- Instantiation substitutes the method argument into the receiver of the decoded call. -/
theorem generic_constrained_receiver :
    let slot := { getSite with method.hasThis := true }
    let caller := { method 8 false [] [instr 0 2, instr 1 0xFE16 (.type (.parameter 0)),
        instr 7 111 (.call slot), instr 12 42] with
      genericParameters := [{ flags := 0, types := [] }], returnType := int32,
      parameters := [.byref (.parameter 0)] }
    (Method.ofRaw? .scalar {} [(2, .direct 1)] (allLive caller) caller [int32]).map (·.code) =
      some [.ldarg 0, .nop, .call slot.method { constrained := some int32 }, .ret] := by
  cil_kernel_rfl
#print axioms generic_constrained_receiver

/-- `ldnull; unbox.any object; pop; ret`, with the type token of the world's `System.Object`. -/
private def unboxBytes : List Nat :=
  [0x22, 0x14, 0xA5] ++ littleEndian 4 tokens.objectRef ++ [0x26, 0x2A]

/-- The definition `unboxBytes` decode to. -/
private def unboxRaw : RawMethod :=
  method 8 false [] [instr 0 0x14, instr 1 0xA5 (.type objectType), instr 6 0x26, instr 7 0x2A]

/-- `unboxBytes` with its token table and the world's metadata. -/
private def unboxBody : BodyEvidence :=
  evidenceOf unboxBytes [(tokens.objectRef, .type objectType)] { own := own.1, others := [lib] }
    unboxRaw

/-- The pinned bytes are well formed, but live unbox.any prevents method construction. -/
theorem live_unbox_refused :
    (checkBody unboxBody unboxRaw []).toBool = true ∧
      (Method.ofBody? .scalar {} [] (allLive unboxRaw) unboxBody unboxRaw []).map (·.code) =
        none := by
  constructor
  · decide +kernel
  · cil_kernel_rfl
#print axioms live_unbox_refused

/-- Closed decoding identifies the first live hole by its index and opcode. -/
theorem unbox_refusal_site :
    Method.ofClosed? .scalar {} [] (allLive unboxRaw) unboxRaw
      ⟨[], [], List.replicate 4 .other⟩ = .error (.liveHole 1 0xa5) := by
  cil_kernel_rfl
#print axioms unbox_refusal_site

/-- error: cil_decoded_method: CIL.Extraction.MethodDecodeError.liveHole 1 165 -/
#guard_msgs in
cil_decoded_method refusedUnbox := Method.ofClosed? .scalar {} [] (allLive unboxRaw)
  unboxRaw ⟨[], [], List.replicate 4 .other⟩

/-- A method evidence record with every instruction reachable and no links. -/
def item (original : RawMethod) (body : BodyEvidence) : MethodEvidence :=
  { original := original, body := body, arguments := [], closed := original,
    parameterInput := ⟨[], [], []⟩, reachable := allLive original, featureStates := [],
    scalarStates := [], layoutUses := [] }

/-- The receiver method named by its own address operand. -/
private def instanceAddressSite : CallSite := {
  method := {
    owner := .object ownIdentity "Program", name := name!"M", hasThis := true,
    genericArity := 0, returnType := .void, parameters := [] },
  declared := { convention := 0x20 }, target := .managed 0x06000001, name := "M",
  typeArguments := [], parameterCount := 0, returnsValue := false }

/-- A parameterless instance method that takes its own address, pops it and returns. -/
private def instanceAddressRaw : RawMethod :=
  { method 8 false [] [instr 0 0xFE06 (.call instanceAddressSite), instr 6 0x26, instr 7 0x2A]
    with hasThis := true, attributes := 0x86,
         receiverClass := some instanceAddressSite.method.owner }

/-- The bytes match the instance method, but its address cannot bind to a static signature. -/
theorem instance_address_program_refused :
    (do
      let (slice, _) ← methodMetadata pin instanceAddressRaw
      let body := evidenceOf [0x22, 0xFE, 0x06, 1, 0, 0, 6, 0x26, 0x2A]
        [(0x06000001, .call instanceAddressSite)] { own := slice } instanceAddressRaw
      let evidence := { item instanceAddressRaw body with
        links := [(0, .address 0)],
        featureStates := [some ⟨[], []⟩, some ⟨[none], []⟩, some ⟨[], []⟩] }
      pure (bodyMatches body instanceAddressRaw [], (decodedProgram? .scalar {} [evidence]).isNone))
      = some (true, true) := by decide +kernel
#print axioms instance_address_program_refused

/-- The adder's certificate records the stack depth before each instruction. -/
def addFeatureStates : FeatureCertificate :=
  [0, 1, 2, 1].map fun depth => some ⟨List.replicate depth none, []⟩

/-- Both adders decode. A malformed second body or missing certificate rejects the program. -/
theorem program_needs_every_body :
    ((encodeBody pin addArgumentsRaw).bind fun body => do
      let adder := { item addArgumentsRaw body with featureStates := addFeatureStates }
      let pair ← decodedProgram? .scalar {} [adder, adder]
      let badBody := { adder with original := { addArgumentsRaw with parameters := [uint64] } }
      let noCertificate := { adder with featureStates := [] }
      pure (pair.length, (decodedProgram? .scalar {} [adder, badBody]).isNone,
        (decodedProgram? .scalar {} [adder, noCertificate]).isNone)) =
      some (2, true, true) := by decide +kernel
#print axioms program_needs_every_body

/-- The profile the decoded definitions below are evaluated under; a named constant passed to
    the decoder stays named in the method. -/
@[cil_code] def testProfile : FeatureProfile := .scalar

/-- The layouts the decoded definitions below are evaluated under. -/
@[cil_code] def testEnvironment : LayoutEnvironment := {}

/-- `ldarg.0; ldarg.1; add; ldc.i4.m1; add; ret` over two `uint32` parameters. -/
private def sumRaw : RawMethod :=
  { method 8 false [] [instr 0 2, instr 1 3, instr 2 0x58, instr 3 0x15, instr 4 0x58,
      instr 5 0x2A] with parameters := [uint32, uint32], returnType := uint32 }

cil_decoded_method sumMethod :=
  Method.ofRaw? testProfile testEnvironment [] (allLive sumRaw) sumRaw []
cil_instruction_equations sumMethod

/-- The definition is the method the decoder gives: the decoded code, the declared signature,
    and the profile and layouts it was evaluated under. -/
example : sumMethod =
    { code := [.ldarg 0, .ldarg 1, .add, .ldc_i4 4294967295, .add, .ret], locals := [],
      profile := testProfile, environment := testEnvironment,
      declared := { parameters := [uint32, uint32], returnType := uint32, initLocals := false },
      returnsValue := true } := rfl

/-- info: Tests.DecodedMethod.sumMethod_decoder_eq :
  Method.ofRaw? testProfile testEnvironment [] (allLive sumRaw) sumRaw [] = some sumMethod -/
#guard_msgs (whitespace := lax) in #check sumMethod_decoder_eq

-- The kernel proves the decoded fact and the field facts by reduction, with no other axiom.
/-- info: 'Tests.DecodedMethod.sumMethod_decoder_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumMethod_decoder_eq
/-- info: 'Tests.DecodedMethod.sumMethod_profile' does not depend on any axioms -/
#guard_msgs in #print axioms sumMethod_profile

-- Stepping reads each instruction as a constructor over numerals, a negative constant included.
/-- info: Tests.DecodedMethod.sumMethod_instruction3 :
  sumMethod.code[3]? = some (Instruction.ldc_i4 0xFFFFFFFF) -/
#guard_msgs (whitespace := lax) in #check sumMethod_instruction3

-- The profile fact names the profile the decoder was given, as an extraction's facts do.
/-- info: Tests.DecodedMethod.sumMethod_profile : sumMethod.profile = testProfile -/
#guard_msgs in #check sumMethod_profile

-- The same unbox opcode remains a hole when its mask entry is false.
cil_decoded_method unboxMethod :=
  Method.ofRaw? testProfile testEnvironment [] [true, false, true, true] unboxRaw []
cil_instruction_equations unboxMethod

/-- info: Tests.DecodedMethod.unboxMethod_instruction1 :
  unboxMethod.code[1]? = some (Instruction.unadmitted 165) -/
#guard_msgs (whitespace := lax) in #check unboxMethod_instruction1

/-- The `uint32` field of `Dog` the decoded definition below names. -/
def ageField : FieldRef := { owner := dogClass, index := 0, type := uint32, name := name!"Age" }

/-- `ldarg.0; ldfld Dog.Age; ret` over one `Dog` parameter. -/
private def ageRaw : RawMethod :=
  { method 8 false [] [instr 0 2, instr 1 0x7B (.field dogClass 0 uint32 name!"Age" false),
      instr 6 0x2A] with parameters := [dogClass], returnType := uint32 }

-- A field operand equal to a listed constant is written as that constant, as an extraction's
-- literal names it, so the shape facts stated about the constant apply to the decoded method.
cil_decoded_method ageMethod [ageField] :=
  Method.ofRaw? testProfile testEnvironment [] (allLive ageRaw) ageRaw []
cil_instruction_equations ageMethod

/-- info: Tests.DecodedMethod.ageMethod_instruction1 :
  ageMethod.code[1]? = some (Instruction.ldfld ageField) -/
#guard_msgs (whitespace := lax) in #check ageMethod_instruction1

/-- A field of `Dog` that `ageRaw` does not access. -/
def weightField : FieldRef := { ageField with index := 1 }

-- A listed constant that names no field operand is refused rather than ignored.
/-- error: cil_decoded_method: the decoded method has no field operand
  Tests.DecodedMethod.weightField -/
#guard_msgs (whitespace := lax) in
cil_decoded_method weightMethod [weightField] :=
  Method.ofRaw? testProfile testEnvironment [] (allLive ageRaw) ageRaw []

-- A body naming an undeclared argument defines nothing.
/-- error: cil_decoded_method: the decoder gives no method
  Method.ofRaw? testProfile testEnvironment [] [true, true, true] (argumentRaw 14 1) [] -/
#guard_msgs (whitespace := lax) in
cil_decoded_method undeclaredMethod :=
  Method.ofRaw? testProfile testEnvironment [] [true, true, true] (argumentRaw 0x0E 1) []

-- A decoder with a hole is not evaluated.
/-- error: cil_decoded_method: the decoder must be a closed term
  Method.ofRaw? ?m.1 testEnvironment [] (allLive sumRaw) sumRaw [] -/
#guard_msgs (whitespace := lax) in
cil_decoded_method openMethod := Method.ofRaw? _ testEnvironment [] (allLive sumRaw) sumRaw []

/-- A number the kernel cannot reduce; compiled code evaluates it to its default. -/
opaque stuckIndex : Nat

/-- A list the kernel cannot reduce; compiled code evaluates it to its default. -/
opaque stuckLocals : List Value

/-- An empty method under the given profile and layouts with the given locals and opaque vector
    locals, a decoder whose fields the kernel may not reduce. -/
private def emptyMethod (profile : FeatureProfile) (environment : LayoutEnvironment)
    (locals : List Value) (opaqueVectorLocals : List Nat) : Option Method :=
  some { code := [], locals, returnsValue := false, opaqueVectorLocals, profile, environment }

-- A value the kernel does not reduce to the evaluated literal is refused, never kept unreduced.
/-- error: cil_decoded_method: the kernel does not reduce both sides of
  Tests.DecodedMethod.stuckIndexMethod_decoder_eq to one term -/
#guard_msgs (whitespace := lax) in
cil_decoded_method stuckIndexMethod := emptyMethod testProfile testEnvironment [] [stuckIndex]

-- A constant passed to the decoder is written by name, so the opaque list is passed inside a term.
/-- error: cil_decoded_method: the kernel does not reduce both sides of
  Tests.DecodedMethod.stuckLocalsMethod_decoder_eq to one term -/
#guard_msgs (whitespace := lax) in
cil_decoded_method stuckLocalsMethod :=
  emptyMethod testProfile testEnvironment (stuckLocals ++ []) []

/-- `ldarg.0; stloc.0; br 7; ldloc.0; ldc.i4.1; sub; stloc.0; ldloc.0; brtrue 3; ldloc.0; ret`:
    a `uint32` count copied to an initialized local and decremented to zero. -/
private def countdownRaw : RawMethod :=
  { method 8 true [uint32] [instr 0 2, instr 1 10, instr 2 0x2B (.target 7), instr 3 6,
      instr 4 0x17, instr 5 0x59, instr 6 10, instr 7 6, instr 8 0x2D (.target 3), instr 9 6,
      instr 10 0x2A] with
    parameters := [uint32], returnType := uint32 }

cil_decoded_method countdownMethod :=
  Method.ofRaw? testProfile testEnvironment [] (allLive countdownRaw) countdownRaw []
cil_instruction_equations countdownMethod
cil_resolution_facts countdownMethod

-- The frame facts hold the decoded local, initialized by the body's flag.
/-- info: Tests.DecodedMethod.countdownMethod_locals : countdownMethod.locals = [Value.i32 0] -/
#guard_msgs in #check countdownMethod_locals
/-- info: Tests.DecodedMethod.countdownMethod_localKinds :
  countdownMethod.localKinds = [LocalKind.word32] -/
#guard_msgs (whitespace := lax) in #check countdownMethod_localKinds

cil_resolution_facts sumMethod

/-- Stepping reads the decoded definition through its `cil_code` facts: the sum of the two
    arguments and the constant `-1`, with memory unchanged. -/
theorem sum_returns (memory : Safety.Memory) (left right : W32) :
    ∃ fuel, Safety.invoke [sumMethod] fuel 0 [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (left + right + 0xFFFFFFFF))]) := by
  cil_checked_steps
#print axioms sum_returns

/-- `sumRaw` as the definition with its own token, the callee of `callerRaw`. -/
private def summingRaw : RawMethod := { sumRaw with token := tokens.main + 1 }

/-- The call site of `summingRaw`, a static method of the world's `Program` class. -/
private def sumSite : CallSite := {
  declared := { convention := 0, returnType := uint32, parameters := [uint32, uint32] },
  method := {
    owner := .object ownIdentity "Program", name := name!"Sum", hasThis := false,
    genericArity := 0, returnType := uint32, parameters := [uint32, uint32] },
  name := "Sum", target := .managed summingRaw.token, typeArguments := [], parameterCount := 2,
  returnsValue := true }

/-- `ldarg.0; ldarg.1; call Sum(uint32, uint32); ret` over two `uint32` parameters. -/
private def callerRaw : RawMethod :=
  { method 8 false [] [instr 0 2, instr 1 3, instr 2 0x28 (.call sumSite), instr 7 0x2A] with
    parameters := [uint32, uint32], returnType := uint32 }

-- The bytes name the callee's token; the program index of `summingRaw`, 1, is the link at pc 2.
cil_decoded_method callerMethod :=
  Method.ofRaw? testProfile testEnvironment [(2, .direct 1)] (allLive callerRaw) callerRaw []
cil_instruction_equations callerMethod
cil_resolution_facts callerMethod

/-- The call decodes to the method its operand names, and its target is the link the decoder
    was given. -/
example : callerMethod.code[2]? = some (.call sumSite.method) ∧
    callerMethod.linkAt 2 = some (.direct 1) := ⟨rfl, rfl⟩

/-- The decoded caller returns what the decoded callee its link names returns. -/
theorem caller_returns (memory : Safety.Memory) (left right : W32) :
    ∃ fuel, Safety.invoke [callerMethod, sumMethod] fuel 0
        [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (left + right + 0xFFFFFFFF))]) := by
  cil_checked_steps
#print axioms caller_returns

/-- The table `callerMethod`'s link indexes: the caller at 0 and its callee at 1. -/
private def callTable : List SpecializedMethod := [⟨[], callerRaw, ⟨ownIdentity⟩⟩, ⟨[], summingRaw, ⟨ownIdentity⟩⟩]

/-- The call check accepts the link the decoder was given and rejects a forged one: another
    method with the same signature but another token, an index past the table, or a link of
    another kind. -/
theorem decoded_call_links :
    ManagedCallsValid callTable [] (fun _ => false) callerRaw [true, true, true, true]
      callerMethod ∧
    ¬ ManagedCallsValid callTable [] (fun _ => false) callerRaw [true, true, true, true]
      { callerMethod with links := [(2, .direct 0)] } ∧
    ¬ ManagedCallsValid callTable [] (fun _ => false) callerRaw [true, true, true, true]
      { callerMethod with links := [(2, .direct 2)] } ∧
    ¬ ManagedCallsValid callTable [] (fun _ => false) callerRaw [true, true, true, true]
      { callerMethod with links := [(2, .virtual [(uint32, 1)])] } ∧
    ¬ ManagedCallsValid callTable [] (fun _ => false) callerRaw [true, true, true, true]
      { callerMethod with links := [] } := by
  decide +kernel
#print axioms decoded_call_links

/-- `T::Word`, one `uint64`. -/
private def wordLayout : RawLayout :=
  { identity := "T::Word", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .unsigned64 }] }

/-- `T::Word` and the layout CoreCLR computes for it. -/
@[cil_code] def wordEnvironment : LayoutEnvironment :=
  { rawLayouts := [wordLayout],
    layouts := #[⟨{ size := 8, fields := [{ offset := 0, width := 8 }] }, 8⟩] }

/-- A static aggregate load requires all eight bytes of the field's checked layout. -/
theorem ordinaryStaticAggregateSizeRefused :
    let site := { bias with
      field.type := .aggregate wordLayout.identity 0, scalar := none, bytes := List.replicate 8 0,
      initializer := some { method := 1, arguments := [] } }
    ordinaryLoad site (environment := wordEnvironment) = .ok [.ldsfld site.field, .ret] ∧
      ordinaryLoad { site with bytes := List.replicate 7 0 } (environment := wordEnvironment) =
        liveHoleAt 0 126 := by decide +kernel
#print axioms ordinaryStaticAggregateSizeRefused

/-- `ret` over one zero-initialized `T::Word` local. -/
private def aggregateLocalRaw : RawMethod :=
  method 8 true [.aggregate "T::Word" 0] [instr 0 0x2A]

cil_decoded_method aggregateLocalMethod :=
  Method.ofRaw? testProfile wordEnvironment [] (allLive aggregateLocalRaw) aggregateLocalRaw []

-- A zero-initialized struct local is written as an extraction's literal writes it, so a proof's
-- hypothesis about making that local matches the goal frame entry leaves.
/-- info: Tests.DecodedMethod.aggregateLocalMethod_locals :
  aggregateLocalMethod.locals = [Value.aggregate (List.replicate 8 0)] -/
#guard_msgs (whitespace := lax) in #check aggregateLocalMethod_locals

open CIL.Safety in
/-- Entering the decoded method's frame makes its struct local from `List.replicate 8 0`, the
    term a caller's hypothesis about the local names. -/
theorem aggregate_local_frame_entry (memory entered : Safety.Memory) (slot : Reference)
    (made : makeLocal memory.nextIdentity (.aggregate 8) (.aggregate (List.replicate 8 0)) memory =
      .ok (.bytes (.aggregate 8) slot, [slot.allocation], entered)) :
    enterFrame aggregateLocalMethod [] memory =
      .ok ({ activation := memory.nextIdentity, locals := [.bytes (.aggregate 8) slot],
              owned := [slot.allocation] }, entered) := by
  simp only [enterFrame, aggregateLocalMethod_opaqueVectorLocals, makeSelectedLocals,
    List.isEmpty_nil, ite_true, aggregateLocalMethod_localKinds, aggregateLocalMethod_locals,
    makeLocals, made, aggregateLocalMethod_parameterHomes, makeParameterHomes, List.map_nil,
    Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
#print axioms aggregate_local_frame_entry

/-- `simp` unfolds a decoded method in the module that defines it, as a batch that inlines an
    extraction beside its proof does. -/
theorem aggregate_local_unfolds : aggregateLocalMethod.code = [CIL.Instruction.ret] := by
  simp only [aggregateLocalMethod]
#print axioms aggregate_local_unfolds

/-- The closed method of `code` under the `live` mask, with no arguments, locals or result. -/
private def prefixedResult (code : List RawInstruction)
    (live : List Bool := code.map fun _ => true) : Except MethodDecodeError Method :=
  let source := { addRaw with code }
  let arguments : RawArguments :=
    { arguments := [], locals := [], code := code.map fun _ => .other }
  Method.ofClosed? .scalar {} [] live source arguments

/-- `unaligned. n` decodes to `nop` and gives the block operation after it its alignment, an
    unprefixed block operation has the default alignment, and a load after the prefix decodes as
    without it. -/
theorem blockOperationsDecode :
    let copy := [instr 0 0xfe12 (.integer 2), instr 2 0xfe17, instr 4 0x2a]
    let fill := [instr 0 0xfe18, instr 2 0x2a]
    let load := [instr 0 0xfe12 (.integer 1), instr 2 0x4b, instr 3 0x2a]
    (match prefixedResult copy, prefixedResult fill, prefixedResult load with
     | .ok copied, .ok filled, .ok loaded =>
       copied.code == [.nop, .cpblk 2, .ret] &&
         filled.code == [.initblk defaultBlockAlignment, .ret] &&
         loaded.code == [.nop, .ldind .u4, .ret]
     | _, _, _ => false) = true := by
  decide +kernel

#print axioms blockOperationsDecode

/-- Whether the closed method of `code` is refused at a live hole of `opcode` at `pc`. -/
private def refusedAt (code : List RawInstruction) (pc opcode : Nat) : Bool :=
  match prefixedResult code with
  | .error (.liveHole site found) => site == pc && found == opcode
  | _ => false

/-- `volatile.` is a hole before an access or a block operation, an `unaligned.` alignment
    other than 1, 2 or 4 is a hole at the prefix, and an instruction `unaligned.` does not
    modify, a second prefix included, is a hole after it. -/
theorem prefixHoles :
    refusedAt [instr 0 0xfe13, instr 2 0x4a, instr 3 0x2a] 0 0xfe13 &&
    refusedAt [instr 0 0xfe13, instr 2 0xfe17, instr 4 0x2a] 0 0xfe13 &&
    refusedAt [instr 0 0xfe12 (.integer 3), instr 2 0x4a, instr 3 0x2a] 0 0xfe12 &&
    refusedAt [instr 0 0xfe12 (.integer 8), instr 2 0xfe17, instr 4 0x2a] 0 0xfe12 &&
    refusedAt [instr 0 0xfe12 (.integer 1), instr 2 0x58, instr 3 0x2a] 1 0x58 &&
    refusedAt [instr 0 0xfe12 (.integer 1), instr 2 0xfe13, instr 4 0x4a, instr 5 0x2a] 1 0xfe13 &&
    refusedAt [instr 0 0xfe12 (.integer 1), instr 2 0xfe12 (.integer 1), instr 4 0x4a,
      instr 5 0x2a] 1 0xfe12 &&
    refusedAt [instr 0 0xfe13, instr 2 0xfe12 (.integer 1), instr 4 0x4a, instr 5 0x2a]
      0 0xfe13 = true := by
  decide +kernel

#print axioms prefixHoles

/-- `unaligned.` next to any other prefix is a hole at the second of the two, or at the first
    when that one decodes to nothing: `readonly.`, `constrained.`, `tail.` and `no.` in
    either order. -/
theorem prefixCombinationsRefused :
    let load := [instr 6 0x4b, instr 7 0x2a]
    let aligned := instr 0 0xfe12 (.integer 1)
    refusedAt ([aligned, instr 2 0xfe1e] ++ load) 1 0xfe1e &&
    refusedAt ([instr 0 0xfe1e, instr 2 0xfe12 (.integer 1)] ++ load) 1 0xfe12 &&
    refusedAt ([aligned, instr 2 0xfe16 (.type int32)] ++ load) 1 0xfe16 &&
    refusedAt ([instr 0 0xfe16 (.type int32), instr 2 0xfe12 (.integer 1)] ++ load) 1 0xfe12 &&
    refusedAt ([aligned, instr 2 0xfe14] ++ load) 1 0xfe14 &&
    refusedAt ([instr 0 0xfe14, instr 2 0xfe12 (.integer 1)] ++ load) 0 0xfe14 &&
    refusedAt ([aligned, instr 2 0xfe19 (.integer 1)] ++ load) 1 0xfe19 &&
    refusedAt ([instr 0 0xfe19 (.integer 1), instr 2 0xfe12 (.integer 1)] ++ load)
      0 0xfe19 = true := by
  decide +kernel

#print axioms prefixCombinationsRefused

/-- A decoded `unaligned.` with no instruction after it, and a branch into the instruction it
    modifies from a live pc, fail the prefix check. -/
theorem prefixStructureRefused :
    let trailing := [instr 0 0x16, instr 1 0xfe12 (.integer 1)]
    let entered :=
      [instr 0 0x38 (.target 2), instr 5 0xfe12 (.integer 1), instr 7 0x4b, instr 8 0x2a]
    (match prefixedResult trailing, prefixedResult entered [true, false, true, true] with
     | .error .invalidPrefixes, .error .invalidPrefixes => true
     | _, _ => false) = true := by
  decide +kernel

#print axioms prefixStructureRefused

end Tests.DecodedMethod
