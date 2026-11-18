import CIL.Extraction.DecodedDefinition
import CIL.InstructionEquations
import CIL.Safety.ResolutionFacts
import CIL.Safety.SymbolicExecution
import Tests.BodyDecoding

/-!
# Decoded method tests

Bodies built by `Tests.BodyEncoding.encodeBody` and by hand over `Tests.MetadataWorld` must
decode through `Method.ofBody?` to the method their bytes denote: the code `Instruction.ofRaw`
gives, locals initialized by the flag in the bytes rather than the definition's, and the code of
the bytes rather than the definition's. A stored argument takes a home. An instruction outside
the value family decodes to a hole carrying its opcode, which faults when stepped; a body the
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

/-- The method of the bytes of `body` against the definition `original`, with no layouts. -/
private def decoded (body : Option BodyEvidence) (original : RawMethod) : Option Method :=
  body.bind fun body => Method.ofBody? .scalar {} [] body original []

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
    (Method.ofRaw? .scalar {} [] ordinaryStaticRaw []).isNone &&
      !decide (MethodShapeValid ordinaryStaticRaw (frame [])) := by
  decide +kernel
#print axioms ordinary_static_prefix_refused

/-- An unreachable tail transfer still returns the enclosing method's declared result. -/
theorem tail_result_mismatch_refused :
    (Method.ofRaw? .scalar {} [] wrongTailRaw []).isNone &&
      !decide (MethodShapeValid wrongTailRaw (frame [])) := by
  decide +kernel
#print axioms tail_result_mismatch_refused

/-- Refusal by the closed method shape excludes every full evidence record for these bodies. -/
theorem dead_call_evidence_refused (item : MethodEvidence) (emitted : Method)
    (layouts : List RawLayout) (computed : Array ComputedLayout) (pins : List AssemblyPin)
    (items : List MethodEvidence) (imports : List ImportSlot)
    (body : item.closed = ordinaryStaticRaw ∨ item.closed = wrongTailRaw ∨
      item.closed = wrongIndirectTailRaw) :
    ¬ MethodEvidenceValid layouts computed pins items imports item emitted := by
  intro valid
  have prefixes := valid.2.2.2.2.2.2.1.2.2.2.2
  rcases body with invalid | invalid | invalid <;> rw [invalid] at prefixes <;>
    exact absurd prefixes (by decide +kernel)
#print axioms dead_call_evidence_refused

/-- Bytes that decode to either invalid body cannot construct a method. -/
theorem dead_call_bytes_refused {pins : List AssemblyPin} {assembly : AssemblyPin}
    {body : BodyEvidence} {raw : RawMethod} {signature : String}
    (decodes : BodyDecodes pins assembly body raw [] signature)
    (invalid : raw = ordinaryStaticRaw ∨ raw = wrongTailRaw) :
    Method.ofBody? .scalar {} [] body raw [] = none := by
  rw [Method.ofBody?_of_decodes decodes]
  rcases invalid with rfl | rfl <;> decide +kernel
#print axioms dead_call_bytes_refused

/-- Branch entry must include the readonly modifier when constructing a method from raw code. -/
theorem raw_prefix_entry_refused :
    let raw := method 8 false [] [instr 0 20, instr 1 22, instr 2 43 (.target 4),
      instr 4 0xFE1E, instr 6 143 (.type int32), instr 11 38, instr 12 42]
    (Method.ofRaw? .scalar {} [] raw []).isNone = true := by
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
    let field := instr 3 123 (.field owner 0 (.atom runtimeScope "System.Int32") name!"n" false)
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
      (Method.ofRaw? .scalar {} [] raw []).isNone && !decide (MethodShapeValid raw (frame []))) =
        true := by
  decide +kernel
#print axioms invalid_prefix_sequences_refused

/-- An explicit receiver cannot be decoded as an additional implicit argument. -/
theorem explicit_this_has_no_raw_method :
    (Method.ofRaw? .scalar {} [] { addRaw with explicitThis := true } []).isNone = true := by
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
    (Method.ofRaw? .scalar {} [] (argumentRaw 0x0E 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] (storeRaw 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] (argumentRaw 0x0F 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} [] (argumentRaw 0x0E 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} [] (storeRaw 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} [] (argumentRaw 0x0F 1) []).isNone = true := by
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
    (Method.ofRaw? .scalar {} [] genericCastRaw [dogClass]).map (·.code) =
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
    (Method.ofRaw? .scalar {} [(2, .direct 1)] caller [int32]).map (·.code) =
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

/-- The unbox body passes the body check and decodes with a hole at pc 1 carrying `unbox.any`'s
    opcode 0xA5, since no family admits `unbox.any`. -/
theorem unbox_decodes_to_a_hole :
    (checkBody unboxBody unboxRaw []).toBool = true ∧
      (Method.ofBody? .scalar {} [] unboxBody unboxRaw []).map (·.code) =
        some [.ldnull, .unadmitted 0xA5, .pop, .ret] := by
  constructor
  · decide +kernel
  · cil_kernel_rfl
#print axioms unbox_decodes_to_a_hole

/-- The method decoded from the unbox bytes pushes its null and faults at the hole's pc. -/
theorem decoded_hole_faults :
    (Method.ofBody? .scalar {} [] unboxBody unboxRaw []).map (fun method =>
      Safety.invoke [method] 4 0 [] Safety.Memory.empty) =
        some (.error ⟨0, 1, .unsupported "Opcode not admitted"⟩) := by
  cil_kernel_rfl
#print axioms decoded_hole_faults

/-- An evidence record whose only fields `decodedProgram?` reads are `original`, `body` and
    `arguments`. -/
def item (original : RawMethod) (body : BodyEvidence) : MethodEvidence :=
  { original := original, body := body, arguments := [], closed := original,
    parameterInput := ⟨[], [], []⟩, reachable := [], featureStates := [], scalarStates := [],
    layoutUses := [] }

/-- A body with a hole still gives its method, so the add and unbox program decodes in full,
    while one refused body leaves the program without one. -/
theorem program_needs_every_body :
    ((encodeBody pin addRaw).bind fun addBody =>
      (decodedProgram? .scalar {} [item addRaw addBody, item unboxRaw unboxBody]).map
        List.length) = some 2 ∧
      ((encodeBody pin addRaw).bind fun addBody =>
        decodedProgram? .scalar {}
          [item addRaw addBody, item { addRaw with parameters := [uint64] } addBody]).isNone =
        true := by
  constructor <;> decide +kernel
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

cil_decoded_method sumMethod := Method.ofRaw? testProfile testEnvironment [] sumRaw []
cil_instruction_equations sumMethod

/-- The definition is the method the decoder gives: the decoded code, the declared signature,
    and the profile and layouts it was evaluated under. -/
example : sumMethod =
    { code := [.ldarg 0, .ldarg 1, .add, .ldc_i4 4294967295, .add, .ret], locals := [],
      profile := testProfile, environment := testEnvironment,
      declared := { parameters := [uint32, uint32], returnType := uint32, initLocals := false },
      returnsValue := true } := rfl

/-- info: Tests.DecodedMethod.sumMethod_decoder_eq :
  Method.ofRaw? testProfile testEnvironment [] sumRaw [] = some sumMethod -/
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

-- An instruction outside the value family is defined as the hole carrying its opcode.
cil_decoded_method unboxMethod := Method.ofRaw? testProfile testEnvironment [] unboxRaw []
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
cil_decoded_method ageMethod [ageField] := Method.ofRaw? testProfile testEnvironment [] ageRaw []
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
  Method.ofRaw? testProfile testEnvironment [] ageRaw []

-- A body naming an undeclared argument defines nothing.
/-- error: cil_decoded_method: the decoder gives no method
  Method.ofRaw? testProfile testEnvironment [] (argumentRaw 14 1) [] -/
#guard_msgs (whitespace := lax) in
cil_decoded_method undeclaredMethod :=
  Method.ofRaw? testProfile testEnvironment [] (argumentRaw 0x0E 1) []

-- A decoder with a hole is not evaluated.
/-- error: cil_decoded_method: the decoder must be a closed term
  Method.ofRaw? ?m.1 testEnvironment [] sumRaw [] -/
#guard_msgs (whitespace := lax) in
cil_decoded_method openMethod := Method.ofRaw? _ testEnvironment [] sumRaw []

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

cil_decoded_method countdownMethod := Method.ofRaw? testProfile testEnvironment [] countdownRaw []
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
  Method.ofRaw? testProfile testEnvironment [(2, .direct 1)] callerRaw []
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
private def callTable : List SpecializedMethod := [⟨[], callerRaw⟩, ⟨[], summingRaw⟩]

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

/-- `ret` over one zero-initialized `T::Word` local. -/
private def aggregateLocalRaw : RawMethod :=
  method 8 true [.aggregate "T::Word" 0] [instr 0 0x2A]

cil_decoded_method aggregateLocalMethod :=
  Method.ofRaw? testProfile wordEnvironment [] aggregateLocalRaw []

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

end Tests.DecodedMethod
