import CIL.Extraction.DecodedMethod
import Tests.BodyDecoding

/-!
# Decoded method tests

Bodies built by `Tests.BodyEncoding.encodeBody` and by hand over `Tests.MetadataWorld` must
decode through `Method.ofBody?` to the method their bytes denote: the code `Instruction.ofRaw`
gives, locals initialized by the flag in the bytes rather than the definition's, and the code of
the bytes rather than the definition's. A stored argument takes a home. An instruction outside
the value family decodes to a hole carrying its opcode, which faults when stepped; a body the
check refuses, or one with an argument instruction naming an undeclared argument, gives no
method, and neither does a program with such a body.
-/

namespace Tests.DecodedMethod

open CIL CIL.Extraction Tests.BodyEncoding Tests.BodyDecoding Tests.MetadataWorld

/-- The method of the bytes of `body` against the definition `original`, with no layouts. -/
private def decoded (body : Option BodyEvidence) (original : RawMethod) : Option Method :=
  body.bind fun body => Method.ofBody? .scalar {} body original []

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

/-- An explicit receiver cannot be decoded as an additional implicit argument. -/
theorem explicit_this_has_no_raw_method :
    (Method.ofRaw? .scalar {} { addRaw with explicitThis := true } []).isNone = true := by
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
private def addArgumentsRaw : RawMethod :=
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
    (Method.ofRaw? .scalar {} (argumentRaw 0x0E 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} (storeRaw 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} (argumentRaw 0x0F 0) []).isSome = true ∧
      (Method.ofRaw? .scalar {} (argumentRaw 0x0E 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} (storeRaw 1) []).isNone = true ∧
      (Method.ofRaw? .scalar {} (argumentRaw 0x0F 1) []).isNone = true := by
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

/-- `ldc.i4.1; newarr object; pop; ret`, with the type token of the world's `System.Object`. -/
private def newarrBytes : List Nat :=
  [0x22, 0x17, 0x8D] ++ littleEndian 4 tokens.objectRef ++ [0x26, 0x2A]

/-- The definition `newarrBytes` decode to. -/
private def newarrRaw : RawMethod :=
  method 8 false [] [instr 0 0x17, instr 1 0x8D (.type objectType), instr 6 0x26, instr 7 0x2A]

/-- `newarrBytes` with its token table and the world's metadata. -/
private def newarrBody : BodyEvidence :=
  evidenceOf newarrBytes [(tokens.objectRef, .type objectType)] { own := own.1, others := [lib] }
    newarrRaw

/-- The newarr body passes the body check and decodes with a hole at pc 1 carrying `newarr`'s
    opcode 0x8D, since no family admits a type operand yet. -/
theorem newarr_decodes_to_a_hole :
    (checkBody newarrBody newarrRaw []).toBool = true ∧
      (Method.ofBody? .scalar {} newarrBody newarrRaw []).map (·.code) =
        some [.ldc_i4 1, .unadmitted 0x8D, .pop, .ret] := by
  constructor
  · decide +kernel
  · cil_kernel_rfl
#print axioms newarr_decodes_to_a_hole

/-- The method decoded from the newarr bytes loads its constant and faults at the hole's pc. -/
theorem decoded_hole_faults :
    (Method.ofBody? .scalar {} newarrBody newarrRaw []).map (fun method =>
      Safety.invoke [method] 4 0 [] Safety.Memory.empty) =
        some (.error ⟨0, 1, .unsupported "Opcode not admitted"⟩) := by
  cil_kernel_rfl
#print axioms decoded_hole_faults

/-- An evidence record whose only fields `decodedProgram?` reads are `original`, `body` and
    `arguments`. -/
private def item (original : RawMethod) (body : BodyEvidence) : MethodEvidence :=
  { original := original, body := body, arguments := [], closed := original,
    parameterInput := ⟨[], [], []⟩, reachable := [], featureStates := [], scalarStates := [],
    layoutUses := [] }

/-- A body with a hole still gives its method, so the add and newarr program decodes in full,
    while one refused body leaves the program without one. -/
theorem program_needs_every_body :
    ((encodeBody pin addRaw).bind fun addBody =>
      (decodedProgram? .scalar {} [item addRaw addBody, item newarrRaw newarrBody]).map
        List.length) = some 2 ∧
      ((encodeBody pin addRaw).bind fun addBody =>
        decodedProgram? .scalar {}
          [item addRaw addBody, item { addRaw with parameters := [uint64] } addBody]).isNone =
        true := by
  constructor <;> decide +kernel
#print axioms program_needs_every_body

end Tests.DecodedMethod
