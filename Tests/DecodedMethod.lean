import CIL.Extraction.DecodedMethod
import Tests.BodyEncoding
import Tests.MetadataWorld

/-!
# Decoded method tests

Bodies built by `Tests.BodyEncoding.encodeBody` and by hand over `Tests.MetadataWorld` must
decode through `Method.ofBody?` to the method their bytes denote: the code `Instruction.ofRaw?`
gives, locals initialized by the flag in the bytes rather than the definition's, and the code of
the bytes rather than the definition's. A body with an instruction outside the value family
gives no method, and neither does a program with such a body.
-/

namespace Tests.DecodedMethod

open CIL CIL.Extraction Tests.BodyEncoding Tests.MetadataWorld

/-- The assembly whose metadata the bodies are checked against. -/
private def pin : AssemblyPin := { identity := ownIdentity }

/-- The world's `Main`, a public static method with no parameters, with the given body fields. -/
private def method (initLocals : Bool) (locals : List TypeExpr) (code : List RawInstruction) :
    RawMethod :=
  { token := tokens.main, owner := ownIdentity ++ "::Program", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0x96, implementation := 0,
    returnType := .void, parameters := [], locals := locals, initLocals := initLocals,
    maxStack := 8, genericParameters := [], code := code }

/-- One raw instruction. -/
private def instr (offset opcode : Nat) (operand : RawOperand := .none) : RawInstruction :=
  { offset := offset, opcode := opcode, operand := operand }

/-- The method of the bytes of `body` against the definition `original`, with no layouts. -/
private def decoded (body : Option BodyEvidence) (original : RawMethod) : Option Method :=
  body.bind fun body => Method.ofBody? .scalar {} body original []

/-- `ldc.i4.1; ldc.i4.2; add; ret`. -/
private def addRaw : RawMethod :=
  method false [] [instr 0 0x17, instr 1 0x18, instr 2 0x58, instr 3 0x2A]

/-- `ldc.i4.1; ldc.i4.2; sub; ret`. -/
private def subRaw : RawMethod :=
  method false [] [instr 0 0x17, instr 1 0x18, instr 2 0x59, instr 3 0x2A]

/-- The frame both bodies declare: no locals, no homes, no arguments, no return value. -/
private def frame (code : List Instruction) : Method :=
  { code := code, locals := [], declared := { parameters := [], returnType := .void },
    returnsValue := false }

/-- The tiny add body decodes to its code and its declared frame. -/
theorem add_decodes :
    decoded (encodeBody pin addRaw) addRaw = some (frame [.ldc_i4 1, .ldc_i4 2, .add, .ret]) := by
  cil_kernel_rfl
#print axioms add_decodes

/-- The method of the sub bytes against the add definition is the sub method: `Method.ofBody?`
    reads no instruction of the definition. -/
theorem code_read_from_bytes :
    decoded (encodeBody pin subRaw) addRaw = some (frame [.ldc_i4 1, .ldc_i4 2, .sub, .ret]) := by
  cil_kernel_rfl
#print axioms code_read_from_bytes

/-- `ldc.i4.1; stloc.0; ldloc.0; ret` over one `uint32` local, with the given init flag. -/
private def localRaw (initLocals : Bool) : RawMethod :=
  method initLocals [uint32] [instr 0 0x17, instr 1 0x0A, instr 2 0x06, instr 3 0x2A]

/-- The locals start at zero exactly when the bytes set the init flag, whatever the definition
    says. -/
theorem locals_initialized_by_the_bytes :
    (decoded (encodeBody pin (localRaw true)) (localRaw false)).map (·.locals) =
        some [.i32 0] ∧
      (decoded (encodeBody pin (localRaw false)) (localRaw true)).map (·.locals) =
        some [.unmodeled] := by
  constructor <;> cil_kernel_rfl
#print axioms locals_initialized_by_the_bytes

/-- `ldc.i4.1; newarr object; pop; ret`, with the type token of the world's `System.Object`. -/
private def newarrBytes : List Nat :=
  [0x22, 0x17, 0x8D] ++ littleEndian 4 tokens.objectRef ++ [0x26, 0x2A]

/-- The system type `newarr` names. -/
private def objectType : TypeExpr := .atom runtimeScope "System.Object"

/-- The definition `newarrBytes` decode to. -/
private def newarrRaw : RawMethod :=
  method false [] [instr 0 0x17, instr 1 0x8D (.type objectType), instr 6 0x26, instr 7 0x2A]

/-- `newarrBytes` with its token table and the world's metadata. -/
private def newarrBody : BodyEvidence :=
  evidenceOf newarrBytes [(tokens.objectRef, .type objectType)] { own := own.1, others := [lib] }
    newarrRaw

/-- The newarr body passes the body check but has no decoded method. -/
theorem newarr_has_no_method :
    (checkBody newarrBody newarrRaw []).toBool = true ∧
      (Method.ofBody? .scalar {} newarrBody newarrRaw []).isNone = true := by
  decide +kernel
#print axioms newarr_has_no_method

/-- An evidence record whose only fields `decodedProgram?` reads are `original`, `body` and
    `arguments`. -/
private def item (original : RawMethod) (body : BodyEvidence) : MethodEvidence :=
  { original := original, body := body, arguments := [], closed := original,
    parameterInput := ⟨[], [], []⟩, reachable := [], featureStates := [], scalarStates := [],
    layoutUses := [] }

/-- One body without a decoded method leaves the program without one. -/
theorem program_needs_every_method :
    ((encodeBody pin addRaw).bind fun addBody =>
      decodedProgram? .scalar {} [item addRaw addBody, item newarrRaw newarrBody]).isNone =
        true := by
  decide +kernel
#print axioms program_needs_every_method

end Tests.DecodedMethod
