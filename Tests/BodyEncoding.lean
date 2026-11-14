import CIL.Extraction.Translation
import Tests.MetadataBuilder

/-!
# Method body encoding for tests

Fixtures that build a `RawMethod` by hand need method-body bytes and metadata that decode to
it, since `MethodEvidenceValid` checks both. `encodeBody` writes the bytes of a method whose
operands carry no token and the metadata slice its definition and locals are checked against,
`realizeOffsets` gives its instructions the byte offsets those bytes imply, and `withBody`
applies both to a `MethodEvidence`. The encoder serves tests only: nothing trusts it, because the
decoder re-reads every byte it writes. It is irreducible: the elaborator would evaluate the state
builder by name, unsharing its states exponentially, so only `decide +kernel` evaluates it.

The encoder handles integer, native integer, `string` and `object` types, references, pointers,
vectors and generic parameters; any other type, a token operand or a float constant gives `none`.
-/

namespace Tests.BodyEncoding

open CIL CIL.Extraction Tests.MetadataBuilder

/-- The token of the first standalone signature, which a method with locals uses. -/
def localSignatureToken : Nat := 0x11000001

/-- The `width` little-endian bytes of the two's-complement encoding of `value`. -/
def littleEndian (width : Nat) (value : Int) : List Nat :=
  let unsigned := (value % ((2 ^ (8 * width) : Nat) : Int)).toNat
  (List.range width).map fun position => unsigned / 256 ^ position % 256

/-- The opcode bytes: one byte, or `0xFE` and the second byte for `0xFE00 + nn`. -/
def opcodeBytes (opcode : Nat) : List Nat :=
  if 0xFE00 ≤ opcode then [0xFE, opcode - 0xFE00] else [opcode]

/-- The byte width of an operand, or `none` when its shape does not suit the operand kind or it
    needs a token. -/
def operandWidth (kind : OperandKind) (operand : RawOperand) : Option Nat :=
  match kind, operand with
  | .none, .none => some 0
  | .signed8, .integer _ | .unsigned8, .integer _ | .shortArgument, .argument _
  | .shortLocal, .local _ | .shortBranch, .target _ => some 1
  | .longArgument, .argument _ | .longLocal, .local _ => some 2
  | .signed32, .integer _ | .longBranch, .target _ => some 4
  | .signed64, .integer _ => some 8
  | .switch, .targets targets => some (4 + 4 * targets.length)
  | _, _ => none

/-- The byte size of one instruction. -/
def instructionSize (instruction : RawInstruction) : Option Nat := do
  let kind ← operandKind instruction.opcode
  let width ← operandWidth kind instruction.operand
  some ((opcodeBytes instruction.opcode).length + width)

/-- The byte offset of each instruction when the first starts at `start`. -/
def offsetsFrom (start : Nat) : List RawInstruction → Option (List Nat)
  | [] => some []
  | instruction :: rest => do
    let size ← instructionSize instruction
    let tail ← offsetsFrom (start + size) rest
    some (start :: tail)

/-- The operand bytes of an instruction that ends at byte `following`. Branch operands are
    relative to `following`. -/
def encodeOperand (offsets : List Nat) (following : Nat) (kind : OperandKind)
    (operand : RawOperand) : Option (List Nat) :=
  let relative (pc : Nat) : Option Int :=
    (offsets[pc]?).map fun target => (target : Int) - following
  match kind, operand with
  | .none, .none => some []
  | .signed8, .integer value | .unsigned8, .integer value => some (littleEndian 1 value)
  | .signed32, .integer value => some (littleEndian 4 value)
  | .signed64, .integer value => some (littleEndian 8 value)
  | .shortArgument, .argument index | .shortLocal, .local index => some (littleEndian 1 index)
  | .longArgument, .argument index | .longLocal, .local index => some (littleEndian 2 index)
  | .shortBranch, .target pc => (relative pc).map fun value => littleEndian 1 value
  | .longBranch, .target pc => (relative pc).map fun value => littleEndian 4 value
  | .switch, .targets pcs => do
    let values ← pcs.mapM relative
    some (littleEndian 4 pcs.length ++ (values.map (littleEndian 4)).flatten)
  | _, _ => none

/-- The bytes of the instructions at the given offsets. -/
def encodeCode (offsets : List Nat) : List (RawInstruction × Nat) → Option (List Nat)
  | [] => some []
  | (instruction, offset) :: rest => do
    let kind ← operandKind instruction.opcode
    let width ← operandWidth kind instruction.operand
    let following := offset + (opcodeBytes instruction.opcode).length + width
    let operandBytes ← encodeOperand offsets following kind instruction.operand
    let restBytes ← encodeCode offsets rest
    some (opcodeBytes instruction.opcode ++ operandBytes ++ restBytes)

/-! ## Metadata -/

/-- The element type byte of each primitive the encoder writes. -/
def primitiveBytes : List (String × Nat) :=
  [("System.Boolean", 0x02), ("System.Char", 0x03), ("System.SByte", 0x04), ("System.Byte", 0x05),
   ("System.Int16", 0x06), ("System.UInt16", 0x07), ("System.Int32", 0x08),
   ("System.UInt32", 0x09), ("System.Int64", 0x0A), ("System.UInt64", 0x0B),
   ("System.Single", 0x0C), ("System.Double", 0x0D), ("System.IntPtr", 0x18),
   ("System.UIntPtr", 0x19), ("System.Object", 0x1C)]

/-- The signature bytes of a type of a method with `arity` generic parameters. -/
def typeBytes (arity : Nat) : TypeExpr → Option (List Nat)
  | .void => some [0x01]
  | .atom scope name =>
    if scope == runtimeScope then (primitiveBytes.lookup name).map fun code => [code] else none
  | .object scope name =>
    if scope == runtimeScope && name == "System.String" then some [0x0E] else none
  | .byref element => (0x10 :: ·) <$> typeBytes arity element
  | .pointer element => (0x0F :: ·) <$> typeBytes arity element
  | .array element => (0x1D :: ·) <$> typeBytes arity element
  | .parameter number => some (if number < arity then [0x1E, number] else [0x13, number - arity])
  | _ => none

/-- The signature blob of a method: convention, generic arity, parameter count, result and
    parameters. -/
def methodBytes (method : RawMethod) : Option (List Nat) := do
  let arity := method.genericParameters.length
  let convention := method.callingConvention + (if method.hasThis then 0x20 else 0) +
    (if method.explicitThis then 0x40 else 0)
  let result ← typeBytes arity method.returnType
  let parameters ← method.parameters.mapM (typeBytes arity)
  some ([convention] ++ (if method.callingConvention / 0x10 % 2 == 1 then [arity] else []) ++
    [parameters.length] ++ result ++ parameters.flatten)

/-- The part of `owner` after `identity ++ "::"`. -/
def ownerName (identity owner : List Nat) : Option (List Nat) :=
  if owner.take (identity.length + 2) == identity ++ [58, 58] then
    some (owner.drop (identity.length + 2))
  else none

/-- The metadata of one method in an assembly of the given pin: `System.Runtime` for the primitive
    types, the owner class `Fixture`-style, the method itself and its locals. The result is the
    slice and the token of the locals signature, or 0. -/
def methodMetadata (pin : AssemblyPin) (method : RawMethod) : Option (MetadataSlice × Nat) := do
  let identity := bytesOf pin.identity
  let typeName ← ownerName identity (bytesOf method.owner)
  let assemblyName := identity.takeWhile (· != 44)
  if method.token != tokenOf Table.methodDef 1 then none
  let arity := method.genericParameters.length
  let signature ← methodBytes method
  let locals ← method.locals.mapM (typeBytes arity)
  let step : Step Nat := do
    let runtimeName ← string "System.Runtime"
    let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
    let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
    modify fun builder => { builder with corlib := 1 }
    let objectName ← string "Object"
    let systemName ← string "System"
    let _ ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
    let moduleName ← string "<Module>"
    let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
    let ownerNameOffset ← stringBytes typeName
    let owner ← row Table.typeDef [1, ownerNameOffset, 0, 1 * 4 + 1, 1, 1]
    let methodName ← string "M"
    let methodBlob ← blob signature
    let definition ← row Table.methodDef
      [0, method.implementation, method.attributes, methodName, methodBlob, 1]
    link linkDeclaring definition 0 owner
    let parameterName ← string "T"
    let ownerRows ← method.ownerParameters.zipIdx.mapM fun (parameter, number) =>
      row Table.genericParam [number, parameter.flags, (owner - 0x02000000) * 2, parameterName]
    if let some first := ownerRows.head? then link linkGenericParams owner 0 first
    let methodRows ← method.genericParameters.zipIdx.mapM fun (parameter, number) =>
      row Table.genericParam [number, parameter.flags,
        (definition - 0x06000000) * 2 + 1, parameterName]
    if let some first := methodRows.head? then link linkGenericParams definition 0 first
    if locals.isEmpty then pure 0 else
      let localBlob ← blob ([0x07, locals.length] ++ locals.flatten)
      row Table.standAloneSig [localBlob]
  some (build step assemblyName pin.identity)

/-- The evidence for body bytes and token claims over `metadata`: the identities, tables and
    names the decoder derives from the metadata for `method`, which a body that does not
    resolve leaves empty so the check refuses it. -/
def evidenceOf (bytes : List Nat) (operands : List (Nat × RawOperand)) (metadata : MethodMetadata)
    (method : RawMethod) : BodyEvidence :=
  let identities := metadata.slices.map fun slice => (slice.assembly.spelling).toOption.getD []
  let tables := metadata.tables.toOption.getD []
  let names := match metadata.environmentWith identities tables [] with
    | .ok env => (methodIdentityValid env method [] []).toOption.getD {}
    | .error _ => {}
  { bytes := bytes, tokens := { operands := operands }, metadata, identities, tables, names,
    pinned := [] }

/-- A body that decodes to the method: a tiny header when the method has no locals, the fixed
    stack depth and no init flag, and a fat header otherwise, with the metadata the method's
    definition and locals are checked against. -/
def encodeBody (pin : AssemblyPin) (method : RawMethod) : Option BodyEvidence := do
  let offsets ← offsetsFrom 0 method.code
  let code ← encodeCode offsets (method.code.zip offsets)
  let (slice, signature) ← methodMetadata pin method
  let tiny := method.locals.isEmpty && !method.initLocals && method.maxStack == tinyMaxStack &&
    code.length < 64
  let flags := 0x03 + (if method.initLocals then 0x10 else 0)
  let header :=
    if tiny then [code.length * 4 + 2]
    else [flags % 256, 0x30 + flags / 256] ++ littleEndian 2 method.maxStack ++
      littleEndian 4 code.length ++ littleEndian 4 signature
  some (evidenceOf (header ++ code) [] { own := slice } method)

/-- The method with the instruction offsets its encoded bytes imply; unchanged if it has no
    encoding. -/
def realizeOffsets (method : RawMethod) : RawMethod :=
  match offsetsFrom 0 method.code with
  | some offsets =>
    { method with code := (method.code.zip offsets).map fun (instruction, offset) =>
        { instruction with offset := offset } }
  | none => method

/-- The evidence with real offsets in its original and closed bodies, the bytes and metadata of
    its original body and the signature its row spells. An unencodable body keeps the evidence's
    own `body`, which then fails the check, so a fixture needs one positive check that its
    evidence has its bytes. -/
def withBody (item : MethodEvidence) : MethodEvidence :=
  let original := realizeOffsets item.original
  let body := (encodeBody item.assembly original).getD item.body
  { item with original := original, closed := realizeOffsets item.closed, body := body,
              signature := (spelled? body.names.signature).getD item.signature }

/-- The body of evidence that `withBody` has not yet filled in; it never decodes. -/
def noBody : BodyEvidence :=
  { bytes := [], tokens := { operands := [] }, metadata := {}, identities := [], tables := [],
    names := {}, pinned := [] }

end Tests.BodyEncoding
