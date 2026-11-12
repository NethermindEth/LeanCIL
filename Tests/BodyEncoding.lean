import CIL.Extraction.Translation

/-!
# Method body encoding for tests

Fixtures that build a `RawMethod` by hand need method-body bytes that decode to it, since
`MethodEvidenceValid` checks the bytes. `encodeBody` writes the bytes and the token table of a
raw method, `realizeOffsets` gives its instructions the byte offsets those bytes imply, and
`withBody` applies both to a `MethodEvidence`. The encoder serves tests only: nothing trusts it,
because the decoder re-reads every byte it writes.

Float constants (`.text "float:.."`) are not encoded; `encodeBody` returns `none` for them.
-/

namespace Tests.BodyEncoding

open CIL CIL.Extraction

/-- The first token of the local-variable signature table, used when a method has locals. -/
def localSignatureToken : Nat := 0x11000001

/-- The `width` little-endian bytes of the two's-complement encoding of `value`. -/
def littleEndian (width : Nat) (value : Int) : List Nat :=
  let unsigned := (value % ((2 ^ (8 * width) : Nat) : Int)).toNat
  (List.range width).map fun position => unsigned / 256 ^ position % 256

/-- The opcode bytes: one byte, or `0xFE` and the second byte for `0xFE00 + nn`. -/
def opcodeBytes (opcode : Nat) : List Nat :=
  if 0xFE00 ≤ opcode then [0xFE, opcode - 0xFE00] else [opcode]

/-- The metadata table whose token an operand of this kind and shape is encoded with. -/
def tokenTableFor : OperandKind → RawOperand → Option Nat
  | .method, .call _ => some 0x06
  | .field, .field .. => some 0x04
  | .type, .type _ => some 0x01
  | .string, .text _ => some 0x70
  | .signature, .indirectCall .. => some 0x11
  | .token, .call _ => some 0x06
  | .token, .field .. => some 0x04
  | .token, .type _ => some 0x01
  | _, _ => none

/-- The byte width of an operand, or `none` when its shape does not suit the operand kind. -/
def operandWidth (kind : OperandKind) (operand : RawOperand) : Option Nat :=
  match kind, operand with
  | .none, .none => some 0
  | .signed8, .integer _ | .unsigned8, .integer _ | .shortArgument, .argument _
  | .shortLocal, .local _ | .shortBranch, .target _ => some 1
  | .longArgument, .argument _ | .longLocal, .local _ => some 2
  | .signed32, .integer _ | .longBranch, .target _ => some 4
  | .signed64, .integer _ => some 8
  | .switch, .targets targets => some (4 + 4 * targets.length)
  | _, _ => (tokenTableFor kind operand).map fun _ => 4

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

/-- The token of an operand under a metadata table: the existing one, or the next row. -/
def tokenFor (table : Nat) (operand : RawOperand) (tokens : List (Nat × RawOperand)) :
    Nat × List (Nat × RawOperand) :=
  match tokens.find? fun entry => entry.2 == operand && metadataTableOf entry.1 == table with
  | some entry => (entry.1, tokens)
  | none =>
    let token := table * 0x1000000 + tokens.length + 1
    (token, tokens ++ [(token, operand)])

/-- The operand bytes of an instruction that ends at byte `following`, and the extended token
    table. Branch operands are relative to `following`. -/
def encodeOperand (offsets : List Nat) (following : Nat) (kind : OperandKind)
    (operand : RawOperand) (tokens : List (Nat × RawOperand)) :
    Option (List Nat × List (Nat × RawOperand)) :=
  let relative (pc : Nat) : Option Int :=
    (offsets[pc]?).map fun target => (target : Int) - following
  match kind, operand with
  | .none, .none => some ([], tokens)
  | .signed8, .integer value | .unsigned8, .integer value => some (littleEndian 1 value, tokens)
  | .signed32, .integer value => some (littleEndian 4 value, tokens)
  | .signed64, .integer value => some (littleEndian 8 value, tokens)
  | .shortArgument, .argument index | .shortLocal, .local index =>
    some (littleEndian 1 index, tokens)
  | .longArgument, .argument index | .longLocal, .local index =>
    some (littleEndian 2 index, tokens)
  | .shortBranch, .target pc => (relative pc).map fun value => (littleEndian 1 value, tokens)
  | .longBranch, .target pc => (relative pc).map fun value => (littleEndian 4 value, tokens)
  | .switch, .targets pcs => do
    let values ← pcs.mapM relative
    some (littleEndian 4 pcs.length ++ (values.map (littleEndian 4)).flatten, tokens)
  | _, _ => do
    let table ← tokenTableFor kind operand
    let (token, tokens) := tokenFor table operand tokens
    some (littleEndian 4 token, tokens)

/-- The bytes of the instructions at the given offsets, and the token table they need. -/
def encodeCode (offsets : List Nat) (tokens : List (Nat × RawOperand)) :
    List (RawInstruction × Nat) → Option (List Nat × List (Nat × RawOperand))
  | [] => some ([], tokens)
  | (instruction, offset) :: rest => do
    let kind ← operandKind instruction.opcode
    let width ← operandWidth kind instruction.operand
    let following := offset + (opcodeBytes instruction.opcode).length + width
    let (operandBytes, tokens) ← encodeOperand offsets following kind instruction.operand tokens
    let (restBytes, tokens) ← encodeCode offsets tokens rest
    some (opcodeBytes instruction.opcode ++ operandBytes ++ restBytes, tokens)

/-- A body that decodes to the method: a tiny header when the method has no locals, the fixed
    stack depth and no init flag, and a fat header otherwise. -/
def encodeBody (method : RawMethod) : Option BodyEvidence := do
  let offsets ← offsetsFrom 0 method.code
  let (code, operands) ← encodeCode offsets [] (method.code.zip offsets)
  let tiny := method.locals.isEmpty && !method.initLocals && method.maxStack == tinyMaxStack &&
    code.length < 64
  let signature := if method.locals.isEmpty then 0 else localSignatureToken
  let flags := 0x03 + (if method.initLocals then 0x10 else 0)
  let header :=
    if tiny then [code.length * 4 + 2]
    else [flags % 256, 0x30 + flags / 256] ++ littleEndian 2 method.maxStack ++
      littleEndian 4 code.length ++ littleEndian 4 signature
  some { bytes := header ++ code,
         tokens := { operands := operands, localSignature := signature, locals := method.locals } }

/-- The method with the instruction offsets its encoded bytes imply; unchanged if it has no
    encoding. -/
def realizeOffsets (method : RawMethod) : RawMethod :=
  match offsetsFrom 0 method.code with
  | some offsets =>
    { method with code := (method.code.zip offsets).map fun (instruction, offset) =>
        { instruction with offset := offset } }
  | none => method

/-- The evidence with real offsets in its original and closed bodies and the bytes of its
    original body. An unencodable body keeps the evidence's own `body`, which then fails the
    check, so a fixture needs one positive check that its evidence has its bytes. -/
def withBody (item : MethodEvidence) : MethodEvidence :=
  let original := realizeOffsets item.original
  { item with original := original, closed := realizeOffsets item.closed,
              body := (encodeBody original).getD item.body }

/-- The body of evidence that `withBody` has not yet filled in; it never decodes. -/
def noBody : BodyEvidence := { bytes := [], tokens := { operands := [], localSignature := 0,
                                                          locals := [] } }

end Tests.BodyEncoding
