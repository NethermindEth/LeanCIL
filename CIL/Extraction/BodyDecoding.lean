import CIL.Extraction.MetadataBinding
import Std.Data.TreeMap

/-!
# Method body decoding

`decodeBody` reads the exact bytes of an ECMA-335 method body (II.25.4): the tiny or fat
header and the instruction stream (III and VI.C). `BodyDecodes` states that the result is the
`maxStack`, `initLocals`, `locals` and `code` of a `RawMethod`, so an extractor's decoded
definition cannot differ from the bytes it was read from.

A `TokenTable` says which decoded operand each metadata token resolves to in this method. The
decoder ties every operand to the four token bytes in the body, and `MetadataBinding` checks
each table entry, the local variable types the header's signature token names and the method's
own definition against the metadata rows the body carries. That the carried rows are the image's
rows, the PE container and definitions in platform assemblies stay trusted.

Opcodes use the numbering of `RawInstruction`: one-byte opcodes keep their byte and two-byte
opcodes `0xFE nn` are `0xFE00 + nn`. Branch operands become instruction indices, and a branch may
not enter a prefixed instruction after its first prefix. A body with extra sections (exception
handlers) is rejected, since the model has none.
-/

namespace CIL.Extraction

/-- How the operand that follows an opcode is encoded. Variable operands split by short or
    long form and by argument or local, since the opcode decides which one is meant. -/
inductive OperandKind where
  | none
  | signed8
  | unsigned8
  | signed32
  | signed64
  | float32
  | float64
  | shortArgument
  | longArgument
  | shortLocal
  | longLocal
  | shortBranch
  | longBranch
  | switch
  | method
  | field
  | type
  | string
  | signature
  | token
  deriving DecidableEq, Repr

/-- The operand encoding of every opcode in the ECMA-335 table, or `none` for a byte that is
    not an opcode. Each comment names the opcodes of the row below it. -/
def operandKind : Nat → Option OperandKind
  -- nop, break, ldarg.0, ldarg.1, ldarg.2, ldarg.3
  | 0x00 | 0x01 | 0x02 | 0x03 | 0x04 | 0x05
  -- ldloc.0, ldloc.1, ldloc.2, ldloc.3, stloc.0, stloc.1
  | 0x06 | 0x07 | 0x08 | 0x09 | 0x0A | 0x0B
  -- stloc.2, stloc.3, ldnull, ldc.i4.m1, ldc.i4.0, ldc.i4.1
  | 0x0C | 0x0D | 0x14 | 0x15 | 0x16 | 0x17
  -- ldc.i4.2, ldc.i4.3, ldc.i4.4, ldc.i4.5, ldc.i4.6, ldc.i4.7
  | 0x18 | 0x19 | 0x1A | 0x1B | 0x1C | 0x1D
  -- ldc.i4.8, dup, pop, ret, ldind.i1, ldind.u1
  | 0x1E | 0x25 | 0x26 | 0x2A | 0x46 | 0x47
  -- ldind.i2, ldind.u2, ldind.i4, ldind.u4, ldind.i8, ldind.i
  | 0x48 | 0x49 | 0x4A | 0x4B | 0x4C | 0x4D
  -- ldind.r4, ldind.r8, ldind.ref, stind.ref, stind.i1, stind.i2
  | 0x4E | 0x4F | 0x50 | 0x51 | 0x52 | 0x53
  -- stind.i4, stind.i8, stind.r4, stind.r8, add, sub
  | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59
  -- mul, div, div.un, rem, rem.un, and
  | 0x5A | 0x5B | 0x5C | 0x5D | 0x5E | 0x5F
  -- or, xor, shl, shr, shr.un, neg
  | 0x60 | 0x61 | 0x62 | 0x63 | 0x64 | 0x65
  -- not, conv.i1, conv.i2, conv.i4, conv.i8, conv.r4
  | 0x66 | 0x67 | 0x68 | 0x69 | 0x6A | 0x6B
  -- conv.r8, conv.u4, conv.u8, conv.r.un, throw, conv.ovf.i1.un
  | 0x6C | 0x6D | 0x6E | 0x76 | 0x7A | 0x82
  -- conv.ovf.i2.un, conv.ovf.i4.un, conv.ovf.i8.un, conv.ovf.u1.un, conv.ovf.u2.un, conv.ovf.u4.un
  | 0x83 | 0x84 | 0x85 | 0x86 | 0x87 | 0x88
  -- conv.ovf.u8.un, conv.ovf.i.un, conv.ovf.u.un, ldlen, ldelem.i1, ldelem.u1
  | 0x89 | 0x8A | 0x8B | 0x8E | 0x90 | 0x91
  -- ldelem.i2, ldelem.u2, ldelem.i4, ldelem.u4, ldelem.i8, ldelem.i
  | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97
  -- ldelem.r4, ldelem.r8, ldelem.ref, stelem.i, stelem.i1, stelem.i2
  | 0x98 | 0x99 | 0x9A | 0x9B | 0x9C | 0x9D
  -- stelem.i4, stelem.i8, stelem.r4, stelem.r8, stelem.ref, conv.ovf.i1
  | 0x9E | 0x9F | 0xA0 | 0xA1 | 0xA2 | 0xB3
  -- conv.ovf.u1, conv.ovf.i2, conv.ovf.u2, conv.ovf.i4, conv.ovf.u4, conv.ovf.i8
  | 0xB4 | 0xB5 | 0xB6 | 0xB7 | 0xB8 | 0xB9
  -- conv.ovf.u8, ckfinite, conv.u2, conv.u1, conv.i, conv.ovf.i
  | 0xBA | 0xC3 | 0xD1 | 0xD2 | 0xD3 | 0xD4
  -- conv.ovf.u, add.ovf, add.ovf.un, mul.ovf, mul.ovf.un, sub.ovf
  | 0xD5 | 0xD6 | 0xD7 | 0xD8 | 0xD9 | 0xDA
  -- sub.ovf.un, endfinally, stind.i, conv.u, arglist, ceq
  | 0xDB | 0xDC | 0xDF | 0xE0 | 0xFE00 | 0xFE01
  -- cgt, cgt.un, clt, clt.un, localloc, endfilter
  | 0xFE02 | 0xFE03 | 0xFE04 | 0xFE05 | 0xFE0F | 0xFE11
  -- volatile., tail., cpblk, initblk, rethrow, refanytype
  | 0xFE13 | 0xFE14 | 0xFE17 | 0xFE18 | 0xFE1A | 0xFE1D
  -- readonly.
  | 0xFE1E => some .none
  -- ldc.i4.s
  | 0x1F => some .signed8
  -- unaligned., no.
  | 0xFE12 | 0xFE19 => some .unsigned8
  -- ldc.i4
  | 0x20 => some .signed32
  -- ldc.i8
  | 0x21 => some .signed64
  -- ldc.r4
  | 0x22 => some .float32
  -- ldc.r8
  | 0x23 => some .float64
  -- ldarg.s, ldarga.s, starg.s
  | 0x0E | 0x0F | 0x10 => some .shortArgument
  -- ldarg, ldarga, starg
  | 0xFE09 | 0xFE0A | 0xFE0B => some .longArgument
  -- ldloc.s, ldloca.s, stloc.s
  | 0x11 | 0x12 | 0x13 => some .shortLocal
  -- ldloc, ldloca, stloc
  | 0xFE0C | 0xFE0D | 0xFE0E => some .longLocal
  -- br.s, brfalse.s, brtrue.s, beq.s, bge.s, bgt.s
  | 0x2B | 0x2C | 0x2D | 0x2E | 0x2F | 0x30
  -- ble.s, blt.s, bne.un.s, bge.un.s, bgt.un.s, ble.un.s
  | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 | 0x36
  -- blt.un.s, leave.s
  | 0x37 | 0xDE => some .shortBranch
  -- br, brfalse, brtrue, beq, bge, bgt
  | 0x38 | 0x39 | 0x3A | 0x3B | 0x3C | 0x3D
  -- ble, blt, bne.un, bge.un, bgt.un, ble.un
  | 0x3E | 0x3F | 0x40 | 0x41 | 0x42 | 0x43
  -- blt.un, leave
  | 0x44 | 0xDD => some .longBranch
  -- switch
  | 0x45 => some .switch
  -- jmp, call, callvirt, newobj, ldftn, ldvirtftn
  | 0x27 | 0x28 | 0x6F | 0x73 | 0xFE06 | 0xFE07 => some .method
  -- ldfld, ldflda, stfld, ldsfld, ldsflda, stsfld
  | 0x7B | 0x7C | 0x7D | 0x7E | 0x7F | 0x80 => some .field
  -- cpobj, ldobj, castclass, isinst, unbox, stobj
  | 0x70 | 0x71 | 0x74 | 0x75 | 0x79 | 0x81
  -- box, newarr, ldelema, ldelem.any, stelem.any, unbox.any
  | 0x8C | 0x8D | 0x8F | 0xA3 | 0xA4 | 0xA5
  -- refanyval, mkrefany, initobj, constrained., sizeof
  | 0xC2 | 0xC6 | 0xFE15 | 0xFE16 | 0xFE1C => some .type
  -- ldstr
  | 0x72 => some .string
  -- calli
  | 0x29 => some .signature
  -- ldtoken
  | 0xD0 => some .token
  | _ => none

/-- The extractor's claim of the operand each metadata token resolves to in this method. -/
structure TokenTable where
  operands : List (Nat × RawOperand)
  deriving DecidableEq, Repr

/-- The exact bytes of one method body, its header and code but not its extra sections, each
    byte a `Nat` below 256, with the token table its operands resolve through, the metadata
    those tokens are checked against and the lookup tables of that metadata. -/
structure BodyEvidence where
  bytes : List Nat
  tokens : TokenTable
  metadata : MethodMetadata
  /-- The identity each slice's assembly spells, in the slices' order; `AssembliesIdentified`
      ties them to the assemblies' bytes once per assembly. -/
  identities : List (List Nat)
  /-- `MetadataSlice.tables` of each slice of `metadata`, built once for the extraction. -/
  tables : List IndexTables
  /-- The owner and base class names the method's definition resolves to. -/
  names : MethodNames
  /-- The identity of every assembly the extraction pins, as bytes; `BodyDecodes` ties them to
      the pins. A reference into one of them needs its slice among `metadata`. -/
  pinned : List (List Nat)
  deriving DecidableEq, Repr

/-- What a body's bytes say about its method: the fields `RawMethod` takes from the body, and
    the token of the local-variable signature the locals are checked against. -/
structure DecodedBody where
  maxStack : Nat
  initLocals : Bool
  localSignature : Nat
  code : List RawInstruction
  deriving DecidableEq, Repr

/-- Why a body does not decode. Offsets are byte offsets of the instruction within the code. -/
inductive BodyError where
  | invalidByte
  | truncatedHeader
  | truncatedOpcode (offset : Nat)
  | unsupportedHeader (flags : Nat)
  | extraSections
  | codeSizeMismatch (declared supplied : Nat)
  | duplicateToken (token : Nat)
  | metadata (error : MetadataError)
  | unknownOpcode (offset opcode : Nat)
  | truncatedOperand (offset : Nat)
  | missingToken (offset token : Nat)
  | mismatchedToken (offset token : Nat)
  | branchOutsideBody (offset : Nat)
  | branchIntoInstruction (offset target : Nat)
  | branchIntoPrefixed (offset target : Nat)
  deriving DecidableEq, Repr

/-- Tokens naming a method: MethodDef, MemberRef or MethodSpec. -/
private def methodTable (table : Nat) : Bool := table == 0x06 || table == 0x0A || table == 0x2B

/-- Tokens naming a field: Field or MemberRef. -/
private def fieldTable (table : Nat) : Bool := table == 0x04 || table == 0x0A

/-- Tokens naming a type: TypeRef, TypeDef or TypeSpec. -/
private def typeTable (table : Nat) : Bool := table == 0x01 || table == 0x02 || table == 0x1B

/-- Whether a token of metadata table `table` may supply `operand` to an opcode whose operand
    kind is `kind`; a user string is table `0x70` and a standalone signature is `0x11`. -/
def tokenAdmits (kind : OperandKind) (table : Nat) (operand : RawOperand) : Bool :=
  match kind, operand with
  | .method, .call _ => methodTable table
  | .field, .field .. => fieldTable table
  | .type, .type _ => typeTable table
  | .string, .text _ => table == 0x70
  | .signature, .indirectCall .. => table == 0x11
  | .token, .call _ => methodTable table
  | .token, .field .. => fieldTable table
  | .token, .type _ => typeTable table
  | _, _ => false

/-- The little-endian value of the next `width` bytes, and the bytes after them. -/
private def readUnsigned (offset : Nat) :
    Nat → List Nat → Except BodyError (Nat × List Nat)
  | 0, rest => .ok (0, rest)
  | width + 1, byte :: rest => do
    let (high, tail) ← readUnsigned offset width rest
    .ok (byte + 256 * high, tail)
  | _ + 1, [] => .error (.truncatedOperand offset)

/-- The two's-complement integer of `width` bytes whose unsigned value is `value`. -/
private def signedOf (width value : Nat) : Int :=
  if value < 2 ^ (8 * width - 1) then (value : Int) else (value : Int) - 2 ^ (8 * width)

/-- The absolute byte offset a branch reaches from the end of its instruction. -/
private def branchTarget (offset following : Nat) (relative : Int) : Except BodyError Nat :=
  if 0 ≤ (following : Int) + relative then .ok ((following : Int) + relative).toNat
  else .error (.branchOutsideBody offset)

/-- The next `count` signed 32-bit values, and the bytes after them. -/
private def readRelatives (offset : Nat) :
    Nat → List Nat → Except BodyError (List Int × List Nat)
  | 0, rest => .ok ([], rest)
  | count + 1, rest => do
    let (value, tail) ← readUnsigned offset 4 rest
    let (values, remaining) ← readRelatives offset count tail
    .ok (signedOf 4 value :: values, remaining)

/-- An operand read as one fixed-width unsigned value and built from it. -/
private def readValue (offset start width : Nat) (build : Nat → RawOperand)
    (rest : List Nat) :
    Except BodyError (RawOperand × Nat × List Nat) := do
  let (value, tail) ← readUnsigned offset width rest
  .ok (build value, start + width, tail)

/-- A branch operand of `width` bytes; the target stays an absolute byte offset until the
    instruction offsets are known. -/
private def readBranch (offset start width : Nat) (rest : List Nat) :
    Except BodyError (RawOperand × Nat × List Nat) := do
  let (value, tail) ← readUnsigned offset width rest
  let target ← branchTarget offset (start + width) (signedOf width value)
  .ok (.target target, start + width, tail)

/-- A `switch` operand: its count, then one offset per case relative to the end of the table. -/
private def readSwitch (offset start : Nat) (rest : List Nat) :
    Except BodyError (RawOperand × Nat × List Nat) := do
  let (count, afterCount) ← readUnsigned offset 4 rest
  let following := start + 4 + 4 * count
  let (relatives, tail) ← readRelatives offset count afterCount
  let targets ← relatives.mapM (branchTarget offset following)
  .ok (.targets targets, following, tail)

/-- A token operand: the four token bytes, the operand the table gives them, and the check that
    the token's metadata table suits the opcode. -/
private def readToken (tokens : Std.TreeMap Nat (RawOperand × TokenFacts)) (offset start : Nat)
    (opcode : Nat) (kind : OperandKind) (rest : List Nat) :
    Except BodyError (RawOperand × Nat × List Nat) := do
  let (token, tail) ← readUnsigned offset 4 rest
  let some (operand, facts) := tokens[token]? | throw (.missingToken offset token)
  if !tokenAdmits kind (metadataTableOf token) operand || !checkSite opcode facts operand then
    throw (.mismatchedToken offset token)
  .ok (operand, start + 4, tail)

/-- Decode the operand that starts at byte offset `start`, returning it, the offset after it
    and the remaining bytes. Branch operands carry absolute byte offsets. -/
private def decodeOperand (tokens : Std.TreeMap Nat (RawOperand × TokenFacts))
    (offset start opcode : Nat) :
    OperandKind → List Nat → Except BodyError (RawOperand × Nat × List Nat)
  | .none, rest => .ok (.none, start, rest)
  | .signed8, rest => readValue offset start 1 (fun value => .integer (signedOf 1 value)) rest
  | .unsigned8, rest => readValue offset start 1 (fun value => .integer value) rest
  | .signed32, rest => readValue offset start 4 (fun value => .integer (signedOf 4 value)) rest
  | .signed64, rest => readValue offset start 8 (fun value => .integer (signedOf 8 value)) rest
  | .float32, rest =>
    readValue offset start 4 (fun value => .text ("float:" ++ toString (signedOf 4 value))) rest
  | .float64, rest =>
    readValue offset start 8 (fun value => .text ("double:" ++ toString (signedOf 8 value))) rest
  | .shortArgument, rest => readValue offset start 1 .argument rest
  | .longArgument, rest => readValue offset start 2 .argument rest
  | .shortLocal, rest => readValue offset start 1 .local rest
  | .longLocal, rest => readValue offset start 2 .local rest
  | .shortBranch, rest => readBranch offset start 1 rest
  | .longBranch, rest => readBranch offset start 4 rest
  | .switch, rest => readSwitch offset start rest
  | kind, rest => readToken tokens offset start opcode kind rest

/-- The opcode at the front of the bytes, its width in bytes and the bytes after it. -/
private def readOpcode (offset : Nat) : List Nat → Except BodyError (Nat × Nat × List Nat)
  | [] => .error (.truncatedOpcode offset)
  | 0xFE :: second :: rest => .ok (0xFE00 + second, 2, rest)
  | [0xFE] => .error (.truncatedOpcode offset)
  | first :: rest => .ok (first, 1, rest)

/-- Decode the instruction stream starting at byte `offset`. `fuel` is the byte count, which
    bounds the instruction count since each instruction takes at least one byte. Branch operands
    carry absolute byte offsets. -/
private def decodeInstructions (tokens : Std.TreeMap Nat (RawOperand × TokenFacts)) :
    Nat → Nat → List Nat → Except BodyError (List RawInstruction)
  | _, _, [] => .ok []
  | 0, offset, _ => .error (.truncatedOperand offset)
  | fuel + 1, offset, bytes => do
    let (opcode, width, afterOpcode) ← readOpcode offset bytes
    let some kind := operandKind opcode | throw (.unknownOpcode offset opcode)
    let (operand, following, remaining) ←
      decodeOperand tokens offset (offset + width) opcode kind afterOpcode
    let rest ← decodeInstructions tokens fuel following remaining
    .ok ({ offset := offset, opcode := opcode, operand := operand } :: rest)

/-- The opcodes that prefix the instruction after them: `unaligned.`, `volatile.`, `tail.`,
    `constrained.`, `no.` and `readonly.`. -/
def isPrefixOpcode (opcode : Nat) : Bool :=
  opcode == 0xFE12 || opcode == 0xFE13 || opcode == 0xFE14 || opcode == 0xFE16 ||
    opcode == 0xFE19 || opcode == 0xFE1E

/-- Map each instruction's start offset to its index and to whether a prefix opcode precedes
    it. -/
private def indexStarts : List RawInstruction → Nat → Bool → Std.TreeMap Nat (Nat × Bool) →
    Std.TreeMap Nat (Nat × Bool)
  | [], _, _, starts => starts
  | instruction :: rest, index, afterPrefix, starts =>
    indexStarts rest (index + 1) (isPrefixOpcode instruction.opcode)
      (starts.insert instruction.offset (index, afterPrefix))

/-- Replace a branch's absolute byte offset by the index of the instruction starting there. The
    target must lie inside the code, start an instruction, and not follow a prefix: control may
    enter a prefixed instruction only at its first prefix (ECMA-335 III.2). -/
private def instructionIndex (starts : Std.TreeMap Nat (Nat × Bool))
    (codeLength offset target : Nat) : Except BodyError Nat :=
  if codeLength ≤ target then .error (.branchOutsideBody offset)
  else match starts[target]? with
    | some (index, false) => .ok index
    | some (_, true) => .error (.branchIntoPrefixed offset target)
    | none => .error (.branchIntoInstruction offset target)

/-- Turn the absolute branch offsets of one instruction into instruction indices. -/
private def resolveBranches (starts : Std.TreeMap Nat (Nat × Bool)) (codeLength : Nat)
    (instruction : RawInstruction) : Except BodyError RawInstruction :=
  match instruction.operand with
  | .target target => do
    let index ← instructionIndex starts codeLength instruction.offset target
    .ok { instruction with operand := .target index }
  | .targets targets => do
    let indices ← targets.mapM (instructionIndex starts codeLength instruction.offset)
    .ok { instruction with operand := .targets indices }
  | _ => .ok instruction
/-- The fields of a method body header. -/
structure BodyHeader where
  maxStack : Nat
  initLocals : Bool
  codeSize : Nat
  localSignature : Nat

/-- A tiny header carries no locals and the CLR's fixed evaluation stack depth. -/
def tinyMaxStack : Nat := 8

/-- Decode the tiny or fat header (II.25.4.2 and II.25.4.3), returning the bytes after it. A fat
    header must be three words long, set only the init-locals flag and have no extra sections. -/
private def decodeHeader : List Nat → Except BodyError (BodyHeader × List Nat)
  | [] => .error .truncatedHeader
  | first :: rest =>
    if first % 4 == 2 then
      .ok ({ maxStack := tinyMaxStack, initLocals := false, codeSize := first / 4,
             localSignature := 0 }, rest)
    else if first % 4 == 3 then
      match rest with
      | second :: stack0 :: stack1 :: size0 :: size1 :: size2 :: size3 ::
          token0 :: token1 :: token2 :: token3 :: code =>
        let flags := first + 256 * (second % 16)
        if second / 16 != 3 then .error (.unsupportedHeader flags)
        else if flags / 8 % 2 == 1 then .error .extraSections
        else if flags != 0x03 && flags != 0x13 then .error (.unsupportedHeader flags)
        else .ok ({ maxStack := stack0 + 256 * stack1, initLocals := flags == 0x13,
                    codeSize := size0 + 256 * (size1 + 256 * (size2 + 256 * size3)),
                    localSignature := token0 + 256 * (token1 + 256 * (token2 + 256 * token3)) },
                  code)
      | _ => .error .truncatedHeader
    else .error (.unsupportedHeader first)

/-- The checked table of a body: every entry is checked against the metadata, and no token has
    two entries. -/
private def checkTable (env : MetadataEnv) (frame : Frame) :
    List (Nat × RawOperand) → Std.TreeMap Nat (RawOperand × TokenFacts) →
      Except BodyError (Std.TreeMap Nat (RawOperand × TokenFacts))
  | [], table => .ok table
  | (token, operand) :: rest, table => do
    if table.contains token then throw (.duplicateToken token)
    let facts ← (checkEntryIn env frame token operand).mapError BodyError.metadata
    checkTable env frame rest (table.insert token (operand, facts))

/-- The metadata of a body as an environment of indexed slices, its own first, over the given
    identities and tables: independent of the number of rows. -/
def MethodMetadata.environmentWith (metadata : MethodMetadata) (identities : List (List Nat))
    (tables : List IndexTables) (pinned : List (List Nat)) : Except MetadataError MetadataEnv :=
  if tables.length != metadata.others.length + 1 || identities.length != tables.length then
    .error .tablesMismatch
  else do
    let indexed ← (metadata.slices.zip (identities.zip tables)).mapM
      fun (slice, identity, sliceTables) => slice.indexWith sliceTables identity
    .ok { slices := indexed, pinned := pinned }

/-- The metadata of a body as an environment of indexed slices, built from its bytes alone. -/
def MethodMetadata.environment (metadata : MethodMetadata) (pinned : List (List Nat) := []) :
    Except MetadataError MetadataEnv := do
  .ok { slices := ← metadata.slices.mapM MetadataSlice.index, pinned := pinned }

/-- Decode a method body: its header and its instructions, with branch operands as instruction
    indices and every token operand checked against the metadata. `arity` is the number of
    generic parameters of the method. The supplied bytes must be exactly the header and the
    declared code. -/
def decodeBody (env : MetadataEnv) (arity : Nat) (body : BodyEvidence) :
    Except BodyError DecodedBody := do
  if !body.bytes.all (· < 256) then throw .invalidByte
  let (header, code) ← decodeHeader body.bytes
  if code.length != header.codeSize then
    throw (.codeSizeMismatch header.codeSize code.length)
  let frame ← (env.frame arity).mapError BodyError.metadata
  let tokens ← checkTable env frame body.tokens.operands ∅
  let raw ← decodeInstructions tokens code.length 0 code
  let starts := indexStarts raw 0 false ∅
  let instructions ← raw.mapM (resolveBranches starts code.length)
  .ok { maxStack := header.maxStack, initLocals := header.initLocals,
        localSignature := header.localSignature, code := instructions }

/-- The method's definition, its locals and its body, each checked against the metadata the
    body carries: the decoded body, when everything agrees with the method. -/
def checkBody (body : BodyEvidence) (method : RawMethod) : Except BodyError DecodedBody := do
  let env ← (body.metadata.environmentWith body.identities body.tables body.pinned).mapError
    BodyError.metadata
  let names ← (methodIdentityValid env method).mapError BodyError.metadata
  if names != body.names then throw (.metadata (.methodMismatch method.token))
  let decoded ← decodeBody env method.genericParameters.length body
  (checkLocals env method.genericParameters.length decoded.localSignature method.locals).mapError
    BodyError.metadata
  .ok decoded

/-- Whether the body decodes to exactly the method's `maxStack`, `initLocals` and `code`, with
    the method's definition and locals agreeing with the metadata. Only the kernel decides it:
    the elaborator's default reduction evaluates a call by name and would unfold the decoder,
    the metadata slices and every token's resolution without sharing, so the definition is
    irreducible and `decide` fails at once; `decide +kernel` evaluates it. -/
@[irreducible] def bodyMatches (body : BodyEvidence) (method : RawMethod) : Bool :=
  match checkBody body method with
  | .ok decoded => decoded.maxStack == method.maxStack &&
      decoded.initLocals == method.initLocals && decoded.code == method.code
  | .error _ => false

/-- The body's tables are what its metadata bytes give, and the method's definition, locals,
    `maxStack`, `initLocals` and `code` are what the body bytes and the metadata say, through the
    body's token table. Names are tied to bytes by equations, so no decision evaluates a string:
    each slice's assembly spells the identity the body lists, the method's own assembly is the
    pin, the pinned identities the body lists are those of the extraction's pins, and the
    owner and base class names the metadata resolves are the ones the method states. -/
abbrev BodyDecodes (pins : List AssemblyPin) (pin : AssemblyPin) (body : BodyEvidence)
    (method : RawMethod) : Prop :=
  AssembliesIdentified body.metadata body.identities ∧
    tablesMatch body.metadata body.tables = true ∧
    body.metadata.own.assembly.identity = pin.identity ∧
    body.pinned.mapM spelled? = some (pins.map (·.identity)) ∧
    body.names.Spell method ∧ bodyMatches body method = true



end CIL.Extraction