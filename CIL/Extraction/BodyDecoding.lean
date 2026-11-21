import CIL.Extraction.MetadataBinding
import CIL.Extraction.PinnedIndex
import CIL.Extraction.Prefixes
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas

/-!
# Method body decoding

`decodeBody` reads the exact bytes of an ECMA-335 method body (II.25.4): the tiny or fat
header and the instruction stream (III and VI.C). `BodyDecodes` states that the result is the
`maxStack`, `initLocals`, `locals` and `code` of a `RawMethod`, so an extractor's decoded
definition cannot differ from the bytes it was read from.

A `TokenTable` says which decoded operand each metadata token resolves to in this method. The
decoder ties every operand to the four token bytes in the body, and `MetadataBinding` checks
each table entry, the local variable types the header's signature token names and the method's
own definition against the metadata rows the body carries, and reads what it relies on about a
type no carried slice defines from the body's platform definitions, which `BodyDecodes` equates
with the extraction's one list. That the carried rows are the image's rows and the PE container
stay trusted.

Opcodes use the numbering of `RawInstruction`: one-byte opcodes keep their byte and two-byte
opcodes `0xFE nn` are `0xFE00 + nn`. Branch operands become instruction indices, and a branch may
not enter a prefixed instruction after its first prefix, so the decoded code satisfies
`PrefixEntryFree` (`checkBody_prefixEntryFree`). A body with extra sections (exception
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

/-- The extraction's import slots and the sorted names of their published layouts. -/
structure ImportSlotIndex where
  slots : FlowIndex ImportSlot
  layouts : Array (List Nat)

/-- Index the verified slots by program position and their published layouts by full identity. -/
def ImportSlotIndex.ofList (imports : List ImportSlot) : ImportSlotIndex :=
  let names := imports.flatMap fun slot =>
    slot.layouts.published.map fun row => bytesOf row.identity
  { slots := FlowIndex.ofList imports, layouts := names.mergeSort.toArray }

/-- Static call slots at their direct-link pcs and the value layouts published by the imports. -/
structure BodyImports where
  calls : List (Prod Nat ImportSlot) := []
  layouts : Array (List Nat) := #[]
  deriving DecidableEq, Repr

/-- Only direct links into the import part of the program grant a call its export identity. -/
def ImportSlotIndex.forLinks (imports : ImportSlotIndex) (methodCount : Nat)
    (links : List (Prod Nat Link)) : BodyImports :=
  match imports.slots with
  | .empty => {}
  | slots =>
    let calls := links.filterMap fun (pc, link) => do
      let .direct target := link | none
      guard (methodCount <= target)
      return (pc, <- slots.get? (target - methodCount))
    { calls, layouts := imports.layouts }

/-- Each mention of an imported method in the instruction stream is a call at its linked pc. -/
def BodyImports.checkUses (bound : BodyImports)
    (identities : Std.TreeMap String ImportSlot) (code : List RawInstruction) : Bool :=
  let positions := Std.TreeMap.ofList bound.calls
  code.zipIdx.all fun (instruction, pc) =>
    match instruction.operand, positions[pc]? with
    | .call site, expected =>
      match site.target, expected with
      | .external name, some slot => instruction.opcode == 0x28 && slot.identity == name
      | .external name, none => !identities.contains name
      | .managed _, slot => slot.isNone
    | _, slot => slot.isNone

/-- Every use of a registered import identity has its own direct call at its linked pc. -/
theorem BodyImports.checked_call_has_link {bound : BodyImports}
    {identities : Std.TreeMap String ImportSlot} {code : List RawInstruction}
    {instruction : RawInstruction} {pc : Nat} {site : CallSite} {identity : String}
    (checked : bound.checkUses identities code = true)
    (atPc : Membership.mem code.zipIdx (instruction, pc))
    (operand : instruction.operand = .call site)
    (target : site.target = .external identity)
    (registered : identities.contains identity = true) :
    Exists fun slot => (Std.TreeMap.ofList bound.calls)[pc]? = some slot /\
      instruction.opcode = 0x28 /\ slot.identity = identity := by
  unfold BodyImports.checkUses at checked
  have accepted := List.all_eq_true.mp checked (instruction, pc) atPc
  cases entry : (Std.TreeMap.ofList bound.calls)[pc]? with
  | none => simp [operand, target, entry, registered] at accepted
  | some slot =>
    refine Exists.intro slot (And.intro rfl ?_)
    simpa [operand, target, entry] using accepted

#print axioms BodyImports.checked_call_has_link

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
  pinned : PinnedIndex
  /-- The platform definitions the checks read a type outside the carried slices from;
      `BodyDecodes` equates them with the extraction's. -/
  platform : PlatformTable := {}
  /-- The direct import links and published layout names bound by the translation certificate. -/
  imports : BodyImports := {}
  /-- The type arguments of a generic instance, method arguments first, as the types its
      signature names; empty for a method that is not an instance. -/
  instantiation : List InstanceArgument := []
  /-- The instruction index and token of each static field access and field `ldtoken` whose
      field a carried `Field` row defines, in code order; the decoder records the same list. -/
  statics : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-- What a body's bytes say about its method: the fields `RawMethod` takes from the body, and
    the token of the local-variable signature the locals are checked against. -/
structure DecodedBody where
  maxStack : Nat
  initLocals : Bool
  localSignature : Nat
  code : List RawInstruction
  /-- The instruction index and token of each static field access whose field a carried row
      defines, as `BodyEvidence.statics` lists them. -/
  statics : List (Nat × Nat)
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

/-- The token of a static field operand whose binding found the carried `Field` row defining
    it, read again from the operand bytes; `none` for any other operand. -/
private def boundStaticToken (tokens : Std.TreeMap Nat (RawOperand × TokenFacts)) (offset : Nat)
    (operand : RawOperand) (bytes : List Nat) : Option Nat :=
  match operand with
  | .field _ _ _ _ true => do
    let (token, _) ← (readUnsigned offset 4 bytes).toOption
    let (_, facts) ← tokens[token]?
    if facts.staticField == some true then some token else none
  | _ => none

/-- Decode the instruction stream starting at byte `offset`, the instruction numbered `index`,
    with the index and token of each bound static field operand. `fuel` is the byte count, which
    bounds the instruction count since each instruction takes at least one byte. Branch operands
    carry absolute byte offsets. -/
private def decodeInstructions (tokens : Std.TreeMap Nat (RawOperand × TokenFacts)) :
    Nat → Nat → Nat → List Nat → Except BodyError (List RawInstruction × List (Nat × Nat))
  | _, _, _, [] => .ok ([], [])
  | 0, offset, _, _ => .error (.truncatedOperand offset)
  | fuel + 1, offset, index, bytes => do
    let (opcode, width, afterOpcode) ← readOpcode offset bytes
    let some kind := operandKind opcode | throw (.unknownOpcode offset opcode)
    let (operand, following, remaining) ←
      decodeOperand tokens offset (offset + width) opcode kind afterOpcode
    let (rest, statics) ← decodeInstructions tokens fuel following (index + 1) remaining
    let instruction : RawInstruction := { offset := offset, opcode := opcode, operand := operand }
    match boundStaticToken tokens offset operand afterOpcode with
    | some token => .ok (instruction :: rest, (index, token) :: statics)
    | none => .ok (instruction :: rest, statics)

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

/-- Look up the slot authorized for an external target by the method's links. -/
def callImportSlot (imports : Std.TreeMap String ImportSlot) (call : CallSite) : Option ImportSlot :=
  match call.target with
  | .external name => imports[name]?
  | .managed _ => none

/-- Index the slots for all imported calls in a body. -/
def BodyImports.byIdentity (imports : BodyImports) : Std.TreeMap String ImportSlot :=
  imports.calls.foldl (fun slots (_, entry) => slots.insert entry.identity entry) {}

/-- The checked table of a body: every entry is checked against the metadata, and no token has
    two entries. -/
private def checkTable (env : MetadataEnv) (frame : Frame)
    (imports : Std.TreeMap String ImportSlot) :
    List (Nat × RawOperand) → Std.TreeMap Nat (RawOperand × TokenFacts) →
      Except BodyError (Std.TreeMap Nat (RawOperand × TokenFacts))
  | [], table => .ok table
  | (token, operand) :: rest, table => do
    if table.contains token then throw (.duplicateToken token)
    let checked := match operand with
      | .call site => checkCallOperand env frame token site (callImportSlot imports site)
      | _ => checkEntryIn env frame token operand
    let facts <- checked.mapError BodyError.metadata
    checkTable env frame imports rest (table.insert token (operand, facts))

/-- Every call in an accepted token table passed the operand check in the same metadata frame. -/
private theorem checkTable_calls {env : MetadataEnv} {frame : Frame} {imports}
    {entries : List (Nat × RawOperand)} {start result : Std.TreeMap Nat (RawOperand × TokenFacts)}
    (checked : checkTable env frame imports entries start = .ok result)
    {token : Nat} {call : CallSite} (listed : (token, .call call) ∈ entries) :
    ∃ facts, checkCallOperand env frame token call (callImportSlot imports call) = .ok facts := by
  induction entries generalizing start with
  | nil => simp at listed
  | cons head rest induction =>
    obtain ⟨key, operand⟩ := head
    simp only [checkTable, bind, Except.bind] at checked
    split at checked
    · contradiction
    split at checked
    · contradiction
    rename_i facts accepted
    rcases List.mem_cons.mp listed with first | later
    · cases first
      cases bound : checkCallOperand env frame token call (callImportSlot imports call) with
      | error fault => simp [checkEntryIn, bound, Except.mapError] at accepted
      | ok value => exact ⟨value, rfl⟩
    · exact induction checked later

#print axioms checkTable_calls

/-- The metadata of a body as an environment of indexed slices, its own first, over the given
    identities and tables: independent of the number of rows. -/
def MethodMetadata.environmentWith (metadata : MethodMetadata) (identities : List (List Nat))
    (tables : List IndexTables) (pinned : PinnedIndex) (platform : PlatformTable) :
    Except MetadataError MetadataEnv :=
  if tables.length != metadata.others.length + 1 || identities.length != tables.length then
    .error .tablesMismatch
  else do
    let indexed ← (metadata.slices.zip (identities.zip tables)).mapM
      fun (slice, identity, sliceTables) => slice.indexWith sliceTables identity
    .ok (MetadataEnv.ofSlices indexed pinned.prefixes platform pinned.exact)

/-- The metadata of a body as an environment of indexed slices, built from its bytes alone. -/
def MethodMetadata.environment (metadata : MethodMetadata)
    (pinned : PinnedIndex := PinnedIndex.ofIdentities []) :
    Except MetadataError MetadataEnv := do
  .ok (MetadataEnv.ofSlices (← metadata.slices.mapM MetadataSlice.index)
    pinned.prefixes (exactPins := pinned.exact))

/-- Decode a method body: its header and its instructions, with branch operands as instruction
    indices and every token operand checked against the metadata. `arity` is the number of
    generic parameters of the method and `ownerArity` that of its owner. The supplied bytes
    must be exactly the header and the declared code. -/
def decodeBody (env : MetadataEnv) (arity ownerArity : Nat) (body : BodyEvidence) :
    Except BodyError DecodedBody := do
  if !body.bytes.all (· < 256) then throw .invalidByte
  let (header, code) ← decodeHeader body.bytes
  if code.length != header.codeSize then
    throw (.codeSizeMismatch header.codeSize code.length)
  let frame ← (env.frame arity ownerArity).mapError BodyError.metadata
  let imports := body.imports.byIdentity
  let tokens <- checkTable env frame imports body.tokens.operands {}
  let (raw, statics) ← decodeInstructions tokens code.length 0 0 code
  if !body.imports.calls.isEmpty && !body.imports.checkUses imports raw then
    throw (.metadata (.operandMismatch 0))
  let starts := indexStarts raw 0 false {}
  let instructions ← raw.mapM (resolveBranches starts code.length)
  .ok { maxStack := header.maxStack, initLocals := header.initLocals,
        localSignature := header.localSignature, code := instructions, statics := statics }

/-- The metadata environment and imported layouts used to check the body's own tokens. -/
def BodyEvidence.environment (body : BodyEvidence) : Except MetadataError MetadataEnv := do
  let env ← body.metadata.environmentWith body.identities body.tables body.pinned body.platform
  return { env with publishedLayouts := body.imports.layouts }

/-- The method's definition, its locals and its body, each checked against the metadata the
    body carries: the decoded body, when everything agrees with the method instantiated at
    `arguments`. -/
def checkBody (body : BodyEvidence) (method : RawMethod) (arguments : List TypeExpr) :
    Except BodyError DecodedBody := do
  let env ← body.environment.mapError BodyError.metadata
  let names ← (methodIdentityValid env method body.instantiation arguments).mapError
    BodyError.metadata
  if names != body.names then throw (.metadata (.methodMismatch method.token))
  -- `methodIdentityValid` has tied both arities to the `GenericParam` rows.
  let arity := method.genericParameters.length
  let ownerArity := method.ownerParameters.length
  let decoded ← decodeBody env arity ownerArity body
  (checkLocals env arity decoded.localSignature method.locals ownerArity).mapError
    BodyError.metadata
  .ok decoded

/-- Whether the body decodes to exactly the method's `maxStack`, `initLocals` and `code`, with
    the method's definition and locals agreeing with the metadata. Only the kernel decides it:
    the elaborator's default reduction evaluates a call by name and would unfold the decoder,
    the metadata slices and every token's resolution without sharing, so the definition is
    irreducible and `decide` fails at once; `decide +kernel` evaluates it. -/
@[irreducible] def bodyMatches (body : BodyEvidence) (method : RawMethod)
    (arguments : List TypeExpr) : Bool :=
  match checkBody body method arguments with
  | .ok decoded => decoded.maxStack == method.maxStack &&
      decoded.initLocals == method.initLocals && decoded.code == method.code &&
      decoded.statics == body.statics
  | .error _ => false

/-- The body's tables are what its metadata bytes give, and the method's definition, locals,
    `maxStack`, `initLocals` and `code` are what the body bytes and the metadata say, through the
    body's token table. Names are tied to bytes by equations, so no decision evaluates a string:
    each slice's assembly spells the identity the body lists, the method's own assembly is the
    pin, the pinned identities the body lists are those of the extraction's pins, its platform
    definitions are the extraction's `platform`, its imported calls and layouts are those of
    the verified links and slots, the owner and base class names the metadata
    resolves are the ones the method states, and `signature`, the string a proof selects the
    method by, is Cecil's full name of the method the row defines, instantiated at
    `arguments`. -/
abbrev BodyDecodes (pins : List AssemblyPin) (platform : PlatformTable) (pin : AssemblyPin)
    (body : BodyEvidence) (method : RawMethod) (arguments : List TypeExpr) (signature : String)
    (imports : BodyImports := {}) : Prop :=
  AssembliesIdentified body.metadata body.identities ∧
    tablesMatch body.metadata body.tables = true ∧
    body.metadata.own.assembly.identity = pin.identity ∧
    body.pinned.identities.mapM spelled? = some (pins.map (·.identity)) ∧
    (body.platform, body.imports) = (platform, imports) /\
    body.names.Spell method ∧ body.names.Selects signature ∧
    bodyMatches body method arguments = true

/-- Whether the instruction before `index` of `code` is a prefix; the first never is. -/
private def followsPrefix (code : List RawInstruction) : Nat → Bool
  | 0 => false
  | index + 1 => (code[index]?).any (isPrefixOpcode ·.opcode)

/-- Every entry of `starts` records whether its index follows a prefix in `code`. -/
private def StartsFollow (code : List RawInstruction)
    (starts : Std.TreeMap Nat (Nat × Bool)) : Prop :=
  ∀ (offset index : Nat) (after : Bool), starts[offset]? = some (index, after) →
    after = followsPrefix code index

/-- `indexStarts` records, for each instruction it indexes, whether a prefix precedes it. -/
private theorem indexStarts_follow (code : List RawInstruction) :
    ∀ (rest : List RawInstruction) (index : Nat) (after : Bool)
      (starts : Std.TreeMap Nat (Nat × Bool)),
      code.drop index = rest → after = followsPrefix code index → StartsFollow code starts →
      StartsFollow code (indexStarts rest index after starts)
  | [], _, _, _, _, _, follow => by simpa [indexStarts] using follow
  | instruction :: rest, index, after, starts, dropped, current, follow => by
    simp only [indexStarts]
    have fetched : code[index]? = some instruction := by
      rw [← List.head?_drop, dropped]; rfl
    apply indexStarts_follow code rest (index + 1)
    · rw [← List.tail_drop, dropped]; rfl
    · simp [followsPrefix, fetched]
    · unfold StartsFollow at follow ⊢
      intro offset found after' entry
      rw [Std.TreeMap.getElem?_insert] at entry
      split at entry
      · simp only [Option.some.injEq, Prod.mk.injEq] at entry
        obtain ⟨rfl, rfl⟩ := entry
        exact current
      · exact follow offset found after' entry

#print axioms indexStarts_follow

/-- A branch destination the body decoder resolves is an entry of `starts` that follows no
    prefix. -/
private theorem instructionIndex_unprefixed {starts : Std.TreeMap Nat (Nat × Bool)}
    {codeLength offset target index : Nat}
    (resolved : instructionIndex starts codeLength offset target = .ok index) :
    ∃ entry : Nat, starts[entry]? = some (index, false) := by
  unfold instructionIndex at resolved
  by_cases outside : codeLength ≤ target
  · simp [outside] at resolved
  · cases found : starts[target]? with
    | none => simp [outside, found] at resolved
    | some entry =>
      obtain ⟨foundIndex, after⟩ := entry
      cases after
      · simp only [outside, found, ite_false, Except.ok.injEq] at resolved
        exact ⟨target, resolved ▸ found⟩
      · simp [outside, found] at resolved

#print axioms instructionIndex_unprefixed

/-- A list an `Except`-valued function maps entirely holds at each index the image of the
    input there. -/
private theorem mapM_ok_at {α β ε : Type} {make : α → Except ε β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM make = .ok outputs →
      ∀ (index : Nat) (output : β), outputs[index]? = some output →
        ∃ input, inputs[index]? = some input ∧ make input = .ok output
  | [], outputs, made, index, output, found => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at made
    subst made
    simp at found
  | input :: rest, outputs, made, index, output, found => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at made
    cases first : make input with
    | error => simp [first] at made
    | ok head =>
      cases others : rest.mapM make with
      | error => simp [first, others] at made
      | ok tail =>
        simp only [first, others, Except.ok.injEq] at made
        subst made
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          exact ⟨input, rfl, found ▸ first⟩
        | succ index =>
          simpa using mapM_ok_at others index output (by simpa using found)

#print axioms mapM_ok_at

/-- An instruction the decoder resolves keeps its opcode, and each of its branch destinations is
    an entry of `starts` that follows no prefix. -/
private theorem resolveBranches_unprefixed {starts : Std.TreeMap Nat (Nat × Bool)}
    {codeLength : Nat} {instruction resolved : RawInstruction}
    (ok : resolveBranches starts codeLength instruction = .ok resolved) :
    resolved.opcode = instruction.opcode ∧ ∀ target, branchesTo target resolved = true →
      ∃ entry : Nat, starts[entry]? = some (target, false) := by
  unfold resolveBranches at ok
  split at ok
  · next destination operand =>
    cases index : instructionIndex starts codeLength instruction.offset destination with
    | error => simp [index, bind, Except.bind] at ok
    | ok found =>
      simp only [index, bind, Except.bind, Except.ok.injEq] at ok
      subst ok
      refine ⟨rfl, fun target branches => ?_⟩
      simp only [branchesTo, beq_iff_eq] at branches
      exact branches ▸ instructionIndex_unprefixed index
  · next destinations operand =>
    cases indices : destinations.mapM (instructionIndex starts codeLength instruction.offset) with
    | error => simp [indices, bind, Except.bind] at ok
    | ok found =>
      simp only [indices, bind, Except.bind, Except.ok.injEq] at ok
      subst ok
      refine ⟨rfl, fun target branches => ?_⟩
      simp only [branchesTo, List.contains_iff_mem] at branches
      obtain ⟨position, at_position⟩ := List.mem_iff_getElem?.mp branches
      obtain ⟨_, _, resolvedAt⟩ := mapM_ok_at indices position target at_position
      exact instructionIndex_unprefixed resolvedAt
  · next unbranched =>
    simp only [Except.ok.injEq] at ok
    subst ok
    refine ⟨rfl, fun target branches => ?_⟩
    simp only [branchesTo] at branches
    simp at branches

#print axioms resolveBranches_unprefixed

/-- Instructions whose branch destinations the decoder resolved against their own starts
    have no branch into the instruction after a prefix. -/
private theorem resolved_prefixEntryFree {raw instructions : List RawInstruction}
    {codeLength : Nat}
    (ok : raw.mapM (resolveBranches (indexStarts raw 0 false ∅) codeLength) = .ok instructions) :
    PrefixEntryFree instructions := by
  have follow : StartsFollow raw (indexStarts raw 0 false ∅) :=
    indexStarts_follow raw raw 0 false ∅ List.drop_zero rfl (by
      unfold StartsFollow
      intro offset index after found
      simp at found)
  intro pc instruction fetched isPrefix
  rw [List.any_eq_false]
  intro other member branches
  obtain ⟨position, otherAt⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨_, _, resolvedOther⟩ := mapM_ok_at ok position other otherAt
  obtain ⟨entry, found⟩ := (resolveBranches_unprefixed resolvedOther).2 (pc + 1) branches
  have unprefixed := follow entry (pc + 1) false found
  obtain ⟨original, originalAt, resolvedHere⟩ := mapM_ok_at ok pc instruction fetched
  have sameOpcode := (resolveBranches_unprefixed resolvedHere).1
  simp [followsPrefix, originalAt, ← sameOpcode, isPrefix] at unprefixed

#print axioms resolved_prefixEntryFree

/-- No branch of a decoded body, reachable or not, enters the instruction after a prefix. -/
theorem decodeBody_prefixEntryFree {env : MetadataEnv} {arity ownerArity : Nat}
    {body : BodyEvidence} {decoded : DecodedBody}
    (ok : decodeBody env arity ownerArity body = .ok decoded) : PrefixEntryFree decoded.code := by
  unfold decodeBody at ok
  simp only [bind, Except.bind] at ok
  repeat' split at ok
  all_goals first
    | (simp only [Except.ok.injEq] at ok; subst ok; exact resolved_prefixEntryFree ‹_›)
    | simp_all

#print axioms decodeBody_prefixEntryFree

/-- No branch of a body the check accepts enters the instruction after a prefix. -/
theorem checkBody_prefixEntryFree {body : BodyEvidence} {method : RawMethod}
    {arguments : List TypeExpr} {decoded : DecodedBody}
    (ok : checkBody body method arguments = .ok decoded) : PrefixEntryFree decoded.code := by
  unfold checkBody at ok
  simp only [bind, Except.bind] at ok
  repeat' split at ok
  all_goals first
    | (simp only [Except.ok.injEq] at ok; subst ok; exact decodeBody_prefixEntryFree ‹_›)
    | simp_all

#print axioms checkBody_prefixEntryFree

/-- A successful decode used one frame to check every operand in its table. -/
private theorem decodeBody_checkedTable {env : MetadataEnv} {arity ownerArity : Nat}
    {body : BodyEvidence} {decoded : DecodedBody} (ok : decodeBody env arity ownerArity body =
      .ok decoded) :
    ∃ frame table, env.frame arity ownerArity = .ok frame ∧
      checkTable env frame body.imports.byIdentity body.tokens.operands ∅ = .ok table := by
  unfold decodeBody at ok
  simp only [bind, Except.bind] at ok
  repeat' split at ok
  all_goals first
    | contradiction
    | (refine ⟨_, _, ?_, by assumption⟩
       cases frameEq : env.frame arity ownerArity <;>
         simp_all [Except.mapError])

#print axioms decodeBody_checkedTable

/-- A bound body validates every call reference listed in its token table in its own type frame. -/
private theorem BodyDecodes.checkedCall {pins platform pin body method arguments signature imports}
    (decodes : BodyDecodes pins platform pin body method arguments signature imports) {token : Nat} {call : CallSite}
    (listed : (token, RawOperand.call call) ∈ body.tokens.operands) :
    ∃ env frame facts,
      body.environment = .ok env ∧
      env.frame method.genericParameters.length method.ownerParameters.length = .ok frame ∧
      checkCallOperand env frame token call (callImportSlot body.imports.byIdentity call) = .ok facts := by
  have matched := decodes.2.2.2.2.2.2.2
  unfold bodyMatches at matched
  split at matched
  · rename_i checked
    unfold checkBody at checked
    simp only [bind, Except.bind] at checked
    repeat' split at checked
    all_goals first
      | contradiction
      | (obtain ⟨frame, table, frameEq, tableEq⟩ := decodeBody_checkedTable
           (show decodeBody _ _ _ body = .ok _ from by assumption)
         obtain ⟨facts, accepted⟩ := checkTable_calls tableEq listed
         refine ⟨_, frame, facts, ?_, frameEq, accepted⟩
         cases envEq : body.environment <;>
           simp_all [Except.mapError])
  · contradiction

#print axioms BodyDecodes.checkedCall

/-- A bound body checks each token's call reference and external identity against one member. -/
theorem BodyDecodes.externalTarget {pins : List AssemblyPin} {pin : AssemblyPin}
    {platform : PlatformTable} {imports : BodyImports}
    {body : BodyEvidence} {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    (decodes : BodyDecodes pins platform pin body method arguments signature imports) {token : Nat}
    {call : CallSite} {identity : String} (listed : (token, .call call) ∈ body.tokens.operands)
    (externalTarget : call.target = .external identity) :
    ∃ env frame site,
      body.environment = .ok env ∧
      env.frame method.genericParameters.length method.ownerParameters.length = .ok frame ∧
      resolveCallMember env frame token call (callImportSlot body.imports.byIdentity call) = .ok site ∧
      checkCallReference env frame token site call = .ok () ∧ site.definition = none ∧ (site.externalName = some (bytesOf identity) ∨
        site.contractName frame = some (bytesOf identity)) := by
  obtain ⟨env, frame, _, built, localFrame, checked⟩ := decodes.checkedCall listed
  obtain ⟨site, target⟩ := checkCallOperand_external checked externalTarget
  exact ⟨env, frame, site, built, localFrame, target⟩

#print axioms BodyDecodes.externalTarget

/-- The checked table contains only supplied token operands or operands already in its input. -/
private theorem checkTable_origin {env : MetadataEnv} {frame : Frame} {imports}
    {entries : List (Nat × RawOperand)} {start result : Std.TreeMap Nat (RawOperand × TokenFacts)}
    (checked : checkTable env frame imports entries start = .ok result) {key operand facts}
    (found : result[key]? = some (operand, facts)) :
    (key, operand) ∈ entries ∨ start[key]? = some (operand, facts) := by
  induction entries generalizing start with
  | nil => cases checked; exact Or.inr found
  | cons head rest ih =>
    obtain ⟨token, value⟩ := head
    simp only [checkTable, bind, Except.bind] at checked
    split at checked <;> try contradiction
    split at checked <;> try contradiction
    rcases ih checked with later | earlier
    · exact Or.inl (List.mem_cons_of_mem _ later)
    · rw [Std.TreeMap.getElem?_insert] at earlier
      split at earlier
      · rename_i same
        obtain rfl := Nat.compare_eq_eq.mp same
        cases earlier
        exact Or.inl List.mem_cons_self
      · exact Or.inr earlier

#print axioms checkTable_origin

/-- A call operand can only come from a token lookup in the instruction bytes. -/
private theorem decodeOperand_call {table offset start opcode kind bytes value call}
    (ok : decodeOperand table offset start opcode kind bytes = .ok value)
    (called : value.1 = RawOperand.call call) :
    ∃ (token : Nat) (facts : TokenFacts), table[token]? = some (RawOperand.call call, facts) := by
  obtain ⟨operand, following, remaining⟩ := value
  cases called
  cases kind <;> simp only [decodeOperand, readToken, readValue, readBranch, readSwitch,
    bind, Except.bind] at ok
  all_goals repeat' split at ok
  all_goals first
    | contradiction
    | (solve | simp at ok)
    | (have same := congrArg Prod.fst (Except.ok.inj ok)
       simp only at same
       subst_vars
       exact ⟨_, _, by assumption⟩)

#print axioms decodeOperand_call

/-- Each call in a decoded instruction stream belongs to the operand table. -/
private theorem decodeInstructions_call {table fuel offset index bytes code statics}
    (ok : decodeInstructions table fuel offset index bytes = .ok (code, statics))
    {instruction : RawInstruction} (member : instruction ∈ code) {call}
    (called : instruction.operand = .call call) :
    ∃ (token : Nat) (facts : TokenFacts), table[token]? = some (RawOperand.call call, facts) := by
  induction fuel generalizing offset index bytes code statics with
  | zero =>
    cases bytes <;> simp only [decodeInstructions] at ok <;> cases ok
    simp at member
  | succ fuel ih =>
    cases bytes with
    | nil => cases ok; simp at member
    | cons byte bytes =>
      simp only [decodeInstructions, bind, Except.bind] at ok
      repeat' split at ok
      all_goals first
        | contradiction
        | (cases ok
           rcases List.mem_cons.mp member with rfl | later
           · simp only at called
             exact decodeOperand_call (by assumption) called
           · exact ih (by assumption) later)

#print axioms decodeInstructions_call

/-- Resolving a branch can never introduce or change a call operand. -/
private theorem resolveBranches_call {starts size raw instruction call}
    (ok : resolveBranches starts size raw = .ok instruction)
    (called : instruction.operand = .call call) : raw.operand = .call call := by
  unfold resolveBranches at ok
  simp only [bind, Except.bind] at ok
  repeat' split at ok
  all_goals first | contradiction | (cases ok; exact called) | (cases ok; cases called)

#print axioms resolveBranches_call

/-- The bytes of a decoded call selected an operand supplied at a token of this body. -/
private theorem decodeBody_call {env arity ownerArity body decoded}
    (ok : decodeBody env arity ownerArity body = .ok decoded)
    {pc : Nat} {instruction : RawInstruction} {call : CallSite}
    (fetched : decoded.code[pc]? = some instruction) (called : instruction.operand = .call call) :
    ∃ token, (token, RawOperand.call call) ∈ body.tokens.operands := by
  unfold decodeBody at ok
  simp only [bind, Except.bind] at ok
  repeat' split at ok
  all_goals first
    | contradiction
    | (cases ok
       obtain ⟨raw, rawAt, resolved⟩ := mapM_ok_at (by assumption) pc instruction fetched
       obtain ⟨token, facts, found⟩ := decodeInstructions_call (by assumption)
         (List.mem_of_getElem? rawAt) (resolveBranches_call resolved called)
       rcases checkTable_origin (by assumption) found with member | empty
       · exact ⟨token, member⟩
       · simp at empty)

#print axioms decodeBody_call

/-- Each call instruction of the decoded method reads an operand from this body's token table. -/
private theorem BodyDecodes.callOperand {pins platform pin body method arguments signature imports}
    (decodes : BodyDecodes pins platform pin body method arguments signature imports)
    {pc : Nat} {instruction : RawInstruction} {call : CallSite}
    (fetched : method.code[pc]? = some instruction) (called : instruction.operand = .call call) :
    ∃ token, (token, RawOperand.call call) ∈ body.tokens.operands := by
  have matched := decodes.2.2.2.2.2.2.2
  unfold bodyMatches at matched
  split at matched
  · rename_i decoded checked
    simp only [Bool.and_eq_true, beq_iff_eq] at matched
    rw [← matched.1.2] at fetched
    unfold checkBody at checked
    simp only [bind, Except.bind] at checked
    repeat' split at checked
    all_goals first
      | contradiction
      | (cases checked
         exact decodeBody_call (by assumption) fetched called)
  · contradiction

#print axioms BodyDecodes.callOperand

/-- Every decoded external call names the metadata member of its own reference. -/
theorem BodyDecodes.callExternalTarget {pins platform pin body method arguments signature imports}
    (decodes : BodyDecodes pins platform pin body method arguments signature imports)
    {pc : Nat} {instruction : RawInstruction} {call : CallSite} {identity : String}
    (fetched : method.code[pc]? = some instruction) (called : instruction.operand = .call call)
    (externalTarget : call.target = .external identity) :
    ∃ token env frame site,
      (token, RawOperand.call call) ∈ body.tokens.operands ∧
      body.environment = .ok env ∧
      env.frame method.genericParameters.length method.ownerParameters.length = .ok frame ∧
      resolveCallMember env frame token call (callImportSlot body.imports.byIdentity call) = .ok site ∧
      checkCallReference env frame token site call = .ok () ∧ site.definition = none ∧ (site.externalName = some (bytesOf identity) ∨
        site.contractName frame = some (bytesOf identity)) := by
  obtain ⟨token, listed⟩ := decodes.callOperand fetched called
  obtain ⟨env, frame, site, resolved⟩ := decodes.externalTarget listed externalTarget
  exact ⟨token, env, frame, site, listed, resolved⟩

#print axioms BodyDecodes.callExternalTarget

/-- Each managed call in the decoded body resolves its operand to a MethodDef in a particular
    metadata slice. A MemberRef in the caller may have a different token from that definition. -/
theorem BodyDecodes.callManagedTarget {pins platform pin body method arguments signature imports}
    (decodes : BodyDecodes pins platform pin body method arguments signature imports)
    {pc target : Nat} {instruction : RawInstruction} {call : CallSite}
    (fetched : method.code[pc]? = some instruction) (called : instruction.operand = .call call)
    (managed : call.target = .managed target) :
    ∃ token env frame site position,
      (token, RawOperand.call call) ∈ body.tokens.operands ∧
      body.environment = .ok env ∧
      env.frame method.genericParameters.length method.ownerParameters.length = .ok frame ∧
      env.methodSite token = .ok site ∧ checkCallReference env frame token site call = .ok () ∧
      site.definition = some (position, target) := by
  obtain ⟨token, listed⟩ := decodes.callOperand fetched called
  obtain ⟨env, frame, _, built, localFrame, checked⟩ := decodes.checkedCall listed
  simp only [callImportSlot, managed] at checked
  obtain ⟨site, position, resolved⟩ := checkCallOperand_managed checked managed
  exact ⟨token, env, frame, site, position, listed, built, localFrame, resolved⟩

#print axioms BodyDecodes.callManagedTarget

end CIL.Extraction
