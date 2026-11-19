import CIL.Extraction.Features
import CIL.Extraction.UnsafeReferences
import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.SpanCalls
import CIL.Extraction.ViewObservations
import CIL.Extraction.GuardCalls
import CIL.Extraction.Prefixes
import CIL.Resolution

/-!
# Scalar flow

CIL arithmetic opcodes are untyped: `add` adds two `int32`s, two `int64`s or a native int
and an `int32`. The emitted instruction set is explicit about width, so extraction must
pick the right encoding from the operand types. `ScalarFlowValid` checks those choices: it
tracks the kind of every stack slot at every reachable pc (taken from the feature
certificate), recomputes each transfer from raw metadata and signatures, and requires each
covered arithmetic, conversion, constant and compare-branch opcode to emit exactly the
encoding its operand kinds imply.

External call signatures are compared byte by byte; byte literals below are ASCII.
-/

namespace CIL.Extraction

/-- The evaluation-stack kind of a value, as far as scalar encodings care. -/
inductive ScalarKind where
  | word32 | word64 | native | reference | nullObject | other
  /-- A class instance reference of an admitted object type. -/
  | object
  /-- A class reference loaded from a field of an `opaqueFieldType`, of a class the model does
      not name: only a store into such a field, a type test or a null test takes it. -/
  | opaque
  | array (element : ArrayElement)
  | enumSpan (element : ArrayElement) (writable : Bool) (reference : Bool)
  | methodPointer (signature : ManagedSignature)
  | methodTable (signature : ManagedSignature)
  | nativeMethodTable (signature : ManagedSignature)
  deriving DecidableEq, Repr

/-- The claimed stack kinds (top first) at each raw pc; `none` where the pc is unreachable. -/
abbrev ScalarCertificate := List (Option (List ScalarKind))

/-- Small integers widen to `word32`. Enums take the stack kind of their immediate integer
    atom, and a malformed enum has kind `other`. -/
def scalarType : TypeExpr → ScalarKind
  | .enum _ underlying => match enumUnderlyingField underlying with
    | some .signed64 | some .unsigned64 => .word64
    | some _ => .word32
    | none => .other
  | .pointer .void => .other
  | .byref element => match scalarType element with
      | .enumSpan identity writable _ => .enumSpan identity writable true
      | _ => .reference
  | .pointer _ => .reference
  | .array (.object ..) => .object
  | .array element => match managedSignature element with
    | some signature => .methodTable signature
    | none => (arrayElementType element).map ScalarKind.array |>.getD .other
  | type@(.functionPointer ..) => (managedSignature type).map ScalarKind.methodPointer |>.getD .other
  | .object .. => .object
  | type@(.apply _ element@(.enum ..)) =>
    match spanStorage type, arrayElementType element with
    | some (.span _ writable), some identity => .enumSpan identity writable false
    | _, _ => .other
  | .atom scope name =>
    if scope != runtimeScope then .other
    else if name ∈ ["System.IntPtr", "System.UIntPtr"] then .native
    else if name ∈ ["System.Int64", "System.UInt64"] then .word64
    else if name ∈ ["System.Boolean", "System.Char", "System.SByte", "System.Byte", "System.Int16",
      "System.UInt16", "System.Int32", "System.UInt32"] then .word32 else .other
  | _ => .other

/-- The stack kind of the receiver of an instance method declared by `owner`: an object
    reference for a class or `System.Object`, a byref for a value type. -/
def receiverKind (owner : TypeExpr) : ScalarKind :=
  match owner with
  | .object .. => .object
  | _ => if owner == .atom runtimeScope "System.Object" then .object
    else scalarType (.byref owner)

private def numeric (kind : ScalarKind) : Bool := kind ∈ [.word32, .word64, .native]

/-- A value of kind `value` may be stored in a slot of kind `home`; `word64` and `native`
    share one representation on the admitted 64-bit targets. -/
private def storageCompatible (value home : ScalarKind) : Bool :=
  value == home || (value == .nullObject &&
    (match home with | .array _ | .methodTable _ | .object => true | _ => false)) ||
    value ∈ [.word64, .native] && home ∈ [.word64, .native]

/-- Two-operand arithmetic: `add` through `xor`, the overflow-checked forms, and `ceq`
    through `clt.un`. Shifts are handled separately. -/
private def scalarBinary : Nat → Bool
  | 88 | 89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 214 | 215 | 216 | 217 | 218 | 219
  | 65025 | 65026 | 65027 | 65028 | 65029 => true
  | _ => false

/-- `ceq`, `cgt`, `cgt.un`, `clt` and `clt.un`, which push an `int32`. -/
private def comparison (opcode : Nat) : Bool := 65025 <= opcode && opcode <= 65029

/-- Integer conversions, plain and overflow-checked; floating-point conversions are not covered. -/
private def conversion : Nat → Bool
  | 103 | 104 | 105 | 106 | 109 | 110 | 130 | 131 | 132 | 133 | 134 | 135 | 136 | 137 | 138 | 139
  | 179 | 180 | 181 | 182 | 183 | 184 | 185 | 186 | 209 | 210 | 211 | 212 | 213 | 224 => true
  | _ => false

/-- Two-operand conditional branches, short and long forms (`beq` through `blt.un`). -/
private def compareBranch (opcode : Nat) : Bool :=
  (46 <= opcode && opcode <= 55) || (59 <= opcode && opcode <= 68)

/-- `bne.un` and the unsigned orderings; CoreCLR widens a mixed int32 operand by provenance. -/
private def unsignedBranch (opcode : Nat) : Bool :=
  (51 <= opcode && opcode <= 55) || (64 <= opcode && opcode <= 68)

/-- Raw array opcodes in the supported integer, element-address and class reference subset. -/
private def arrayCovered (opcode : Nat) : Bool :=
  (142 ≤ opcode && opcode ≤ 151) ||
    (155 ≤ opcode && opcode ≤ 159) || opcode ∈ [154, 162, 163, 164]

/-- Null is a permitted array operand, but arbitrary opaque/reference values are not. -/
private def arrayOperand : ScalarKind → Option (Option ArrayElement)
  | .array element => some (some element)
  | .nullObject => some none
  | _ => none

/-- The stack after `ldlen`, `ldelem.ref` and `stelem.ref` on an array of class references, which
    is an object; a null array reaches the same operations, which throw for it. -/
private def referenceArrayStep (instruction : RawInstruction) (stack : List ScalarKind) :
    Option (List ScalarKind) :=
  if instruction.operand != .none then none else
  match instruction.opcode, stack with
  | 142, .object :: tail => some (.native :: tail)
  | 154, index :: array :: tail =>
    if index ∈ [.word32, .native] && array ∈ [.object, .nullObject] then some (.object :: tail)
    else none
  | 162, value :: index :: array :: tail =>
    if value ∈ [.object, .nullObject] && index ∈ [.word32, .native] &&
        array ∈ [.object, .nullObject] then some tail
    else none
  | _, _ => none

/-- Exact array stack transition, including primitive tokens and element types. -/
private def arrayStep (instruction : RawInstruction) (stack : List ScalarKind) :
    Option (List ScalarKind) := do
  if let some after := referenceArrayStep instruction stack then return after
  let opcode := instruction.opcode
  if opcode == 142 then
    let array :: tail := stack | none
    let _ ← arrayOperand array
    if instruction.operand == .none then return .native :: tail else none
  let store := (155 ≤ opcode && opcode ≤ 159) || opcode == 164
  let (value, input) := if store then (stack.head?, stack.drop 1) else (none, stack)
  let index :: array :: tail := input | none
  if index ∉ [.word32, .native] then none else pure ()
  let element ← arrayOperand array
  if opcode == 143 then
    let .type token := instruction.operand | none
    let expected ← arrayElementType token
    if element.isSome && element != some expected then none else
      return .reference :: tail
  if opcode ∈ [163, 164] then
    let .type token := instruction.operand | none
    let expected ← arrayElementType token
    if element.isSome && element != some expected then none else pure ()
    if expected.composite then
      if store then
        if value == some .other then return tail else none
      else return .other :: tail
  let (width, native) : Nat × Bool ←
    if opcode ∈ [163, 164] then do
      let .type token := instruction.operand | none
      let expected ← arrayElementType token
      if element.isSome && element != some expected then none else
        pure (expected.width, expected.native)
    else do
      if instruction.operand != .none then none else pure ()
      let (width, native) ← match opcode with
        | 144 | 145 | 156 => some (1, false) | 146 | 147 | 157 => some (2, false)
        | 148 | 149 | 158 => some (4, false) | 150 | 159 => some (8, false)
        | 151 | 155 => some (8, true)
        | _ => none
      if let some actual := element then
        if actual.composite then none else pure ()
        if actual.width != width || actual.native != native then none else pure ()
      pure (width, native)
  let kind := if native then ScalarKind.native else if width == 8 then .word64 else .word32
  if store then
    if value == some kind then return tail else none
  else return kind :: tail

/-- Array operations cannot be introduced through an unrelated stack-effect-only encoding. -/
private def arrayEmission : Instruction → Bool
  | .newarr _ => true
  | .ldlen | .ldelem _ | .ldelem_ref | .stelem _ | .stelem_ref | .ldelem_any _ | .stelem_any _
  | .ldelema .. => true
  | _ => false

/-- The emitted array operation agrees exactly with its independently decoded raw opcode: a
    decoded opcode emits its decoding after `previous`, the raw instruction before it, and a
    typed one the operation its element gives. -/
private def arrayMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction) (skipEncoding : Bool) : Bool :=
  if instruction.opcode == 141 then
    match instruction.operand, stack, emitted with
    | .type token, length :: _, .newarr element => length ∈ [.word32, .native] && token == element
    | _, _, _ => false
  else
    Instruction.valueOpcode instruction.opcode &&
      (skipEncoding || valueEncodingMatches previous instruction emitted)
/-- Opcodes whose emitted encoding the scalar check fixes: integer constants, arithmetic,
    shifts, `neg`, `not`, conversions and compare-branches. -/
def scalarCovered (opcode : Nat) : Bool :=
  opcode == 141 || arrayCovered opcode || (21 <= opcode && opcode <= 33) ||
    scalarBinary opcode || conversion opcode ||
    compareBranch opcode || opcode ∈ [20, 44, 45, 57, 58, 98, 99, 100, 101, 102]

/-- The emitted operation each covered non-branch opcode must produce. -/
private def scalarEncodingMatches (opcode : Nat) (emitted : Instruction) : Bool :=
  match opcode, emitted with
  -- Arithmetic, division and remainder.
  | 88, .add | 89, .sub | 90, .mul => true
  | 91, .div | 92, .div_un | 93, .rem | 94, .rem_un => true
  -- Bitwise, shifts, `neg` and `not`.
  | 95, .and | 96, .or | 97, .xor | 98, .shl | 99, .shr | 100, .shr_un
  | 101, .neg | 102, .not => true
  -- Conversions, wrapping and overflow-checked.
  | 103, .conv_i1 | 104, .conv_i2 | 105, .conv_i4 | 106, .conv_i8 | 109, .conv_u4
  | 110, .conv_u8 => true
  | 130, .conv_ovf_un .i1 | 131, .conv_ovf_un .i2 | 132, .conv_ovf_un .i4
  | 133, .conv_ovf_un .i8 | 134, .conv_ovf_un .u1 | 135, .conv_ovf_un .u2
  | 136, .conv_ovf_un .u4 | 137, .conv_ovf_un .u8 | 138, .conv_ovf_un .i
  | 139, .conv_ovf_un .u => true
  | 179, .conv_ovf .i1 | 180, .conv_ovf .u1 | 181, .conv_ovf .i2 | 182, .conv_ovf .u2
  | 183, .conv_ovf .i4 | 184, .conv_ovf .u4 | 185, .conv_ovf .i8 | 186, .conv_ovf .u8 => true
  | 209, .conv_u2 | 210, .conv_u1 | 211, .conv_i | 224, .conv_u => true
  | 212, .conv_ovf .i | 213, .conv_ovf .u => true
  -- Overflow-checked arithmetic and comparisons.
  | 214, .add_ovf | 215, .add_ovf_un | 216, .mul_ovf | 217, .mul_ovf_un
  | 218, .sub_ovf | 219, .sub_ovf_un => true
  | 65025, .ceq | 65026, .cgt | 65027, .cgt_un | 65028, .clt | 65029, .clt_un => true
  | _, _ => false

/-- The emitted branch each compare-branch opcode must produce, keeping its target. -/
private def branchEncodingMatches (opcode target : Nat) (emitted : Instruction) : Bool :=
  (comparisonBranchIndex opcode).any fun index => match index, emitted with
  | 0, .beq actual | 1, .bge actual | 2, .bgt actual | 3, .ble actual | 4, .blt actual
  | 5, .bne_un actual | 6, .bge_un actual | 7, .bgt_un actual | 8, .ble_un actual
  | 9, .blt_un actual => actual == target
  | _, _ => false

/-- One operand is a native int and the other an `int32`. -/
private def mixedNative (left right : ScalarKind) : Bool :=
  (left == .native && right == .word32) || (left == .word32 && right == .native)

/-- Operand kinds a two-operand opcode accepts: equal numeric kinds, or native with `int32`. -/
private def compatibleBinary (left right : ScalarKind) : Bool :=
  numeric left && numeric right && (left == right || mixedNative left right)

/-- Object references and null support equality, and `cgt.un` against null tests presence;
    only managed references support unsigned ordering. -/
private def referenceComparison (opcode : Nat) (left right : ScalarKind) : Bool :=
  (left == right &&
    ((opcode ∈ [46, 51, 59, 64, 65025] && left ∈ [.reference, .nullObject]) ||
      (opcode ∈ [52, 53, 54, 55, 65, 66, 67, 68, 65027, 65029] && left == .reference))) ||
    (opcode ∈ [46, 51, 59, 64, 65025] && left ∈ [.object, .nullObject] &&
      right ∈ [.object, .nullObject]) ||
    (opcode == 65027 && left == .object && right == .nullObject)

/-- The constant an `ldc` instruction must emit; an out-of-range operand has none. -/
private def literal (instruction : RawInstruction) : Option Instruction :=
  match instruction.opcode, instruction.operand with
  | 21, .none => some (.ldc_i4 (BitVec.ofInt 32 (-1)))
  | 31, .integer value =>
    if -128 <= value && value < 128 then some (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 32, .integer value =>
    if -(2^31) <= value && value < 2^31 then some (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 33, .integer value =>
    if -(2^63) <= value && value < 2^63 then some (.ldc_i8 (BitVec.ofInt 64 value)) else none
  | opcode, .none =>
    if 22 <= opcode && opcode <= 30 then some (.ldc_i4 (BitVec.ofNat 32 (opcode - 22))) else none
  | _, _ => none

/-- Pointer addition admits an int32 or native byte offset on either side of the reference. -/
private def referenceAddition : ScalarKind → ScalarKind → Bool
  | .reference, offset | offset, .reference => offset ∈ [.word32, .native]
  | _, _ => false

/-- A covered opcode after `previous`, the raw instruction before it, emits exactly the
    encoding its operand kinds imply. -/
def scalarOpMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction) (skipEncoding := false) : Bool :=
  if instruction.opcode == 141 || arrayCovered instruction.opcode || arrayEmission emitted then
    arrayMatches previous instruction stack emitted skipEncoding
  else if instruction.opcode == 20 then
    instruction.operand == .none && match emitted with | .ldnull => true | _ => false
  else if instruction.opcode ∈ [44, 45, 57, 58] then
    match instruction.operand, stack, emitted with
    | .target target, value :: _, .brfalse actual =>
      instruction.opcode ∈ [44, 57] && target == actual &&
        (numeric value || value ∈ [.reference, .nullObject, .object])
    | .target target, value :: _, .brtrue actual =>
      instruction.opcode ∈ [45, 58] && target == actual &&
        (numeric value || value ∈ [.reference, .nullObject, .object])
    | _, _, _ => false
  else if 21 <= instruction.opcode && instruction.opcode <= 33 then
    match literal instruction, emitted with
    | some (.ldc_i4 expected), .ldc_i4 actual => expected == actual
    | some (.ldc_i8 expected), .ldc_i8 actual => expected == actual
    | _, _ => false
  else if compareBranch instruction.opcode then match instruction.operand, stack with
    | .target target, right :: left :: _ =>
        (compatibleBinary left right || referenceComparison instruction.opcode left right) &&
        !(mixedNative left right && unsignedBranch instruction.opcode) &&
        branchEncodingMatches instruction.opcode target emitted
    | _, _ => false
  else if instruction.operand != .none then false
  else if instruction.opcode == 88 &&
      (stack[0]? == some .reference || stack[1]? == some .reference) then
    match stack, emitted with
    | right :: left :: _, .add => referenceAddition left right
    | _, _ => false
  else if instruction.opcode == 89 && (stack.drop 1).head? == some .reference then
    match stack.head?, emitted with
    | some kind, .sub => kind ∈ [.word32, .native, .reference]
    | _, _ => false
  else if scalarBinary instruction.opcode then match stack with
    | right :: left :: _ =>
        (compatibleBinary left right || referenceComparison instruction.opcode left right) &&
        scalarEncodingMatches instruction.opcode emitted
    | _ => false
  else if instruction.opcode ∈ [98, 99, 100] then match stack with
    | right :: left :: _ =>
      numeric left && right ∈ [.word32, .native] &&
        scalarEncodingMatches instruction.opcode emitted
    | _ => false
  else match stack with
    | value :: _ => numeric value && scalarEncodingMatches instruction.opcode emitted
    | _ => false

/-- Operations computing a scalar from operands or a literal; only a covered encoding may
    emit one. -/
private def scalarEmission : Instruction → Bool
  | .ldc_i4 _ | .ldc_i8 _ | .add | .sub | .mul | .and | .or | .xor | .shl
  | .shr | .shr_un | .neg | .not | .ceq | .clt | .clt_un | .cgt | .cgt_un | .conv_i1
  | .conv_i2 | .conv_i4 | .conv_i8 | .conv_u1 | .conv_u2 | .conv_u4 | .conv_u8 | .conv_u
  | .conv_i | .conv_ovf _ | .conv_ovf_un _
  | .div | .div_un | .rem | .rem_un | .add_ovf | .add_ovf_un | .sub_ovf | .sub_ovf_un
  | .mul_ovf | .mul_ovf_un
  | .beq _ | .bge _ | .bgt _ | .ble _ | .blt _ | .bne_un _ | .bge_un _ | .bgt_un _
  | .ble_un _ | .blt_un _ => true
  | _ => false

/-- Byte width of a non-aggregate `sizeof` operand on the admitted 64-bit target. -/
private def primitiveSize (type : TypeExpr) : Option Nat :=
  match typeStorage [] type with
  | some (.field kind) => primitiveFieldWidth kind
  | some .vector128 => some 16
  | some .vector256 => some 32
  | some .vector512 => some 64
  | _ => none

/-- A `sizeof` constant has its primitive width; an aggregate size is bound by its layout use
    instead. `Unsafe.SizeOf` keeps its call, whose model reads the size from the layouts. -/
private def sizeConstant (instruction : RawInstruction) (bits : W32) : Bool :=
  match instruction.opcode, instruction.operand with
  | 65052, .type (.aggregate ..) => true
  | 65052, .type type => primitiveSize type == some bits.toNat
  | _, _ => false

/-- An instance field instruction, or an emitted field instruction. -/
private def instanceFieldSite (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  (instruction.opcode ∈ [123, 124, 125] && match instruction.operand with
    | .field _ _ _ _ false => true
    | _ => false) ||
  match emitted with
  | .ldfld _ | .ldflda _ | .stfld _ => true
  | _ => false

/-- Whether the raw operand names an instance field of a class or a generic class instance. -/
private def classOwned (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .field owner _ _ _ false => owner matches .object .. || owner.objectApplication
  | _ => false

/-- The kinds a class instance field holding references stores: an opaque reference or null in
    a generic class instance, also an object in `System.Object`, an object or null otherwise. -/
private def storedReferences (type : TypeExpr) : List ScalarKind :=
  if type.objectApplication then [.opaque, .nullObject]
  else if opaqueFieldType type then [.opaque, .object, .nullObject]
  else [.object, .nullObject]

/-- `ldfld`, `ldflda` and `stfld` of a class instance field emit the instruction the raw one
    decodes to after `previous`, naming the field its operand names, on an object or null
    receiver. A stored class or class array must be an object or null, a stored value array one
    of the field's element, and a stored integer of the field's stack kind (`word32` up to 4
    bytes, `word64` or `native` for 8), so `classFieldStore` never meets a word of the other
    width; the step resolves the slot and faults on a field type without one. -/
private def classFieldMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction) (skipEncoding : Bool) : Bool :=
  (skipEncoding || valueEncodingMatches previous instruction emitted) && match emitted, stack with
  | .ldfld _, receiver :: _ | .ldflda _, receiver :: _ => receiver ∈ [.object, .nullObject]
  | .stfld field, value :: receiver :: _ =>
    receiver ∈ [.object, .nullObject] &&
      (!referenceFieldType field.type || value ∈ storedReferences field.type) &&
      (valueArrayFieldElement field.type).all (fun declared => value == .array declared) &&
      ((objectFieldShape field.type).isNone || storageCompatible value (scalarType field.type))
  | _, _ => false

/-- `ldfld`, `ldflda` and `stfld` of a struct instance field emit the instruction the raw one
    decodes to after `previous`, naming the field its operand names. A load reads through a
    reference or from a struct value, an address and a store go through a reference, and a stored
    value has the field's stack kind; the step takes the offset and width from the layouts. -/
private def structFieldMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction) (skipEncoding : Bool) : Bool :=
  (skipEncoding || valueEncodingMatches previous instruction emitted) && match emitted, stack with
  | .ldfld _, receiver :: _ => receiver ∈ [.reference, .other]
  | .ldflda _, receiver :: _ => receiver == .reference
  | .stfld field, value :: receiver :: _ =>
    receiver == .reference && storageCompatible value (scalarType field.type)
  | _, _ => false

/-- Only `ldstr` loads a literal, and only its own text; inside a folded throw it emits nothing. -/
private def stringLiteralMatches (role : Option FoldRole) (instruction : RawInstruction)
    (emitted : Instruction) : Bool :=
  match instruction.opcode, instruction.operand, emitted with
  | 114, .text _, .nop => role ∈ [some .head, some .interior]
  | 114, .text text, .memory (.stringLiteral actual) => role == none && text == actual
  | _, _, _ => false

/-- The decoded `readonly.` rule at one site after `previous`: `readonly.` and `ldelema` emit
    their decoding, so an `ldelema` is read-only exactly when `readonly.` precedes it. -/
def readOnlyDecodedMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (emitted : Instruction) (skipEncoding := false) : Bool :=
  !(instruction.opcode == 143 || instruction.opcode == 65054) ||
    (skipEncoding || valueEncodingMatches previous instruction emitted)

/-- Covered opcodes emit exactly their encoding, and a class type test only from the raw
    `castclass` or `isinst` of the same class on an object. Elsewhere only a decided type test's
    word, a size constant or an exact runtime query may emit a scalar operation. `previous` is
    the raw instruction before `instruction`, `none` at the first pc. A `no.` prefix has no
    scalar emission, and `readonly.` must agree with the decoded address. -/
def scalarEmissionMatches (layouts : Array RawLayout) (role : Option FoldRole)
    (previous : Option RawInstruction) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction) (skipEncoding := false) : Bool :=
  if instruction.opcode == 0xFE19 || invalidPredecessor previous instruction then false
  else if !readOnlyDecodedMatches previous instruction emitted skipEncoding then false
  else if let some (.typeBranch taken) := role then typeBranchMatches instruction taken emitted
  else if let some (.result value) := role then
    match emitted with | .ldc_i4 bits => bits == if value then 1 else 0 | _ => false
  else if let some (opcode, type) := typeTestSource emitted then
    match instruction.operand, stack with
    | .type target, value :: _ =>
      instruction.opcode == opcode && type == target && value ∈ [.object, .opaque, .nullObject]
    | _, _ => false
  else if (match instruction.operand with
    | .call site => referenceContentQuery site | _ => false) then
    match instruction.operand, emitted with
    | .call site, .ldc_i4 bits => instruction.opcode == 40 &&
      referenceContentConstant layouts site == some bits
    | _, _ => false
  else if instruction.opcode == 77 && (stack.head?).any
      (fun kind => match kind with | .nativeMethodTable _ => true | _ => false) then
    match stack, emitted with
    | .nativeMethodTable _ :: _, .ldind .i => true
    | _, _ => false
  else if instruction.opcode == 88 && (match stack with
      | .nativeMethodTable _ :: _ | _ :: .nativeMethodTable _ :: _ => true | _ => false) then
    instruction.operand == .none && match stack, emitted with
    | offset :: .nativeMethodTable _ :: _, .add
    | .nativeMethodTable _ :: offset :: _, .add => offset ∈ [.word32, .native]
    | _, _ => false
  else if let .managed operation := emitted then match operation with
    | .address .. => instruction.opcode == 65030
    | .call .. => instruction.opcode == 41
  else if let some helper := unsafeReferenceHelper instruction then helper.matches emitted
  else if arrayEmission emitted then arrayMatches previous instruction stack emitted skipEncoding
  else if instruction.opcode == 114 ||
      (match emitted with | .memory (.stringLiteral _) => true | _ => false) then
    stringLiteralMatches role instruction emitted
  else if instruction.opcode == 20 && role ∈ [some .head, some .interior] then
    instruction.operand == .none && match emitted with | .nop => true | _ => false
  else if instanceFieldSite instruction emitted then
    if classOwned instruction then
      classFieldMatches previous instruction stack emitted skipEncoding
    else structFieldMatches previous instruction stack emitted skipEncoding
  else if scalarCovered instruction.opcode then
    scalarOpMatches previous instruction stack emitted skipEncoding
  else !scalarEmission emitted || match role, emitted with
    | _, .ldc_i4 bits => sizeConstant instruction bits ||
        platformField instruction == some bits ||
        (instruction.opcode == 40 && match instruction.operand with
          | .call site => platformConstant site == some bits
          | _ => false)
    | _, _ => false

/-- The result kind of a conversion opcode: `conv.i`/`conv.u` forms give native ints,
    `conv.i8`/`conv.u8` forms give `int64`, the rest `int32`. -/
private def resultKind (opcode : Nat) : ScalarKind :=
  if opcode ∈ [211, 212, 213, 138, 139, 224] then .native
  else if opcode ∈ [106, 110, 133, 137, 185, 186] then .word64 else .word32

/-- The UTF-8 bytes of `text`. -/
private def signatureBytes (text : String) : List UInt8 := text.toByteArray.data.toList

/-- Splits at every occurrence of `separator`; the fuel bounds the walk by the text length. -/
private def splitTextBytes (separator : List UInt8) :
    Nat → List UInt8 → List UInt8 → List (List UInt8)
  | 0, current, tail => [current.reverse ++ tail]
  | _ + 1, current, [] => [current.reverse]
  | remaining + 1, current, text@(c :: tail) =>
    if separator.isPrefixOf text then
      current.reverse :: splitTextBytes separator remaining [] (text.drop separator.length)
    else splitTextBytes separator remaining (c :: current) tail

private def splitBytes (text separator : List UInt8) : List (List UInt8) :=
  splitTextBytes separator (text.length + 1) [] text

/-- Replaces every occurrence of `pattern`, scanning left to right without overlap. -/
private def replaceTextBytes (pattern replacement : List UInt8) : Nat → List UInt8 → List UInt8
  | 0, text => text
  | _ + 1, [] => []
  | remaining + 1, text@(c :: tail) =>
    if pattern.isPrefixOf text then
      replacement ++ replaceTextBytes pattern replacement remaining (text.drop pattern.length)
    else c :: replaceTextBytes pattern replacement remaining tail

private def replaceBytes (text pattern replacement : List UInt8) : List UInt8 :=
  replaceTextBytes pattern replacement (text.length + 1) text

private def joinBytes (separator : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [text] => text
  | text :: tail => text ++ separator ++ joinBytes separator tail

/-- A type as it is spelled inside a method signature string: no scope, `!!n` for a
    method type parameter, `&` and `*` suffixes, and `<...>` for generic arguments. -/
private def scalarTypeBytes : TypeExpr → Option (List UInt8)
  | .void => some (signatureBytes "System.Void")
  | .atom _ name | .constructor _ name | .objectConstructor _ name | .object _ name =>
    some (signatureBytes name)
  | type@(.aggregate ..) => signatureBytes <$> spanElementName type
  -- Enum names cannot contain generic owner arguments.
  | .enum identity _ => (splitBytes (signatureBytes identity) [58, 58])[1]?
  | .parameter index => some (signatureBytes ("!!" ++ toString index))
  | .functionPointer .. | .signatureParameter .. | .modified .. | .ownerParameter _ => none
  -- `&` and `*`.
  | .byref element => (· ++ [38]) <$> scalarTypeBytes element
  | .pointer element => (· ++ [42]) <$> scalarTypeBytes element
  | .array element => (· ++ [91, 93]) <$> scalarTypeBytes element
  -- `Name<A>`, or `Name<A,B>` when the constructor already ends in `>`.
  | .apply constructor argument => do
    let name ← scalarTypeBytes constructor
    let element ← scalarTypeBytes argument
    return if name.reverse.head? == some 62 then
        name.take (name.length - 1) ++ [44] ++ element ++ [62]
      else name ++ [60] ++ element ++ [62]

/-- Splits a parameter list at top-level commas (44), tracking `<` (60) and `>` (62) depth;
    rejects empty entries and unbalanced brackets. -/
private def parameterTokens (depth : Nat) (current : List UInt8) :
    List UInt8 → Option (List (List UInt8))
  | [] => if depth != 0 then none else if current.isEmpty then some [] else some [current.reverse]
  | 44 :: [] => none
  | 44 :: tail =>
    if depth == 0 then
      if current.isEmpty then none else (current.reverse :: ·) <$> parameterTokens 0 [] tail
    else parameterTokens depth (44 :: current) tail
  | 60 :: tail => parameterTokens (depth + 1) (60 :: current) tail
  | 62 :: tail => if depth == 0 then none else parameterTokens (depth - 1) (62 :: current) tail
  | c :: tail => parameterTokens depth (c :: current) tail

/-- A signature token spells `type`, or is a type-parameter reference `!n` (33) standing for
    a non-scalar type, possibly under `&` (38) or `*` (42). -/
private def parameterTypeMatches (token : List UInt8) (type : TypeExpr) : Bool :=
  if scalarTypeBytes type == some token then true
  else match type with
    | .byref element => [33].isPrefixOf token && ![33, 33].isPrefixOf token &&
        token.reverse.head? == some 38 && scalarType element == .other
    | .pointer element => [33].isPrefixOf token && ![33, 33].isPrefixOf token &&
        token.reverse.head? == some 42 && scalarType element == .other
    | _ => [33].isPrefixOf token && ![33, 33].isPrefixOf token && scalarType type == .other

/-- Substitutes the site's method type arguments for `!!n` and, when the declaring type is
    generic, its type arguments for `!n`. -/
private def normalizeExternalIdentity (site : CallSite) (identity : List UInt8) :
    Option (List UInt8) := do
  let normalized ← site.typeArguments.zipIdx.reverse.foldlM (fun text (type, index) => do
    let name ← scalarTypeBytes type
    return replaceBytes text (signatureBytes ("!!" ++ toString index)) name) identity
  let owner ← scalarTypeBytes site.declaringType
  -- Split the owner at `<` to recover its generic arguments.
  match splitBytes owner [60] with
  | [] | [_] => return normalized
  | _ :: tail =>
    let suffix := joinBytes [60] tail
    if suffix.reverse.head? != some 62 then none else
      let arguments ← parameterTokens 0 [] (suffix.take (suffix.length - 1))
      return arguments.zipIdx.reverse.foldl (fun text (name, index) =>
        replaceBytes text (signatureBytes ("!" ++ toString index)) name) normalized

/-- Parentheses, `(` (40) and `)` (41), are balanced from `depth`. -/
private def balancedParentheses : Nat → List UInt8 → Bool
  | depth, [] => depth == 0
  | depth, 40 :: tail => balancedParentheses (depth + 1) tail
  | 0, 41 :: _ => false
  | depth + 1, 41 :: tail => balancedParentheses depth tail
  | depth, _ :: tail => balancedParentheses depth tail

/-- The parameter list in an external identity's signature names exactly the site's
    parameter types. -/
private def externalParametersMatch (site : CallSite) (identity : String) : Bool :=
  ((do
    let original := identity.toByteArray.data.toList
    if !balancedParentheses 0 original then none else
    let _ :: rest := splitBytes original [40] | none
    let rawTail ← rest.getLast?
    let tail ← normalizeExternalIdentity site rawTail
    if !balancedParentheses 1 tail || tail.reverse.head? != some 41 then none else
      let tokens ← parameterTokens 0 [] (tail.take (tail.length - 1))
      return tokens.length == site.parameterTypes.length &&
        (tokens.zip site.parameterTypes).all fun (token, type) =>
          parameterTypeMatches token type) : Option Bool).getD false

/-- The site's parameter types agree with its count and, for an external target, with the
    signature in its identity. -/
private def callParametersMatch (site : CallSite) : Bool :=
  site.parameterCount == site.parameterTypes.length && match site.target with
    | .managed _ => true
    | .external identity => externalParametersMatch site identity

/-- The result kind of an external call, trusted only when the return type at the start
    of the identity's signature (after `::`, before a space) spells the site's return type. -/
private def externalResult (site : CallSite) (identity : String) : ScalarKind :=
  if scalarType site.returnType == .other then .other else
  match normalizeExternalIdentity site identity.toByteArray.data.toList with
  | none => .other
  | some normalized =>
    let signature := (splitBytes normalized [58, 58])[1]?.getD []
    match site.returnType with
    | .atom _ name =>
      if (signatureBytes name ++ [32]).isPrefixOf signature then scalarType site.returnType
      else .other
    | .byref _ =>
      if ((splitBytes signature [32])[0]?.getD []).reverse.head? == some 38 then .reference
      else .other
    | .enum identity _ =>
      let name := (splitBytes (signatureBytes identity) [58, 58])[1]?.getD []
      if !name.isEmpty && (name ++ [32]).isPrefixOf signature then scalarType site.returnType
      else .other
    | .apply .. =>
      match scalarTypeBytes site.returnType with
      | some name => if (name ++ [32]).isPrefixOf signature then scalarType site.returnType
          else .other
      | none => .other
    | _ => .other

/-- The kind a call pushes. -/
private def callResult (site : CallSite) : ScalarKind :=
  if unsafePointerOffset ⟨0, 40, .call site⟩ || spanCallReturnsReference site ||
      (viewObservation ⟨0, 40, .call site⟩).any
        (fun operation => operation == .spanPinnable) then .reference
  else match site.target with
    | .managed _ => scalarType site.returnType
    | .external identity => externalResult site identity

/-- Exactly `newobj ReadOnlySpan<byte>(void*, int)`. -/
def byteSpanConstructor (opcode : Nat) (site : CallSite) : Bool :=
  opcode == 115 && site.name == ".ctor" && site.hasThis && !site.returnsValue &&
    site.typeArguments.isEmpty && site.parameterCount == 2 && site.returnType == .void &&
    site.declaringType == .apply (.constructor runtimeScope "System.ReadOnlySpan`1")
      (.atom runtimeScope "System.Byte") &&
    site.parameterTypes == [.pointer .void, .atom runtimeScope "System.Int32"] &&
    site.target == .external (runtimeScope ++
      "::System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)")

/-- Exact span pointer constructor, including owner scope and external signature. -/
private def spanConstructor (opcode : Nat) (site : CallSite) : Option (Nat × Bool) := do
  if opcode != 115 || site.name != ".ctor" || !site.hasThis || site.returnsValue ||
      !site.typeArguments.isEmpty || site.parameterCount != 2 || site.returnType != .void ||
      site.parameterTypes != [.pointer .void, .atom runtimeScope "System.Int32"] then none
    else pure ()
  let .apply (.constructor _ owner) elementType := site.declaringType | none
  let element ← spanElementName elementType
  let .span width writable ← spanStorage site.declaringType | none
  if site.target != .external (runtimeScope ++ "::System.Void " ++ owner ++ "<" ++ element ++
      ">::.ctor(System.Void*,System.Int32)") then none else some (width, writable)

/-- Span constructors retain the exact element width and readonly capability. -/
private def spanCreateMatches (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  let modeled := match instruction.operand with
    | .call site => byteSpanConstructor instruction.opcode site
    | _ => false
  if modeled then match emitted with | .memory .spanCreate => true | _ => false
  else if let .call site := instruction.operand then
    match spanConstructor instruction.opcode site with
    | some (width, writable) => match emitted with
      | .memory (.spanFromReference actual capability) =>
        spanConstructorMatches (.reference width writable) (.reference actual capability)
      | _ => false
    | none => match emitted with | .memory .spanCreate => false | _ => true
  else match emitted with | .memory .spanCreate => false | _ => true

/-- What a scalar site reads about the body's local slots: the declared type of each slot, and
    whether a `calli` consumes the slot as a native method pointer. -/
structure ScalarLocals where
  typeAt : Nat → Option TypeExpr
  pointer : Nat → Bool

/-- The local slots as the raw metadata lists state them, scanned at each site. -/
def ScalarLocals.ofLists (raw : RawMethod) (context : NativeDispatchContext) : ScalarLocals :=
  ⟨(raw.locals[·]?), context.pointerLocals.contains⟩

/-- The local slots read from a `FlowIndex` of the declared types and a `Std.TreeSet` of the
    pointer locals, each built once per body. -/
def ScalarLocals.indexed (raw : RawMethod) (context : NativeDispatchContext) : ScalarLocals :=
  ⟨(FlowIndex.ofList raw.locals).get?, (Std.TreeSet.ofList context.pointerLocals compare).contains⟩

/-- Indexes built once per body answer every local slot query exactly as the metadata lists do. -/
theorem ScalarLocals.indexed_eq (raw : RawMethod) (context : NativeDispatchContext) :
    ScalarLocals.indexed raw context = ScalarLocals.ofLists raw context := by
  have typeAt : (FlowIndex.ofList raw.locals).get? = (raw.locals[·]?) :=
    funext (FlowIndex.get?_ofList raw.locals)
  have pointer : (Std.TreeSet.ofList context.pointerLocals compare).contains =
      context.pointerLocals.contains := by
    funext index
    rw [Std.TreeSet.contains_ofList]
  rw [ScalarLocals.indexed, ScalarLocals.ofLists, typeAt, pointer]

#print axioms ScalarLocals.indexed_eq

/-- Contextual callable kinds retain the independently derived native home identity; `pointer`
    holds the locals a `calli` consumes. -/
private def dispatchScalar (context : NativeDispatchContext) (type : TypeExpr)
    (index : Option Nat := none) (pointer : Nat → Bool := context.pointerLocals.contains) :
    ScalarKind :=
  match nativeDispatchStorage context type index pointer with
  | some (.methodTable signature) => .nativeMethodTable signature
  | some (.methodPointer signature) => .methodPointer signature
  | _ => scalarType type

/-- The kind of argument `index`, counting `this` as argument 0. -/
private def argumentKind (raw : RawMethod)
    (context : NativeDispatchContext) (index : Nat) : Option ScalarKind :=
  if raw.hasThis && index == 0 then some (if raw.objectReceiver then .object else .reference)
  else dispatchScalar context <$> raw.parameters[index - (if raw.hasThis then 1 else 0)]?

/-- The kind an opcode with a fixed one-value push leaves on the stack, reading local slots
    through `locals`. -/
private def pushedKind (raw : RawMethod)
    (context : NativeDispatchContext) (locals : ScalarLocals)
    (instruction : RawInstruction) : Option ScalarKind := do
  match argumentOperation instruction with
  | some (.load index) => argumentKind raw context index
  | _ =>
    -- `ldloc`.
    if instruction.opcode ∈ [6, 7, 8, 9, 17, 65036] then
      let index ← localIndex instruction
      return dispatchScalar context (← locals.typeAt index) (some index) locals.pointer
    -- `ldarga`, `ldloca`, `ldflda` and `ldsflda`.
    else if instruction.opcode ∈ [18, 65037] then
      let index ← localIndex instruction
      let type ← locals.typeAt index
      -- A class instance's slot is never addressed, so no byref stands in for a receiver.
      if type matches .object .. then none else
      if (nativeDispatchStorage context type (some index) locals.pointer).isSome then none else
        return scalarType (.byref type)
    else if instruction.opcode ∈ [15, 65034] then
      match argumentOperation instruction with
      | some (.address index) =>
        -- An object receiver has no home, so its address is never taken.
        if raw.hasThis && index == 0 then
          if raw.objectReceiver then none else return .reference
        let type ← raw.parameters[index - (if raw.hasThis then 1 else 0)]?
        if type matches .object .. then none else
        if (nativeDispatchStorage context type).isSome then none else
          return scalarType (.byref type)
      | _ => none
    else if instruction.opcode ∈ [124, 127] then some .reference
    -- `ldfld` and `ldsfld`, then `ldobj`.
    else if instruction.opcode == 123 || instruction.opcode == 126 then
      let .field owner _ type _ static := instruction.operand | none
      if instruction.opcode == 123 && !static && owner matches .object .. &&
          opaqueFieldType type then
        return .opaque
      return scalarType type
    else if instruction.opcode == 113 then
      let .type type := instruction.operand | none
      return scalarType type
    -- `ldind.i`, `ldind.i8`, then `ldind.i1` through `ldind.u4` and `sizeof`.
    else if instruction.opcode == 77 then some .native
    else if instruction.opcode == 76 then some .word64
    else if instruction.opcode ∈ [70, 71, 72, 73, 74, 75, 65052] then some .word32
    else some .other

/-- The stack kinds after `instruction`, with local slots read through `locals`, or `none` if
    its operands have the wrong kinds. -/
def scalarTransfer (raw : RawMethod) (instruction : RawInstruction)
    (stack : List ScalarKind) (role : Option FoldRole := none)
    (context : NativeDispatchContext := nativeDispatchContext raw)
    (locals : ScalarLocals := .ofLists raw context) : Option (List ScalarKind) := do
  let opcode := instruction.opcode
  if role matches some (.typeBranch _) then
    let _ :: _ :: tail := stack | none
    return tail
  if role matches some (.result _) then
    let _ :: _ :: tail := stack | none
    return .word32 :: tail
  -- A literal outside a folded throw is an object; a folded throw's message is never a value.
  if opcode == 114 && role == none then
    let .text _ := instruction.operand | none
    return .object :: stack
  if opcode == 65030 then
    let .call site := instruction.operand | none
    let signature : ManagedSignature :=
      ⟨callableType site.returnType, site.parameterTypes.map callableType⟩
    if site.hasThis || managedSignature signature.typeExpr != some signature then none else
      return .methodPointer signature :: stack
  if opcode == 41 then
    let .indirectCall result parameters false false 0 := instruction.operand | none
    let signature : ManagedSignature := ⟨callableType result, parameters.map callableType⟩
    let .methodPointer actual :: values := stack | none
    if actual != signature || managedSignature signature.typeExpr != some signature then none else
    let expected := parameters.reverse.map scalarType
    if expected.length > values.length ||
        !(values.take expected.length == expected) then none else
      return (if result == .void then [] else [scalarType result]) ++ values.drop expected.length
  if opcode == 77 then
    if let .nativeMethodTable signature :: rest := stack then return .methodPointer signature :: rest
  if opcode == 88 then
    match stack with
    | offset :: .nativeMethodTable signature :: rest
    | .nativeMethodTable signature :: offset :: rest =>
      if offset ∈ [.word32, .native] then return .nativeMethodTable signature :: rest else none
    | _ => pure ()
  if opcode == 142 then
    if let .methodTable _ :: rest := stack then return .native :: rest
  if opcode == 151 || opcode == 163 then
    if let index :: .methodTable signature :: rest := stack then
      if index ∉ [.word32, .native] || (opcode == 163 &&
          (match instruction.operand with
           | .type type => managedSignature type != some signature | _ => true)) then none else
        return .methodPointer signature :: rest
  if opcode == 141 then
    let .type token := instruction.operand | none
    let length :: tail := stack | none
    if length ∉ [.word32, .native] then none else
    -- An array of class references is itself an object reference.
    if token matches .object .. then return .object :: tail else
    let element ← arrayElementType token
    return .array element :: tail
  if arrayCovered opcode then return (← arrayStep instruction stack)
  -- `castclass` and `isinst` of a class leave an object reference.
  if opcode == 116 || opcode == 117 then
    match instruction.operand, stack with
    | .type (.object ..), value :: tail =>
      if value ∈ [.object, .opaque, .nullObject] then return .object :: tail
    | _, _ => pure ()
  if opcode == 20 then
    if instruction.operand == .none then return .nullObject :: stack else none
  if opcode ∈ [44, 45, 57, 58] then
    let value :: tail := stack | none
    if numeric value || value ∈ [.reference, .nullObject, .object, .opaque] then return tail
    else none
  if compareBranch opcode then
    let right :: left :: tail := stack | none
    if compatibleBinary left right || referenceComparison opcode left right then return tail else none
  if opcode == 65039 then
    match stack with
    | [kind] => if kind ∈ [.word32, .native] then return [.reference] else none
    | _ => none
  -- Constants.
  if 21 <= opcode && opcode <= 33 then
    let _ ← literal instruction
    return (if opcode == 33 then .word64 else .word32) :: stack
  -- Arithmetic, shifts, `neg`, `not` and conversions.
  if scalarBinary opcode then
    let right :: left :: tail := stack | none
    if (opcode == 88 && referenceAddition left right) ||
        (opcode == 89 && left == .reference && right ∈ [.word32, .native]) then
      return .reference :: tail
    if opcode == 89 && left == .reference && right == .reference then
      return .native :: tail
    if !(compatibleBinary left right || referenceComparison opcode left right) then none else
      return (if comparison opcode then .word32
        else if mixedNative left right then .native else left) :: tail
  if opcode ∈ [98, 99, 100] then
    let right :: left :: tail := stack | none
    if !numeric left || right ∉ [.word32, .native] then none else return left :: tail
  if opcode == 101 || opcode == 102 || conversion opcode then
    let value :: tail := stack | none
    if !numeric value then none else
      return (if conversion opcode then resultKind opcode else value) :: tail
  -- Stores to locals and arguments must fit the slot.
  if opcode ∈ [10, 11, 12, 13, 19, 65038] then
    let index ← localIndex instruction
    let type ← locals.typeAt index
    let value :: tail := stack | none
    if storageCompatible value (dispatchScalar context type (some index) locals.pointer) then
      return tail
    else none
  if let some (.store index) := argumentOperation instruction then
    let expected ← argumentKind raw context index
    let value :: tail := stack | none
    if storageCompatible value expected then return tail else none
  -- `dup`.
  if opcode == 37 then
    let value :: tail := stack | none
    return value :: value :: tail
  -- `call` and `newobj`: the operands must have the signature's kinds.
  if opcode == 40 || opcode == 111 || opcode == 115 then
    let .call site := instruction.operand | none
    let expected := if let some (copy, _) := unsafeBlockCall instruction then
        [.word32, if copy then .reference else .word32, .reference] else
        if let some (type, read, _) := unsafeValueCall instruction then
        (if read then [] else [scalarType type]) ++ [.reference] else
      if unsafeReferenceHelper instruction == some .asRef then [.reference] else
      if nullGuardCall instruction then [.object, .object] else
      if unsafePointerOffset instruction then [.word32, .reference] else
      if (opcode == 115 || opcode == 40) && (spanConstructor 115 site).isSome
      then [.word32, .reference] ++
        (if opcode == 40 then [scalarType (.byref site.declaringType)] else []) else
      site.parameterTypes.reverse.map scalarType ++
        (if opcode != 115 && site.hasThis then [receiverKind site.declaringType] else [])
    -- A folded throw's literal or null message arguments are never values on the stack.
    let folded := opcode == 115 && role == some .interior
    let inputs := if folded then
        stack.map (fun kind => if kind == .nullObject then .other else kind)
      else stack
    let expected := if folded then
        expected.map (fun kind => if kind == .object then .other else kind)
      else expected
    let pops := expected.length
    if !callParametersMatch site || pops > stack.length || !((inputs.take pops).zip expected).all (fun (value, home) =>
        value == home || (value == .nullObject &&
          (match home with | .array _ | .methodTable _ | .object => true | _ => false))) ||
        site.returnsValue != (site.returnType != .void) then none else
      return (if opcode == 115 then [scalarType site.declaringType]
        else if site.returnsValue then [callResult site] else []) ++ stack.drop pops
  -- `ret` leaves exactly the return value, of a compatible kind.
  if opcode == 42 then
    if raw.returnType == .void then
      if stack.isEmpty then return [] else none
    else match stack with
      | [value] => if storageCompatible value (scalarType raw.returnType) then return [] else none
      | _ => none
  -- Everything else by its fixed stack effect.
  let (pops, pushes) ← rawStackEffect opcode
  if pops > stack.length then none else
    if pushes == 0 then return stack.drop pops
    else if pushes == 1 then
      return (← pushedKind raw context locals instruction) :: stack.drop pops
    else none

/-- A `stloc` of a 64-bit or native value into a 32-bit local, emitted as a store to that
    same local, whose type `locals` gives. The checked interpreter rejects that store, so the
    site needs no successor. -/
def scalarStoreFault (raw : RawMethod) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Instruction)
    (locals : ScalarLocals := .ofLists raw (nativeDispatchContext raw)) : Bool :=
  ((do
    if instruction.opcode ∉ [10, 11, 12, 13, 19, 65038] then none else
    let index ← localIndex instruction
    let type ← locals.typeAt index
    let value :: _ := stack | none
    return scalarType type == .word32 && value ∈ [.word64, .native] &&
      match emitted with
      | .stloc actual => actual == index
      | _ => false) : Option Bool).getD false

/-- A `readonly.` site requires the raw instruction after it, `next`, to be `ldelema` (143), so a
    `readonly.` that ends the body is refused. This is the rule that only `ldelema` follows
    `readonly.`: a reachable `readonly.` falls through to the instruction after it, which
    `PrefixEntryFree` keeps every branch out of. Translated sites never consult the decoder, so
    the rule holds them to it until no site is translated. -/
def readOnlyPrefixMatches (next : Option RawInstruction) (instruction : RawInstruction) : Bool :=
  instruction.opcode != 65054 || next.any (prefixTakes instruction)

/-- Only ordinary, unfolded, non-hole sites can reuse the raw value decoder's comparison. -/
private def decodedValueSite (raw : RawInstruction) (role : Option FoldRole)
    (emitted : Instruction) : Bool :=
  !methodTokenCall raw.opcode && role.isNone && !(emitted matches .unadmitted _)

/-- One pc of the certificate: an unreachable pc must emit a hole; a reachable one must
    agree with the feature stack depth, satisfy the indirect access rule and the `readonly.` rule
    (`readOnlyPrefixMatches`) over the raw instructions `rawAt` gives, emit the right encoding
    after the raw instruction before it, and give every successor, which must be reachable,
    exactly the resulting stack kinds, with local slots read through `locals`. -/
private def checkScalarSite (decoded : Bool) (layouts : Array RawLayout) (raw : RawMethod)
    (context : NativeDispatchContext) (locals : ScalarLocals) (rawAt : Nat → Option RawInstruction)
    (successor : List ScalarKind → Nat → Bool) :
    (RawInstruction × Option FoldRole) × Nat → Option FeatureState → Option (List ScalarKind) →
      Instruction → Bool
  | _, none, none, .unadmitted _ => true
  | ((instruction, role), pc), some feature, some stack, emitted =>
    let skipEncoding := decoded && decodedValueSite instruction role emitted
    stack.length == feature.stack.length && stack.length <= raw.maxStack &&
      (match role with
        | some (.spanConstructor index constructor) => match emitted with
          | .initializeSpanLocal actual operation => index == actual && spanConstructorMatches constructor operation
          | _ => false
        | _ => spanCreateMatches instruction emitted && spanCallMatches instruction emitted) &&
      indirectSiteWindow rawAt pc instruction emitted skipEncoding &&
      readOnlyPrefixMatches (rawAt (pc + 1)) instruction &&
      scalarEmissionMatches layouts role (rawBefore rawAt pc) instruction stack emitted
        skipEncoding &&
      (scalarStoreFault raw instruction stack emitted locals ||
      match scalarTransfer raw instruction stack role context locals,
          featureSuccessors role pc instruction feature.stack with
      | some after, some successors =>
        successors.all (successor after)
      | _, _ => false)
  | _, _, _, _ => false

/-- The scalar certificate covers exactly the feature-reachable pcs, starts with an empty
    stack, and passes every site check. -/
def ScalarFlowValid (layouts : Array RawLayout) (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Instruction) (decoded := false) : Prop :=
  let context := nativeDispatchContext raw
  let locals := ScalarLocals.indexed raw context
  let rawAt := (FlowIndex.ofList raw.code).get?
  raw.code.length = features.length ∧ raw.code.length = certificate.length ∧
    raw.code.length = code.length ∧
  certificate[0]? = some (some []) ∧
  all3Flow (fun lookup instruction (feature, stack) emitted =>
      checkScalarSite decoded layouts raw context locals rawAt
        (fun after target => match lookup target with
          | some (some _, incoming) => incoming == some after
          | _ => false) instruction feature stack emitted)
    (.ofList (features.zip certificate)) 0
    (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx (features.zip certificate) code = true

instance (layouts : Array RawLayout) (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate)
    (code : List Instruction) (decoded : Bool) :
    Decidable (ScalarFlowValid layouts raw features certificate code decoded) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Pairing feature and scalar states preserves both the reachability and exact stack
    check, including targets missing from either certificate. -/
theorem scalarSuccessor_zip (features : FeatureCertificate)
    (certificate : ScalarCertificate)
    (target : Nat) (after : List ScalarKind) :
    (match (features.zip certificate)[target]? with
      | some (some _, incoming) => incoming == some after
      | _ => false) =
    (match features[target]? with
      | some (some _) => certificate[target]? == some (some after)
      | _ => false) := by
  simp only [List.zip, List.getElem?_zipWith]
  cases features[target]? with
  | none => rfl
  | some feature =>
    cases certificate[target]? with
    | none => cases feature <;> rfl
    | some stack => cases feature <;> cases stack <;> rfl

#print axioms scalarSuccessor_zip

/-- Streaming scalar validation preserves all list-indexed site checks and lengths, with local
    slots read from the metadata lists at each site. -/
theorem ScalarFlowValid_iff_list (layouts : Array RawLayout) (raw : RawMethod)
    (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Instruction) (decoded : Bool) :
    ScalarFlowValid layouts raw features certificate code decoded ↔
      raw.code.length = features.length ∧ raw.code.length = certificate.length ∧
      raw.code.length = code.length ∧ certificate[0]? = some (some []) ∧
      all3 (fun (instruction, feature) stack emitted =>
          checkScalarSite decoded layouts raw (nativeDispatchContext raw)
            (ScalarLocals.ofLists raw (nativeDispatchContext raw))
            (fun target => raw.code[target]?)
            (fun after target => match features[target]? with
            | some (some _) => certificate[target]? == some (some after)
            | _ => false)
            instruction feature stack emitted)
        ((raw.code.zip (foldRoles raw.locals raw.code)).zipIdx.zip features) certificate code =
        true := by
  dsimp only [ScalarFlowValid]
  have rawAt : (FlowIndex.ofList raw.code).get? = (fun target => raw.code[target]?) :=
    funext (FlowIndex.get?_ofList raw.code)
  rw [ScalarLocals.indexed_eq, rawAt,
    all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm]
  simp only [scalarSuccessor_zip]
  by_cases featureLength : raw.code.length = features.length
  · by_cases scalarLength : raw.code.length = certificate.length
    · rw [all3_zip_states _ _ _ _ _ (featureLength.symm.trans scalarLength)]
      simp only [List.length_zipIdx, List.length_zip]
      exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_eq featureLength)
    · simp [scalarLength]
  · simp [featureLength]

#print axioms ScalarFlowValid_iff_list

/-- At a decoded site each skipped encoding comparison would succeed. -/
private theorem decodedSite_eq (layouts : Array RawLayout) (raw : RawMethod)
    (context : NativeDispatchContext) (locals : ScalarLocals) (rawAt : Nat → Option RawInstruction)
    (successor : List ScalarKind → Nat → Bool) (instruction : RawInstruction)
    (role : Option FoldRole) (pc : Nat) (feature : Option FeatureState)
    (stack : Option (List ScalarKind)) (emitted : Instruction)
    (same : methodTokenCall instruction.opcode = false → role = none →
      emitted = Instruction.ofRaw (rawBefore rawAt pc) instruction ∨
        emitted = .unadmitted instruction.opcode) :
    checkScalarSite true layouts raw context locals rawAt successor ((instruction, role), pc)
        feature stack emitted =
      checkScalarSite false layouts raw context locals rawAt successor ((instruction, role), pc)
        feature stack emitted := by
  have redundant :
      (decodedValueSite instruction role emitted ||
        valueEncodingMatches (rawBefore rawAt pc) instruction emitted) =
          valueEncodingMatches (rawBefore rawAt pc) instruction emitted := by
    by_cases called : methodTokenCall instruction.opcode = true
    · simp [decodedValueSite, called]
    by_cases unfolded : role = none
    case neg => cases role <;> simp_all [decodedValueSite]
    obtain same | hole := same (Bool.eq_false_iff.mpr called) unfolded
    case inr => simp [hole, decodedValueSite]
    cases partialDecode : Instruction.ofRaw? (rawBefore rawAt pc) instruction with
    | none =>
      simp [Instruction.ofRaw, partialDecode] at same
      subst emitted
      simp [decodedValueSite]
    | some value =>
      rw [Instruction.ofRaw_of_ofRaw? partialDecode] at same
      subst emitted
      simp [valueEncodingMatches, partialDecode,
        Instruction.sameValue_self_of_ofRaw? partialDecode]
  cases feature <;> cases stack <;> first
    | rfl
    | (cases emitted <;> rfl)
    | (unfold checkScalarSite
       delta indirectSiteWindow scalarEmissionMatches indirectAccessMatches scalarOpMatches
         arrayMatches classFieldMatches structFieldMatches readOnlyDecodedMatches
       simp only [Bool.true_and, Bool.false_and, redundant, Bool.false_or])

#print axioms decodedSite_eq

/-- A certificate checked against the decoded code also passes every explicit encoding check. -/
theorem ScalarFlowValid.of_decoded {layouts : Array RawLayout} {raw : RawMethod}
    {features : FeatureCertificate} {certificate : ScalarCertificate} {code : List Instruction}
    {live : Nat → Bool} {localKind : TypeExpr → Option LocalKind} {decodeCall : CallDecoder}
    (same : code = Instruction.ofRawCode none raw.code
        (Instruction.withCallDecoder (foldRoles raw.locals raw.code).toArray
          live localKind decodeCall))
    (valid : ScalarFlowValid layouts raw features certificate code true) :
    ScalarFlowValid layouts raw features certificate code false := by
  dsimp only [ScalarFlowValid] at valid ⊢
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm] at valid ⊢
  refine ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, ?_⟩
  rw [← valid.2.2.2.2]
  apply all3_congr_getElem?
  rintro pc ⟨⟨instruction, role⟩, index⟩ ⟨feature, stack⟩ emitted site _ emittedAt
  simp only [List.getElem?_zipIdx, Nat.zero_add, Option.map_eq_some_iff] at site
  obtain ⟨pair, entry, found⟩ := site
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj found
  have rawAt := (List.getElem?_zip_eq_some.mp entry).1
  rw [same, Instruction.ofRawCode_getElem? raw.code pc _, Instruction.ofRawAt, rawAt]
    at emittedAt
  apply Eq.symm
  apply decodedSite_eq
  intro ordinary unfolded
  have roleAt := (List.getElem?_zip_eq_some.mp entry).2
  rw [unfolded] at roleAt
  cases active : live pc with
  | false =>
    exact Or.inr (by simpa [Instruction.withCallDecoder, active] using
      (Option.some.inj emittedAt).symm)
  | true =>
    exact Or.inl (by simpa [Instruction.withCallDecoder, active, ordinary, roleAt, rawBefore,
      FlowIndex.get?_ofList] using (Option.some.inj emittedAt).symm)

#print axioms ScalarFlowValid.of_decoded

/-- At every reachable pc the emitted instruction is the scalar encoding the raw one implies
    after the raw instruction before it. -/
theorem ScalarFlowValid.instruction_checked {layouts : Array RawLayout} {raw : RawMethod}
    {features : FeatureCertificate}
    {certificate : ScalarCertificate} {code : List Instruction}
    {decoded : Bool} (valid : ScalarFlowValid layouts raw features certificate code decoded)
    {live : Nat → Bool} {localKind : TypeExpr → Option LocalKind} {decodeCall : CallDecoder}
    (codeDecodes : decoded = true → code =
      Instruction.ofRawCode none raw.code
        (Instruction.withCallDecoder (foldRoles raw.locals raw.code).toArray
          live localKind decodeCall))
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole} {feature : FeatureState}
    {stack : List ScalarKind} {emitted : Instruction}
    (rawAt : raw.code[pc]? = some instruction)
    (roleAt : (foldRoles raw.locals raw.code)[pc]? = some role)
    (featureAt : features[pc]? = some (some feature))
    (stackAt : certificate[pc]? = some (some stack)) (emittedAt : code[pc]? = some emitted) :
    scalarEmissionMatches layouts role (rawBefore (raw.code[·]?) pc) instruction stack emitted =
      true := by
  have pairAt : (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx[pc]? =
      some ((instruction, role), pc) := by
    simp [List.getElem?_zipIdx, List.getElem?_zip_eq_some, rawAt, roleAt]
  have statesAt : (features.zip certificate)[pc]? = some (some feature, some stack) :=
    List.getElem?_zip_eq_some.mpr ⟨featureAt, stackAt⟩
  have checkedFlow : ScalarFlowValid layouts raw features certificate code false := by
    cases decoded
    · exact valid
    · exact valid.of_decoded (codeDecodes rfl)
  have sites := checkedFlow.2.2.2.2
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm] at sites
  have checked := all3_at sites pairAt statesAt emittedAt
  simp only [checkScalarSite, Bool.false_and, Bool.and_eq_true] at checked
  simpa only [rawBefore, FlowIndex.get?_ofList] using checked.1.2

#print axioms ScalarFlowValid.instruction_checked

/-- At a live folded pc in a prefix-valid literal, the decoder selects its certified
    instruction. The decoded operation passes the feature and scalar checks at that pc.
    A direct tail call also needs the operand check that binds its managed target. -/
theorem fold_decoding_agreement {layouts : Array RawLayout} {raw : RawMethod}
    {constants : Nat → Option W32} {linkAt : Nat → Option Link} {profile : FeatureProfile}
    {features : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    {scalars : ScalarCertificate}
    (prefixes : rawPrefixesValid raw.returnType raw.code = true)
    (featureFlow : FeatureFlowValid layouts constants linkAt raw profile features reachable code)
    (scalarFlow : ScalarFlowValid layouts raw features scalars code false)
    {pc : Nat} {instruction : RawInstruction} {role : FoldRole} {state : FeatureState}
    {stack : List ScalarKind} {emitted : Instruction}
    (rawAt : raw.code[pc]? = some instruction)
    (roleAt : (foldRoles raw.locals raw.code)[pc]? = some (some role))
    (featureAt : features[pc]? = some (some state)) (stackAt : scalars[pc]? = some (some stack))
    (codeAt : code[pc]? = some emitted)
    (supported : match role with
      | .blocked | .spanConstructor .. => False
      | .tailCall => instruction.opcode = 40 ∧
        valueEncodingMatches (rawBefore (raw.code[·]?) pc) instruction emitted = true
      | _ => True) :
    let previous := rawBefore (raw.code[·]?) pc
    invalidPredecessor previous instruction = false ∧
      Instruction.ofRole? role previous instruction = some emitted ∧
      ∀ decoded, Instruction.ofRole? role previous instruction = some decoded →
        featureOpMatchesAt layouts raw (some role) instruction decoded (fun _ => previous) = true ∧
        scalarEmissionMatches layouts (some role) previous instruction stack decoded = true := by
  have feature := featureFlow.instruction_checked rawAt roleAt featureAt codeAt
  have scalar := scalarFlow.instruction_checked (live := fun _ => true)
    (localKind := fun _ => none) (decodeCall := fun _ _ raw => .unadmitted raw.opcode)
    (by intro impossible; contradiction) rawAt roleAt featureAt stackAt codeAt
  have bound : Instruction.ofRole? role (rawBefore (raw.code[·]?) pc) instruction =
      some emitted := by
    cases role with
    | argument => exact argument_of_featureOpMatchesAt feature
    | tailCall => exact tailCall_of_valueEncodingMatches supported.1 supported.2
    | blocked | spanConstructor => exact supported.elim
    | head | interior | result | raise | typeBranch =>
      exact (fixedRole_matches _ _ _ _ _ _ trivial).mp feature
  refine ⟨?_, bound, ?_⟩
  · cases pc with
    | zero => rfl
    | succ index =>
      simp only [rawBefore, Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, if_false]
      cases before : raw.code[index]? with
      | none => rfl
      | some modifier => exact rawPrefixesValid_predecessor prefixes before rawAt
  · intro decoded found
    cases Option.some.inj (bound.symm.trans found)
    exact ⟨feature, scalar⟩

#print axioms fold_decoding_agreement

end CIL.Extraction
