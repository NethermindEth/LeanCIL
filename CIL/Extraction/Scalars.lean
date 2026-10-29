import CIL.Extraction.Features
import CIL.Extraction.UnsafeReferences
import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.SpanCalls
import CIL.Extraction.ViewObservations

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
  | array (element : ArrayElement)
  | enumSpan (element : ArrayElement) (writable : Bool) (reference : Bool)
  | methodPointer (signature : ManagedSignature)
  | methodTable (signature : ManagedSignature)
  | nativeMethodTable (signature : ManagedSignature)
  deriving DecidableEq, Repr

/-- The claimed stack kinds (top first) at each raw pc; `none` where the pc is unreachable. -/
abbrev ScalarCertificate := List (Option (List ScalarKind))

/-- The stack kind of a metadata type: small integers widen to `word32`, enums use their
    underlying type. -/
def scalarType : TypeExpr → ScalarKind
  | .enum _ underlying => scalarType underlying
  | .pointer .void => .other
  | .byref element => match scalarType element with
      | .enumSpan identity writable _ => .enumSpan identity writable true
      | _ => .reference
  | .pointer _ => .reference
  | .array element => match managedSignature element with
    | some signature => .methodTable signature
    | none => (arrayElementType element).map ScalarKind.array |>.getD .other
  | type@(.functionPointer ..) => (managedSignature type).map ScalarKind.methodPointer |>.getD .other
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

private def numeric (kind : ScalarKind) : Bool := kind ∈ [.word32, .word64, .native]

/-- A value of kind `value` may be stored in a slot of kind `home`; `word64` and `native`
    share one representation on the admitted 64-bit targets. -/
private def storageCompatible (value home : ScalarKind) : Bool :=
  value == home || (value == .nullObject &&
    (match home with | .array _ | .methodTable _ => true | _ => false)) ||
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

/-- Raw array opcodes in the supported integer and element-address subset. -/
private def arrayCovered (opcode : Nat) : Bool :=
  (142 ≤ opcode && opcode ≤ 151) ||
    (155 ≤ opcode && opcode ≤ 159) || opcode ∈ [163, 164]

/-- Null is a permitted array operand, but arbitrary opaque/reference values are not. -/
private def arrayOperand : ScalarKind → Option (Option ArrayElement)
  | .array element => some (some element)
  | .nullObject => some none
  | _ => none

/-- Exact array instruction and stack transition, including primitive tokens and element types. -/
private def arrayStep (instruction : RawInstruction) (stack : List ScalarKind) :
    Option (MemoryOp × List ScalarKind) := do
  let opcode := instruction.opcode
  if opcode == 142 then
    let array :: tail := stack | none
    let _ ← arrayOperand array
    if instruction.operand == .none then return (.arrayLength, .native :: tail) else none
  let store := (155 ≤ opcode && opcode ≤ 159) || opcode == 164
  let (value, input) := if store then (stack.head?, stack.drop 1) else (none, stack)
  let index :: array :: tail := input | none
  if index ∉ [.word32, .native] then none else pure ()
  let element ← arrayOperand array
  if opcode == 143 then
    let .type token := instruction.operand | none
    let expected ← arrayElementType token
    if element.isSome && element != some expected then none else
      return (.arrayAddress expected, .reference :: tail)
  if opcode ∈ [163, 164] then
    let .type token := instruction.operand | none
    let expected ← arrayElementType token
    if element.isSome && element != some expected then none else pure ()
    match expected with
    | .aggregate .. | .vector .. =>
      if store then
        if value == some .other then return (.arrayTransfer expected true, tail) else none
      else return (.arrayTransfer expected false, .other :: tail)
    | _ => pure ()
  let (width, signed, native) : Nat × Bool × Bool ←
    if opcode ∈ [163, 164] then do
      let .type token := instruction.operand | none
      let expected ← arrayElementType token
      if element.isSome && element != some expected then none else
        pure (expected.width, expected.signed, expected.native)
    else do
      if instruction.operand != .none then none else pure ()
      let (width, signed, native) ← match opcode with
        | 144 => some (1, true, false) | 145 => some (1, false, false)
        | 146 => some (2, true, false) | 147 => some (2, false, false)
        | 148 | 149 => some (4, false, false)
        | 150 => some (8, false, false) | 151 | 155 => some (8, false, true)
        | 156 => some (1, false, false) | 157 => some (2, false, false)
        | 158 => some (4, false, false) | 159 => some (8, false, false)
        | _ => none
      if let some actual := element then
        if (match actual with | .aggregate .. | .vector .. => true | _ => false) then none else pure ()
        if actual.width != width || actual.native != native then none else pure ()
      pure (width, signed, native)
  let kind := if native then ScalarKind.native else if width == 8 then .word64 else .word32
  if store then
    if value == some kind then return (.arrayStore width, tail) else none
  else return (.arrayLoad width signed, kind :: tail)

/-- Array operations cannot be introduced through an unrelated stack-effect-only encoding. -/
private def arrayEmission : Op → Bool
  | .newArray _ => true
  | .memory .arrayLength | .memory (.arrayLoad ..) | .memory (.arrayStore _)
  | .memory (.arrayAddress ..) => true
  | .memory (.arrayTransfer ..) => true
  | _ => false

/-- The emitted array operation agrees exactly with its independently decoded raw opcode. -/
private def arrayMatches (instruction : RawInstruction) (stack : List ScalarKind)
    (emitted : Op) : Bool :=
  if instruction.opcode == 141 then
    match instruction.operand, stack, emitted with
    | .type token, length :: _, .newArray element =>
      length ∈ [.word32, .native] && element.allocationSupported &&
        arrayElementType token == some element
    | _, _, _ => false
  else
  match arrayStep instruction stack, emitted with
  | some (.arrayLength, _), .memory .arrayLength => true
  | some (.arrayLoad width signed, _), .memory (.arrayLoad actual polarity) =>
    width == actual && signed == polarity
  | some (.arrayStore width, _), .memory (.arrayStore actual) => width == actual
  | some (.arrayAddress element _, _), .memory (.arrayAddress actual _) =>
    element == actual.metadata
  | some (.arrayTransfer element store, _), .memory (.arrayTransfer actual actualStore) =>
    element == actual.metadata && store == actualStore
  | _, _ => false
/-- Opcodes whose emitted encoding the scalar check fixes: integer constants, arithmetic,
    shifts, `neg`, `not`, conversions and compare-branches. -/
def scalarCovered (opcode : Nat) : Bool :=
  opcode == 141 || arrayCovered opcode || (21 <= opcode && opcode <= 33) ||
    scalarBinary opcode || conversion opcode ||
    compareBranch opcode || opcode ∈ [20, 44, 45, 57, 58, 98, 99, 100, 101, 102, 65054]

/-- The emitted operation each covered non-branch opcode must produce. -/
private def scalarEncodingMatches (opcode : Nat) (emitted : Op) : Bool :=
  match opcode, emitted with
  -- Arithmetic, division and remainder.
  | 88, .add | 89, .sub | 90, .mul => true
  | 91, .divide true false | 92, .divide false false
  | 93, .divide true true | 94, .divide false true => true
  -- Bitwise, shifts, `neg` and `not`.
  | 95, .band | 96, .bor | 97, .bxor | 98, .shl | 99, .shr | 100, .shrUn
  | 101, .neg | 102, .bnot => true
  -- Conversions; `checkedConvert width signed unsignedInput`.
  | 103, .convI1 | 104, .convI2 | 105, .convI4 | 106, .convI8 | 109, .convU4 | 110, .convU8 => true
  | 130, .checkedConvert 8 true true | 131, .checkedConvert 16 true true
  | 132, .checkedConvert 32 true true | 133, .checkedConvert 64 true true
  | 134, .checkedConvert 8 false true | 135, .checkedConvert 16 false true
  | 136, .checkedConvert 32 false true | 137, .checkedConvert 64 false true
  | 138, .checkedConvert 64 true true | 139, .checkedConvert 64 false true
  | 179, .checkedConvert 8 true false | 180, .checkedConvert 8 false false
  | 181, .checkedConvert 16 true false | 182, .checkedConvert 16 false false
  | 183, .checkedConvert 32 true false | 184, .checkedConvert 32 false false
  | 185, .checkedConvert 64 true false | 186, .checkedConvert 64 false false => true
  | 209, .convU2 | 210, .convU1 | 211, .convI8 | 224, .convU => true
  | 212, .checkedConvert 64 true false | 213, .checkedConvert 64 false false => true
  -- Overflow-checked arithmetic and comparisons.
  | 214, .checkedArithmetic .add true | 215, .checkedArithmetic .add false
  | 216, .checkedArithmetic .mul true | 217, .checkedArithmetic .mul false
  | 218, .checkedArithmetic .sub true | 219, .checkedArithmetic .sub false => true
  | 65025, .eq | 65026, .gt | 65027, .gtu | 65028, .lt | 65029, .ltu => true
  | _, _ => false

/-- The emitted branch each compare-branch opcode must produce, keeping its target. -/
private def branchEncodingMatches (opcode target : Nat) (emitted : Op) : Bool :=
  match (if opcode <= 55 then opcode - 46 else opcode - 59), emitted with
  | 0, .beq actual | 1, .bge actual | 2, .bgt actual | 3, .ble actual | 4, .blt actual
  | 5, .bne actual | 6, .bgeu actual | 7, .bgtu actual | 8, .bleu actual
  | 9, .bltu actual => actual == target
  | _, _ => false

/-- One operand is a native int and the other an `int32`. -/
private def mixedNative (left right : ScalarKind) : Bool :=
  (left == .native && right == .word32) || (left == .word32 && right == .native)

/-- Operand kinds a two-operand opcode accepts: equal numeric kinds, or native with `int32`. -/
private def compatibleBinary (left right : ScalarKind) : Bool :=
  numeric left && numeric right && (left == right || mixedNative left right)

/-- Object null supports equality; only managed references support unsigned ordering. -/
private def referenceComparison (opcode : Nat) (left right : ScalarKind) : Bool :=
  left == right &&
    ((opcode ∈ [46, 51, 59, 64, 65025] && left ∈ [.reference, .nullObject]) ||
      (opcode ∈ [52, 53, 54, 55, 65, 66, 67, 68, 65027, 65029] && left == .reference))

/-- Mixed native/int32 operands require exactly one `nativeBinary` wrapper; any other pair
    forbids it. -/
private def nativeWrapped (left right : ScalarKind) (encoding : Op → Bool) : Op → Bool
  | .nativeBinary operation => mixedNative left right && encoding operation
  | operation => !mixedNative left right && encoding operation

/-- The constant an `ldc` instruction must emit; an out-of-range operand has none. -/
private def literal (instruction : RawInstruction) : Option Op :=
  match instruction.opcode, instruction.operand with
  | 21, .none => some (.const32 (BitVec.ofInt 32 (-1)))
  | 31, .integer value =>
    if -128 <= value && value < 128 then some (.const32 (BitVec.ofInt 32 value)) else none
  | 32, .integer value =>
    if -(2^31) <= value && value < 2^31 then some (.const32 (BitVec.ofInt 32 value)) else none
  | 33, .integer value =>
    if -(2^63) <= value && value < 2^63 then some (.const64 (BitVec.ofInt 64 value)) else none
  | opcode, .none =>
    if 22 <= opcode && opcode <= 30 then some (.const32 (BitVec.ofNat 32 (opcode - 22))) else none
  | _, _ => none

/-- A covered opcode emits exactly the encoding its operand kinds imply. -/
def scalarOpMatches (instruction : RawInstruction) (stack : List ScalarKind) (emitted : Op) :
    Bool :=
  if instruction.opcode == 141 || arrayCovered instruction.opcode || arrayEmission emitted then
    arrayMatches instruction stack emitted
  else if instruction.opcode == 65054 then
    instruction.operand == .none && match emitted with | .nop => true | _ => false
  else if instruction.opcode == 20 then
    instruction.operand == .none && match emitted with | .memory .nullRef => true | _ => false
  else if instruction.opcode ∈ [44, 45, 57, 58] then
    match instruction.operand, stack, emitted with
    | .target target, value :: _, .brzero actual =>
      instruction.opcode ∈ [44, 57] && target == actual &&
        (numeric value || value ∈ [.reference, .nullObject])
    | .target target, value :: _, .brnonzero actual =>
      instruction.opcode ∈ [45, 58] && target == actual &&
        (numeric value || value ∈ [.reference, .nullObject])
    | _, _, _ => false
  else if 21 <= instruction.opcode && instruction.opcode <= 33 then
    match literal instruction, emitted with
    | some (.const32 expected), .const32 actual => expected == actual
    | some (.const64 expected), .const64 actual => expected == actual
    | _, _ => false
  else if compareBranch instruction.opcode then match instruction.operand, stack with
    | .target target, right :: left :: _ =>
        (compatibleBinary left right || referenceComparison instruction.opcode left right) &&
        !(mixedNative left right && unsignedBranch instruction.opcode) &&
        nativeWrapped left right (branchEncodingMatches instruction.opcode target) emitted
    | _, _ => false
  else if instruction.operand != .none then false
  else if instruction.opcode == 88 && (stack[1]? == some .reference) then
    match stack[0]?, emitted with
    | some kind, .memory (.add 1 true) => kind ∈ [.word32, .native]
    | _, _ => false
  else if instruction.opcode == 89 && (stack.drop 1).head? == some .reference then
    match stack.head?, emitted with
    | some kind, .sub => kind ∈ [.word32, .native, .reference]
    | _, _ => false
  else if scalarBinary instruction.opcode then match stack with
    | right :: left :: _ =>
        (compatibleBinary left right || referenceComparison instruction.opcode left right) &&
        nativeWrapped left right (scalarEncodingMatches instruction.opcode) emitted
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
private def scalarEmission : Op → Bool
  | .const32 _ | .const64 _ | .add | .sub | .mul | .divide .. | .band | .bor | .bxor | .shl
  | .shr | .shrUn | .neg | .bnot | .eq | .lt | .ltu | .gt | .gtu | .convI1 | .convI2 | .convI4
  | .convI8 | .convU1 | .convU2 | .convU4 | .convU8 | .convU | .checkedConvert ..
  | .checkedArithmetic .. | .nativeBinary _
  | .beq _ | .bge _ | .bgt _ | .ble _ | .blt _ | .bne _ | .bgeu _ | .bgtu _ | .bleu _
  | .bltu _ => true
  | _ => false

/-- Byte width of a non-aggregate `sizeof` operand on the admitted 64-bit target. -/
private def primitiveSize (type : TypeExpr) : Option Nat :=
  match typeStorage [] type with
  | some (.field kind) => primitiveFieldWidth kind
  | some .vector128 => some 16
  | some .vector256 => some 32
  | some .vector512 => some 64
  | _ => none

/-- Exactly `call Unsafe.SizeOf<T>()`. -/
private def unsafeSizeOf (site : CallSite) : Bool :=
  site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" &&
    site.name == "SizeOf" && !site.hasThis && site.returnsValue && site.parameterCount == 0 &&
    site.parameterTypes.isEmpty && site.returnType == .atom runtimeScope "System.Int32" &&
    site.target == .external (runtimeScope ++
      "::System.Int32 System.Runtime.CompilerServices.Unsafe::SizeOf()")

/-- A size constant has its primitive width; an aggregate size is bound by its layout use
    instead. -/
private def sizeConstant (instruction : RawInstruction) (bits : W32) : Bool :=
  let sized : TypeExpr → Bool
    | .aggregate .. => true
    | type => primitiveSize type == some bits.toNat
  match instruction.opcode, instruction.operand with
  | 65052, .type type => sized type
  | 40, .call site => unsafeSizeOf site && match site.typeArguments with
    | [type] => sized type
    | _ => false
  | _, _ => false

/-- Covered opcodes emit exactly their encoding. Elsewhere only a decided type test's word
    (bound by the feature check) or a size constant may emit a scalar operation. -/
def scalarEmissionMatches (role : Option FoldRole) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Op) : Bool :=
  if instruction.opcode == 77 && (stack.head?).any
      (fun kind => match kind with | .nativeMethodTable _ => true | _ => false) then
    match stack, emitted with
    | .nativeMethodTable signature :: _, .managed (.tableLoad actual) => signature == actual
    | _, _ => false
  else if instruction.opcode == 88 && (stack[1]?).any
      (fun kind => match kind with | .nativeMethodTable _ => true | _ => false) then
    match stack, emitted with
    | offset :: _ :: _, .managed .tableOffset => offset ∈ [.word32, .native]
    | _, _ => false
  else if let .managed operation := emitted then match operation, stack with
    | .address .., _ => instruction.opcode == 65030
    | .call .., _ => instruction.opcode == 41
    | .tableOffset, offset :: .nativeMethodTable _ :: _ =>
      instruction.opcode == 88 && offset ∈ [.word32, .native]
    | .tableLoad signature, .nativeMethodTable actual :: _ =>
      instruction.opcode == 77 && signature == actual
    | .tableAddress .., _ => false
    | .tableLength, .methodTable _ :: _ => instruction.opcode == 142
    | .tableElement signature, index :: .methodTable actual :: _ =>
      index ∈ [.word32, .native] && signature == actual &&
        (instruction.opcode == 151 || (instruction.opcode == 163 &&
          (match instruction.operand with
           | .type type => managedSignature type == some signature | _ => false)))
    | _, _ => false
  else if let some helper := unsafeReferenceHelper instruction then helper.matches emitted
  else if arrayEmission emitted then arrayMatches instruction stack emitted
  else if instruction.opcode == 20 && role ∈ [some .head, some .interior] then
    instruction.operand == .none && match emitted with | .nop => true | _ => false
  else if scalarCovered instruction.opcode then scalarOpMatches instruction stack emitted
  else !scalarEmission emitted || match role, emitted with
    | some (.result _), .const32 _ => true
    | _, .const32 bits => sizeConstant instruction bits
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
  | .atom _ name | .constructor _ name => some (signatureBytes name)
  | type@(.aggregate ..) => signatureBytes <$> spanElementName type
  -- Enum names cannot contain generic owner arguments.
  | .enum identity _ => (splitBytes (signatureBytes identity) [58, 58])[1]?
  | .parameter index => some (signatureBytes ("!!" ++ toString index))
  | .functionPointer .. | .signatureParameter .. => none
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
        (fun operation => operation == .spanPinnable || operation == .arrayData) then .reference
  else match site.target with
    | .managed _ => scalarType site.returnType
    | .external identity => externalResult site identity

/-- Exactly `newobj ReadOnlySpan<byte>(void*, int)`. -/
private def byteSpanConstructor (opcode : Nat) (site : CallSite) : Bool :=
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
private def spanCreateMatches (instruction : RawInstruction) (emitted : Op) : Bool :=
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

/-- Contextual callable kinds retain the independently derived native home identity. -/
private def dispatchScalar (context : NativeDispatchContext) (type : TypeExpr)
    (index : Option Nat := none) : ScalarKind :=
  match nativeDispatchStorage context type index with
  | some (.methodTable signature) => .nativeMethodTable signature
  | some (.methodPointer signature) => .methodPointer signature
  | _ => scalarType type

/-- The kind of argument `index`, counting `this` as argument 0. -/
private def argumentKind (raw : RawMethod) (context : NativeDispatchContext) (index : Nat) : Option ScalarKind :=
  if raw.hasThis && index == 0 then some .reference
  else dispatchScalar context <$> raw.parameters[index - (if raw.hasThis then 1 else 0)]?

/-- The kind an opcode with a fixed one-value push leaves on the stack. -/
private def pushedKind (raw : RawMethod) (context : NativeDispatchContext)
    (instruction : RawInstruction) : Option ScalarKind := do
  match argumentOperation instruction with
  | some (.load index) => argumentKind raw context index
  | _ =>
    -- `ldloc`.
    if instruction.opcode ∈ [6, 7, 8, 9, 17, 65036] then
      let index ← localIndex instruction
      return dispatchScalar context (← raw.locals[index]?) (some index)
    -- `ldarga`, `ldloca`, `ldflda` and `ldsflda`.
    else if instruction.opcode ∈ [18, 65037] then
      let index ← localIndex instruction
      let type ← raw.locals[index]?
      if (nativeDispatchStorage context type (some index)).isSome then none else
        return scalarType (.byref type)
    else if instruction.opcode ∈ [15, 65034] then
      match argumentOperation instruction with
      | some (.address index) =>
        if raw.hasThis && index == 0 then return .reference
        let type ← raw.parameters[index - (if raw.hasThis then 1 else 0)]?
        if (nativeDispatchStorage context type).isSome then none else
          return scalarType (.byref type)
      | _ => none
    else if instruction.opcode ∈ [124, 127] then some .reference
    -- `ldfld` and `ldsfld`, then `ldobj`.
    else if instruction.opcode == 123 || instruction.opcode == 126 then
      let .field _ _ type _ := instruction.operand | none
      return scalarType type
    else if instruction.opcode == 113 then
      let .type type := instruction.operand | none
      return scalarType type
    -- `ldind.i`, `ldind.i8`, then `ldind.i1` through `ldind.u4` and `sizeof`.
    else if instruction.opcode == 77 then some .native
    else if instruction.opcode == 76 then some .word64
    else if instruction.opcode ∈ [70, 71, 72, 73, 74, 75, 65052] then some .word32
    else some .other

/-- The stack kinds after `instruction`, or `none` if its operands have the wrong kinds. -/
def scalarTransfer (raw : RawMethod) (instruction : RawInstruction)
    (stack : List ScalarKind) (role : Option FoldRole := none)
    (context : NativeDispatchContext := nativeDispatchContext raw) : Option (List ScalarKind) := do
  let opcode := instruction.opcode
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
    if let offset :: .nativeMethodTable signature :: rest := stack then
      if offset ∈ [.word32, .native] then return .nativeMethodTable signature :: rest else none
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
    let element ← arrayElementType token
    let length :: tail := stack | none
    if !element.allocationSupported || length ∉ [.word32, .native] then none else
      return .array element :: tail
  if arrayCovered opcode then return (← arrayStep instruction stack).2
  if opcode == 20 then
    if instruction.operand == .none then return .nullObject :: stack else none
  if opcode ∈ [44, 45, 57, 58] then
    let value :: tail := stack | none
    if numeric value || value ∈ [.reference, .nullObject] then return tail else none
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
    if opcode ∈ [88, 89] && left == .reference && right ∈ [.word32, .native] then
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
    let type ← raw.locals[index]?
    let value :: tail := stack | none
    if storageCompatible value (dispatchScalar context type (some index)) then return tail else none
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
      if unsafePointerOffset instruction then [.word32, .reference] else
      if (opcode == 115 || opcode == 40) && (spanConstructor 115 site).isSome
      then [.word32, .reference] ++
        (if opcode == 40 then [scalarType (.byref site.declaringType)] else []) else
      site.parameterTypes.reverse.map scalarType ++
        (if opcode != 115 && site.hasThis then [scalarType (.byref site.declaringType)] else [])
    let inputs := if opcode == 115 && role == some .interior then
        stack.map (fun kind => if kind == .nullObject then .other else kind)
      else stack
    let pops := expected.length
    if !callParametersMatch site || pops > stack.length || !((inputs.take pops).zip expected).all (fun (value, home) =>
        value == home || (value == .nullObject &&
          (match home with | .array _ | .methodTable _ => true | _ => false))) ||
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
    else if pushes == 1 then return (← pushedKind raw context instruction) :: stack.drop pops
    else none

/-- A `stloc` of a 64-bit or native value into a 32-bit local, emitted as a store to that
    same local. The checked interpreter rejects that store, so the site needs no successor. -/
def scalarStoreFault (raw : RawMethod) (instruction : RawInstruction)
    (stack : List ScalarKind) (emitted : Op) : Bool :=
  ((do
    if instruction.opcode ∉ [10, 11, 12, 13, 19, 65038] then none else
    let index ← localIndex instruction
    let type ← raw.locals[index]?
    let value :: _ := stack | none
    return scalarType type == .word32 && value ∈ [.word64, .native] &&
      match emitted with
      | .setLocal actual _ => actual == index
      | _ => false) : Option Bool).getD false

/-- Whether the immediately preceding raw instruction is a readonly prefix. -/
private def followsReadOnly (raw : RawMethod) (pc : Nat) : Bool :=
  pc > 0 && (raw.code[pc - 1]?).any (fun instruction => instruction.opcode == 65054)

/-- A readonly prefix is inseparable from its element address, including branch entry. -/
private def readOnlySiteMatches (raw : RawMethod) (pc : Nat) (instruction : RawInstruction)
    (emitted : Op) : Bool :=
  let entered (target : Nat) := raw.code.any fun source => match source.operand with
    | .target destination => destination == target
    | .targets destinations => destinations.contains target
    | _ => false
  if instruction.opcode == 65054 then
    instruction.operand == .none &&
      (raw.code[pc + 1]?).any (fun next => next.opcode == 143) && !entered (pc + 1)
  else if instruction.opcode == 143 then
    match emitted with
    | .memory (.arrayAddress _ writable) =>
      writable == !followsReadOnly raw pc && (!followsReadOnly raw pc || !entered pc)
    | _ => false
  else true

/-- One pc of the certificate: an unreachable pc must emit a hole; a reachable one must
    agree with the feature stack depth, emit the right encoding, and give every successor,
    which must be reachable, exactly the resulting stack kinds. -/
private def checkScalarSite (raw : RawMethod) (context : NativeDispatchContext)
    (successor : List ScalarKind → Nat → Bool) :
    (RawInstruction × Option FoldRole) × Nat → Option FeatureState → Option (List ScalarKind) →
      Op → Bool
  | _, none, none, .unsupported _ => true
  | ((instruction, role), pc), some feature, some stack, emitted =>
    stack.length == feature.stack.length && stack.length <= raw.maxStack &&
      (match role with
        | some (.spanConstructor index constructor) => match emitted with
          | .initializeSpanLocal actual operation => index == actual && spanConstructorMatches constructor operation
          | _ => false
        | _ => spanCreateMatches instruction emitted && spanCallMatches instruction emitted) &&
      readOnlySiteMatches raw pc instruction emitted &&
      scalarEmissionMatches role instruction stack emitted &&
      (scalarStoreFault raw instruction stack emitted ||
      match scalarTransfer raw instruction stack role context, featureSuccessors pc instruction feature with
      | some after, some successors =>
        successors.all (successor after)
      | _, _ => false)
  | _, _, _, _ => false

/-- The scalar certificate covers exactly the feature-reachable pcs, starts with an empty
    stack, and passes every site check. -/
def ScalarFlowValid (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Op) : Prop :=
  let context := nativeDispatchContext raw
  raw.code.length = features.length ∧ raw.code.length = certificate.length ∧
    raw.code.length = code.length ∧
  certificate[0]? = some (some []) ∧
  all3Flow (fun lookup instruction (feature, stack) emitted =>
      checkScalarSite raw context (fun after target => match lookup target with
        | some (some _, incoming) => incoming == some after
        | _ => false) instruction feature stack emitted)
    (.ofList (features.zip certificate)) 0
    (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx (features.zip certificate) code = true

instance (raw : RawMethod) (features : FeatureCertificate) (certificate : ScalarCertificate)
    (code : List Op) : Decidable (ScalarFlowValid raw features certificate code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Pairing feature and scalar states preserves both the reachability and exact stack
    check, including targets missing from either certificate. -/
theorem scalarSuccessor_zip (features : FeatureCertificate) (certificate : ScalarCertificate)
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

/-- Streaming scalar validation preserves all list-indexed site checks and lengths. -/
theorem ScalarFlowValid_iff_list (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Op) :
    ScalarFlowValid raw features certificate code ↔
      raw.code.length = features.length ∧ raw.code.length = certificate.length ∧
      raw.code.length = code.length ∧ certificate[0]? = some (some []) ∧
      all3 (fun (instruction, feature) stack emitted =>
          checkScalarSite raw (nativeDispatchContext raw) (fun after target => match features[target]? with
            | some (some _) => certificate[target]? == some (some after)
            | _ => false)
            instruction feature stack emitted)
        ((raw.code.zip (foldRoles raw.locals raw.code)).zipIdx.zip features) certificate code =
        true := by
  dsimp only [ScalarFlowValid]
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm]
  simp only [scalarSuccessor_zip]
  by_cases featureLength : raw.code.length = features.length
  · by_cases scalarLength : raw.code.length = certificate.length
    · rw [all3_zip_states _ _ _ _ _ (featureLength.symm.trans scalarLength)]
      simp only [List.length_zipIdx, List.length_zip]
      exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_eq featureLength)
    · simp [scalarLength]
  · simp [featureLength]

#print axioms ScalarFlowValid_iff_list

/-- At every reachable pc the emitted instruction is the scalar encoding the raw one implies. -/
theorem ScalarFlowValid.instruction_checked {raw : RawMethod} {features : FeatureCertificate}
    {certificate : ScalarCertificate} {code : List Op}
    (valid : ScalarFlowValid raw features certificate code)
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole} {feature : FeatureState}
    {stack : List ScalarKind} {emitted : Op}
    (rawAt : raw.code[pc]? = some instruction)
    (roleAt : (foldRoles raw.locals raw.code)[pc]? = some role)
    (featureAt : features[pc]? = some (some feature))
    (stackAt : certificate[pc]? = some (some stack)) (emittedAt : code[pc]? = some emitted) :
    scalarEmissionMatches role instruction stack emitted = true := by
  have pairAt : (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx[pc]? =
      some ((instruction, role), pc) := by
    simp [List.getElem?_zipIdx, List.getElem?_zip_eq_some, rawAt, roleAt]
  have statesAt : (features.zip certificate)[pc]? = some (some feature, some stack) :=
    List.getElem?_zip_eq_some.mpr ⟨featureAt, stackAt⟩
  have sites := valid.2.2.2.2
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm] at sites
  have checked := all3_at sites pairAt statesAt emittedAt
  simp only [checkScalarSite, Bool.and_eq_true] at checked
  exact checked.1.2

#print axioms ScalarFlowValid.instruction_checked

end CIL.Extraction
