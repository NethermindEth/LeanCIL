import CIL.Extraction.MetadataBytes

/-!
# Signature blobs

Method, field, local-variable, type and method-instantiation signatures of ECMA-335 II.23.2,
decoded from the bytes of a `#Blob` entry. Type tokens stay tokens of the slice the blob
comes from; `MetadataResolution` gives them names. Forms the model has no place for are refused
with the offset and the element byte: general arrays, `typedref`, the vararg sentinel,
pinned locals, vararg calling conventions and trailing bytes.

Recursion is on a fuel equal to the blob length, which bounds the node count since every node
takes at least one byte.
-/

namespace CIL.Extraction

mutual

/-- A signature type, with type tokens as the blob writes them. -/
inductive SigType where
  /-- An element type of II.23.1.16 that names no token: `void`, the integers, `string`,
      `object` and the native integers. -/
  | primitive (code : Nat)
  /-- A `CLASS` or `VALUETYPE` element with the token of its `TypeDefOrRef` encoding. -/
  | named (valueType : Bool) (token : Nat)
  | var (index : Nat)
  | mvar (index : Nat)
  | byref (element : SigType)
  | pointer (element : SigType)
  | szarray (element : SigType)
  | genericInst (valueType : Bool) (token : Nat) (arguments : SigList)
  | functionPointer (convention : Nat) (result : SigType) (parameters : SigList)
  | modified (required : Bool) (modifier : Nat) (element : SigType)
  deriving DecidableEq, Repr

/-- A list of signature types, as a chain so that the types derive decidable equality. -/
inductive SigList where
  | nil
  | cons (head : SigType) (tail : SigList)
  deriving DecidableEq, Repr

end

/-- The types of a chain, in order. -/
def SigList.toList : SigList → List SigType
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- A method signature: calling convention byte, generic arity, result and parameters. -/
structure MethodSig where
  convention : Nat
  genericArity : Nat
  result : SigType
  parameters : List SigType
  deriving DecidableEq, Repr

/-- The element type bytes that name a type without a token. -/
def primitiveCodes : List Nat :=
  [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x18, 0x19,
   0x1C]

/-- The calling-convention flag of a method with a `this` argument. -/
def hasThisFlag : Nat := 0x20

/-- The calling-convention flag of a method whose `this` argument is explicit. -/
def explicitThisFlag : Nat := 0x40

/-- The calling-convention flag of a generic method, which is followed by its arity. -/
def genericFlag : Nat := 0x10

/-- The offset in the blob of the byte at the front of the remaining bytes. -/
private def offsetOf (total : Nat) (rest : List Nat) : Nat := total - rest.length

/-- A compressed unsigned integer, or a truncated-signature error. -/
private def compressed (total : Nat) (bytes : List Nat) :
    Except MetadataError (Nat × List Nat) :=
  match decodeCompressed bytes with
  | some result => .ok result
  | none => .error (.truncatedSignature (offsetOf total bytes))

/-- The token of a `TypeDefOrRef` coded index at the front of the bytes. -/
private def typeToken (total : Nat) (bytes : List Nat) :
    Except MetadataError (Nat × List Nat) := do
  let (value, rest) ← compressed total bytes
  .ok (← decodeCoded typeDefOrRefTags 2 value, rest)

/-- The calling-convention byte of a method signature. Its kind must be a managed or unmanaged
    default (0 to 4), and the generic flag is allowed only where `generic` says so. -/
def callingConvention (total : Nat) (generic : Bool) :
    List Nat → Except MetadataError (Nat × List Nat)
  | [] => .error (.truncatedSignature total)
  | convention :: rest =>
    if convention % 0x10 > 4 || convention ≥ 0x80 ||
        (!generic && convention / genericFlag % 2 == 1) then
      .error (.unsupportedSignature (offsetOf total rest - 1) convention)
    else .ok (convention, rest)

mutual

/-- Decode one type at the front of the bytes, with the bytes after it. -/
def decodeType (total : Nat) : Nat → List Nat → Except MetadataError (SigType × List Nat)
  | 0, rest => .error (.unsupportedSignature (offsetOf total rest) 0)
  | _ + 1, [] => .error (.truncatedSignature total)
  | fuel + 1, first :: rest =>
    if primitiveCodes.contains first then .ok (.primitive first, rest)
    else if first == 0x0F then do
      let (element, tail) ← decodeType total fuel rest
      .ok (.pointer element, tail)
    else if first == 0x10 then do
      let (element, tail) ← decodeType total fuel rest
      .ok (.byref element, tail)
    else if first == 0x1D then do
      let (element, tail) ← decodeType total fuel rest
      .ok (.szarray element, tail)
    else if first == 0x11 || first == 0x12 then do
      let (token, tail) ← typeToken total rest
      .ok (.named (first == 0x11) token, tail)
    else if first == 0x13 || first == 0x1E then do
      let (index, tail) ← compressed total rest
      .ok (if first == 0x13 then .var index else .mvar index, tail)
    else if first == 0x1F || first == 0x20 then do
      let (modifier, afterModifier) ← typeToken total rest
      let (element, tail) ← decodeType total fuel afterModifier
      .ok (.modified (first == 0x1F) modifier element, tail)
    else if first == 0x15 then
      match rest with
      | kind :: afterKind =>
        if kind != 0x11 && kind != 0x12 then
          .error (.unsupportedSignature (offsetOf total rest) kind)
        else do
          let (token, afterToken) ← typeToken total afterKind
          let (count, afterCount) ← compressed total afterToken
          let (arguments, tail) ← decodeTypes total fuel count afterCount
          .ok (.genericInst (kind == 0x11) token arguments, tail)
      | [] => .error (.truncatedSignature total)
    else if first == 0x1B then do
      let (convention, afterConvention) ← callingConvention total false rest
      let (count, afterCount) ← compressed total afterConvention
      let (result, afterResult) ← decodeType total fuel afterCount
      let (parameters, tail) ← decodeTypes total fuel count afterResult
      .ok (.functionPointer convention result parameters, tail)
    else .error (.unsupportedSignature (offsetOf total (first :: rest)) first)

/-- Decode `count` types in a row. -/
def decodeTypes (total : Nat) : Nat → Nat → List Nat →
    Except MetadataError (SigList × List Nat)
  | _, 0, rest => .ok (.nil, rest)
  | 0, _ + 1, rest => .error (.unsupportedSignature (offsetOf total rest) 0)
  | fuel + 1, count + 1, rest => do
    let (head, afterHead) ← decodeType total fuel rest
    let (tail, remaining) ← decodeTypes total fuel count afterHead
    .ok (.cons head tail, remaining)

end

/-- A method signature: the convention, the generic arity when the generic flag is set, the
    parameter count, the result and the parameters. Nothing may follow the last parameter. -/
def decodeMethodSig (blob : List Nat) : Except MetadataError MethodSig := do
  let total := blob.length
  let (convention, afterConvention) ← callingConvention total true blob
  let (arity, afterArity) ←
    if convention / genericFlag % 2 == 1 then compressed total afterConvention
    else pure (0, afterConvention)
  let (count, afterCount) ← compressed total afterArity
  let (result, afterResult) ← decodeType total total afterCount
  let (parameters, rest) ← decodeTypes total total count afterResult
  if rest.isEmpty then
    .ok { convention, genericArity := arity, result, parameters := parameters.toList }
  else .error (.unsupportedSignature (offsetOf total rest) 0x100)

/-- Nothing may follow a decoded signature. -/
private def finished {α : Type} (total : Nat) (value : α) (rest : List Nat) :
    Except MetadataError α :=
  if rest.isEmpty then .ok value else .error (.unsupportedSignature (offsetOf total rest) 0x100)

/-- A field signature: `FIELD` and then the field's type. -/
def decodeFieldSig (blob : List Nat) : Except MetadataError SigType :=
  match blob with
  | 0x06 :: rest => do
    let (type, tail) ← decodeType blob.length blob.length rest
    finished blob.length type tail
  | first :: _ => .error (.unsupportedSignature 0 first)
  | [] => .error (.truncatedSignature 0)

/-- A local-variable signature: `LOCAL_SIG`, the count and one type per local. A pinned local
    (`0x45`) is refused as an unsupported element. -/
def decodeLocalSig (blob : List Nat) : Except MetadataError (List SigType) :=
  match blob with
  | 0x07 :: rest => do
    let total := blob.length
    let (count, afterCount) ← compressed total rest
    let (types, tail) ← decodeTypes total total count afterCount
    finished total types.toList tail
  | first :: _ => .error (.unsupportedSignature 0 first)
  | [] => .error (.truncatedSignature 0)

/-- A `TypeSpec` blob: one type. -/
def decodeTypeSpec (blob : List Nat) : Except MetadataError SigType := do
  let (type, tail) ← decodeType blob.length blob.length blob
  finished blob.length type tail

/-- A `MethodSpec` blob: `GENERICINST`, the count and the type arguments. -/
def decodeMethodSpec (blob : List Nat) : Except MetadataError (List SigType) :=
  match blob with
  | 0x0A :: rest => do
    let total := blob.length
    let (count, afterCount) ← compressed total rest
    let (types, tail) ← decodeTypes total total count afterCount
    finished total types.toList tail
  | first :: _ => .error (.unsupportedSignature 0 first)
  | [] => .error (.truncatedSignature 0)

end CIL.Extraction
