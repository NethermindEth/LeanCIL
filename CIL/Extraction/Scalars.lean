import CIL.Extraction.Features

namespace CIL.Extraction

inductive ScalarKind where
  | word32 | word64 | native | reference | other
  deriving DecidableEq, Repr

abbrev ScalarCertificate := List (Option (List ScalarKind))

def scalarType : TypeExpr → ScalarKind
  | .enum _ underlying => scalarType underlying
  | .byref _ => .reference
  | .atom scope name =>
    if scope != runtimeScope then .other
    else if name ∈ ["System.IntPtr", "System.UIntPtr"] then .native
    else if name ∈ ["System.Int64", "System.UInt64"] then .word64
    else if name ∈ ["System.Boolean", "System.Char", "System.SByte", "System.Byte", "System.Int16",
      "System.UInt16", "System.Int32", "System.UInt32"] then .word32 else .other
  | _ => .other

private def numeric (kind : ScalarKind) : Bool := kind ∈ [.word32, .word64, .native]

private def storageCompatible (value home : ScalarKind) : Bool :=
  value == home || value ∈ [.word64, .native] && home ∈ [.word64, .native]

private def scalarBinary : Nat → Bool
  | 88 | 89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 214 | 215 | 216 | 217 | 218 | 219
  | 65025 | 65026 | 65027 | 65028 | 65029 => true
  | _ => false

private def comparison (opcode : Nat) : Bool := 65025 <= opcode && opcode <= 65029

private def conversion : Nat → Bool
  | 103 | 104 | 105 | 106 | 109 | 110 | 130 | 131 | 132 | 133 | 134 | 135 | 136 | 137 | 138 | 139
  | 179 | 180 | 181 | 182 | 183 | 184 | 185 | 186 | 209 | 210 | 211 | 212 | 213 | 224 => true
  | _ => false

private def compareBranch (opcode : Nat) : Bool := (46 <= opcode && opcode <= 55) || (59 <= opcode && opcode <= 68)

/-- `bne.un` and the unsigned orderings; CoreCLR widens a mixed int32 operand by provenance. -/
private def unsignedBranch (opcode : Nat) : Bool := (51 <= opcode && opcode <= 55) || (64 <= opcode && opcode <= 68)

def scalarCovered (opcode : Nat) : Bool :=
  (21 <= opcode && opcode <= 33) || scalarBinary opcode || conversion opcode || compareBranch opcode ||
    opcode ∈ [98, 99, 100, 101, 102]

private def scalarEncodingMatches (opcode : Nat) (emitted : Op) : Bool :=
  match opcode, emitted with
  | 88, .add | 89, .sub | 90, .mul => true
  | 91, .divide true false | 92, .divide false false
  | 93, .divide true true | 94, .divide false true => true
  | 95, .band | 96, .bor | 97, .bxor | 98, .shl | 99, .shr | 100, .shrUn
  | 101, .neg | 102, .bnot => true
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
  | 214, .checkedArithmetic .add true | 215, .checkedArithmetic .add false
  | 216, .checkedArithmetic .mul true | 217, .checkedArithmetic .mul false
  | 218, .checkedArithmetic .sub true | 219, .checkedArithmetic .sub false => true
  | 65025, .eq | 65026, .gt | 65027, .gtu | 65028, .lt | 65029, .ltu => true
  | _, _ => false

private def branchEncodingMatches (opcode target : Nat) (emitted : Op) : Bool :=
  match (if opcode <= 55 then opcode - 46 else opcode - 59), emitted with
  | 0, .beq actual | 1, .bge actual | 2, .bgt actual | 3, .ble actual | 4, .blt actual
  | 5, .bne actual | 6, .bgeu actual | 7, .bgtu actual | 8, .bleu actual | 9, .bltu actual => actual == target
  | _, _ => false

private def mixedNative (left right : ScalarKind) : Bool :=
  (left == .native && right == .word32) || (left == .word32 && right == .native)

private def compatibleBinary (left right : ScalarKind) : Bool :=
  numeric left && numeric right && (left == right || mixedNative left right)

/-- Mixed native/int32 operands require exactly one `nativeBinary` wrapper; any other pair forbids it. -/
private def nativeWrapped (left right : ScalarKind) (encoding : Op → Bool) : Op → Bool
  | .nativeBinary operation => mixedNative left right && encoding operation
  | operation => !mixedNative left right && encoding operation

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

def scalarOpMatches (instruction : RawInstruction) (stack : List ScalarKind) (emitted : Op) : Bool :=
  if 21 <= instruction.opcode && instruction.opcode <= 33 then
    match literal instruction, emitted with
    | some (.const32 expected), .const32 actual => expected == actual
    | some (.const64 expected), .const64 actual => expected == actual
    | _, _ => false
  else if compareBranch instruction.opcode then match instruction.operand, stack with
    | .target target, right :: left :: _ => compatibleBinary left right &&
        !(mixedNative left right && unsignedBranch instruction.opcode) &&
        nativeWrapped left right (branchEncodingMatches instruction.opcode target) emitted
    | _, _ => false
  else if instruction.operand != .none then false
  else if scalarBinary instruction.opcode then match stack with
    | right :: left :: _ => compatibleBinary left right &&
        nativeWrapped left right (scalarEncodingMatches instruction.opcode) emitted
    | _ => false
  else if instruction.opcode ∈ [98, 99, 100] then match stack with
    | right :: left :: _ => numeric left && right ∈ [.word32, .native] && scalarEncodingMatches instruction.opcode emitted
    | _ => false
  else match stack with
    | value :: _ => numeric value && scalarEncodingMatches instruction.opcode emitted
    | _ => false

/-- Operations computing a scalar from operands or a literal; only a covered encoding may emit one. -/
private def scalarEmission : Op → Bool
  | .const32 _ | .const64 _ | .add | .sub | .mul | .divide .. | .band | .bor | .bxor | .shl | .shr | .shrUn
  | .neg | .bnot | .eq | .lt | .ltu | .gt | .gtu | .convI1 | .convI2 | .convI4 | .convI8 | .convU1 | .convU2
  | .convU4 | .convU8 | .convU | .checkedConvert .. | .checkedArithmetic .. | .nativeBinary _
  | .beq _ | .bge _ | .bgt _ | .ble _ | .blt _ | .bne _ | .bgeu _ | .bgtu _ | .bleu _ | .bltu _ => true
  | _ => false

/-- Byte width of a non-aggregate `sizeof` operand on the admitted 64-bit target. -/
private def primitiveSize (type : TypeExpr) : Option Nat :=
  match typeStorage [] type with
  | some (.field kind) => match kind with
    | .signed8 | .unsigned8 | .boolean => some 1
    | .signed16 | .unsigned16 | .character => some 2
    | .signed32 | .unsigned32 => some 4
    | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some 8
    | _ => none
  | some .vector128 => some 16
  | some .vector256 => some 32
  | _ => none

private def unsafeSizeOf (site : CallSite) : Bool :=
  site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" && site.name == "SizeOf" &&
    !site.hasThis && site.returnsValue && site.parameterCount == 0 && site.parameterTypes.isEmpty &&
    site.returnType == .atom runtimeScope "System.Int32" &&
    site.target == .external (runtimeScope ++ "::System.Int32 System.Runtime.CompilerServices.Unsafe::SizeOf()")

/-- A size constant has its primitive width; an aggregate size is bound by its layout use instead. -/
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
  if scalarCovered instruction.opcode then scalarOpMatches instruction stack emitted
  else !scalarEmission emitted || match role, emitted with
    | some (.result _), .const32 _ => true
    | _, .const32 bits => sizeConstant instruction bits
    | _, _ => false

private def resultKind (opcode : Nat) : ScalarKind :=
  if opcode ∈ [211, 212, 213, 138, 139, 224] then .native
  else if opcode ∈ [106, 110, 133, 137, 185, 186] then .word64 else .word32

private def signatureBytes (text : String) : List UInt8 := text.toByteArray.data.toList

private def splitTextBytes (separator : List UInt8) : Nat → List UInt8 → List UInt8 → List (List UInt8)
  | 0, current, tail => [current.reverse ++ tail]
  | _ + 1, current, [] => [current.reverse]
  | remaining + 1, current, text@(c :: tail) =>
    if separator.isPrefixOf text then
      current.reverse :: splitTextBytes separator remaining [] (text.drop separator.length)
    else splitTextBytes separator remaining (c :: current) tail

private def splitBytes (text separator : List UInt8) : List (List UInt8) :=
  splitTextBytes separator (text.length + 1) [] text

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

private def scalarTypeBytes : TypeExpr → Option (List UInt8)
  | .void => some (signatureBytes "System.Void")
  | .atom _ name | .constructor _ name => some (signatureBytes name)
  | .aggregate identity _ | .enum identity _ => (splitBytes (signatureBytes identity) [58, 58])[1]?
  | .parameter index => some (signatureBytes ("!!" ++ toString index))
  | .byref element => (· ++ [38]) <$> scalarTypeBytes element
  | .pointer element => (· ++ [42]) <$> scalarTypeBytes element
  | .apply constructor argument => do
    let name ← scalarTypeBytes constructor
    let element ← scalarTypeBytes argument
    return if name.reverse.head? == some 62 then name.take (name.length - 1) ++ [44] ++ element ++ [62]
      else name ++ [60] ++ element ++ [62]

private def parameterTokens (depth : Nat) (current : List UInt8) : List UInt8 → Option (List (List UInt8))
  | [] => if depth != 0 then none else if current.isEmpty then some [] else some [current.reverse]
  | 44 :: [] => none
  | 44 :: tail =>
    if depth == 0 then
      if current.isEmpty then none else (current.reverse :: ·) <$> parameterTokens 0 [] tail
    else parameterTokens depth (44 :: current) tail
  | 60 :: tail => parameterTokens (depth + 1) (60 :: current) tail
  | 62 :: tail => if depth == 0 then none else parameterTokens (depth - 1) (62 :: current) tail
  | c :: tail => parameterTokens depth (c :: current) tail

private def parameterTypeMatches (token : List UInt8) (type : TypeExpr) : Bool :=
  if scalarTypeBytes type == some token then true
  else match type with
    | .byref element => [33].isPrefixOf token && ![33, 33].isPrefixOf token &&
        token.reverse.head? == some 38 && scalarType element == .other
    | .pointer element => [33].isPrefixOf token && ![33, 33].isPrefixOf token &&
        token.reverse.head? == some 42 && scalarType element == .other
    | _ => [33].isPrefixOf token && ![33, 33].isPrefixOf token && scalarType type == .other

private def normalizeExternalIdentity (site : CallSite) (identity : List UInt8) : Option (List UInt8) := do
  let normalized ← site.typeArguments.zipIdx.reverse.foldlM (fun text (type, index) => do
    let name ← scalarTypeBytes type
    return replaceBytes text (signatureBytes ("!!" ++ toString index)) name) identity
  let owner ← scalarTypeBytes site.declaringType
  match splitBytes owner [60] with
  | [] | [_] => return normalized
  | _ :: tail =>
    let suffix := joinBytes [60] tail
    if suffix.reverse.head? != some 62 then none else
      let arguments ← parameterTokens 0 [] (suffix.take (suffix.length - 1))
      return arguments.zipIdx.reverse.foldl (fun text (name, index) =>
        replaceBytes text (signatureBytes ("!" ++ toString index)) name) normalized

private def balancedParentheses : Nat → List UInt8 → Bool
  | depth, [] => depth == 0
  | depth, 40 :: tail => balancedParentheses (depth + 1) tail
  | 0, 41 :: _ => false
  | depth + 1, 41 :: tail => balancedParentheses depth tail
  | depth, _ :: tail => balancedParentheses depth tail

private def externalParametersMatch (site : CallSite) (identity : String) : Bool :=
  ((do
    let original := identity.toByteArray.data.toList
    if !balancedParentheses 0 original then none else
    let head :: rest := splitBytes original [40] | none
    let _ := head
    let rawTail ← rest.getLast?
    let tail ← normalizeExternalIdentity site rawTail
    if !balancedParentheses 1 tail || tail.reverse.head? != some 41 then none else
      let tokens ← parameterTokens 0 [] (tail.take (tail.length - 1))
      return tokens.length == site.parameterTypes.length &&
        (tokens.zip site.parameterTypes).all fun (token, type) => parameterTypeMatches token type) : Option Bool).getD false

private def callParametersMatch (site : CallSite) : Bool :=
  site.parameterCount == site.parameterTypes.length && match site.target with
    | .managed _ => true
    | .external identity => externalParametersMatch site identity

private def externalResult (site : CallSite) (identity : String) : ScalarKind :=
  if scalarType site.returnType == .other then .other else
  match normalizeExternalIdentity site identity.toByteArray.data.toList with
  | none => .other
  | some normalized =>
    let signature := (splitBytes normalized [58, 58])[1]?.getD []
    match site.returnType with
    | .atom _ name => if (signatureBytes name ++ [32]).isPrefixOf signature then scalarType site.returnType else .other
    | .byref _ =>
      if ((splitBytes signature [32])[0]?.getD []).reverse.head? == some 38 then .reference else .other
    | .enum identity _ =>
      let name := (splitBytes (signatureBytes identity) [58, 58])[1]?.getD []
      if !name.isEmpty && (name ++ [32]).isPrefixOf signature then scalarType site.returnType else .other
    | _ => .other

private def callResult (site : CallSite) : ScalarKind :=
  match site.target with
  | .managed _ => scalarType site.returnType
  | .external identity => externalResult site identity

private def byteSpanConstructor (opcode : Nat) (site : CallSite) : Bool :=
  opcode == 115 && site.name == ".ctor" && site.hasThis && !site.returnsValue &&
    site.typeArguments.isEmpty && site.parameterCount == 2 && site.returnType == .void &&
    site.declaringType == .apply (.constructor runtimeScope "System.ReadOnlySpan`1") (.atom runtimeScope "System.Byte") &&
    site.parameterTypes == [.pointer .void, .atom runtimeScope "System.Int32"] &&
    site.target == .external (runtimeScope ++ "::System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)")

private def spanCreateMatches (instruction : RawInstruction) (emitted : Op) : Bool :=
  let modeled := match instruction.operand with
    | .call site => byteSpanConstructor instruction.opcode site
    | _ => false
  match emitted with
  | .memory .spanCreate => modeled
  | _ => !modeled

private def argumentKind (raw : RawMethod) (index : Nat) : Option ScalarKind :=
  if raw.hasThis && index == 0 then some .reference
  else scalarType <$> raw.parameters[index - (if raw.hasThis then 1 else 0)]?

private def pushedKind (raw : RawMethod) (instruction : RawInstruction) : Option ScalarKind := do
  match argumentOperation instruction with
  | some (.load index) => argumentKind raw index
  | _ =>
    if instruction.opcode ∈ [6, 7, 8, 9, 17, 65036] then
      scalarType <$> raw.locals[← localIndex instruction]?
    else if instruction.opcode ∈ [15, 18, 124, 127, 65034, 65037] then some .reference
    else if instruction.opcode == 123 || instruction.opcode == 126 then
      let .field _ _ type _ := instruction.operand | none
      return scalarType type
    else if instruction.opcode == 113 then
      let .type type := instruction.operand | none
      return scalarType type
    else if instruction.opcode == 77 then some .native
    else if instruction.opcode == 76 then some .word64
    else if instruction.opcode ∈ [70, 71, 72, 73, 74, 75, 65052] then some .word32
    else some .other

def scalarTransfer (raw : RawMethod) (instruction : RawInstruction)
    (stack : List ScalarKind) : Option (List ScalarKind) := do
  let opcode := instruction.opcode
  if 21 <= opcode && opcode <= 33 then
    let _ ← literal instruction
    return (if opcode == 33 then .word64 else .word32) :: stack
  if scalarBinary opcode then
    let right :: left :: tail := stack | none
    if !compatibleBinary left right then none else
      return (if comparison opcode then .word32 else if mixedNative left right then .native else left) :: tail
  if opcode ∈ [98, 99, 100] then
    let right :: left :: tail := stack | none
    if !numeric left || right ∉ [.word32, .native] then none else return left :: tail
  if opcode == 101 || opcode == 102 || conversion opcode then
    let value :: tail := stack | none
    if !numeric value then none else
      return (if conversion opcode then resultKind opcode else value) :: tail
  if opcode ∈ [10, 11, 12, 13, 19, 65038] then
    let index ← localIndex instruction
    let type ← raw.locals[index]?
    let value :: tail := stack | none
    if storageCompatible value (scalarType type) then return tail else none
  if let some (.store index) := argumentOperation instruction then
    let expected ← argumentKind raw index
    let value :: tail := stack | none
    if storageCompatible value expected then return tail else none
  if opcode == 37 then
    let value :: tail := stack | none
    return value :: value :: tail
  if opcode == 40 || opcode == 115 then
    let .call site := instruction.operand | none
    let expected := if byteSpanConstructor opcode site then [.word32, .reference] else
      site.parameterTypes.reverse.map scalarType ++ (if opcode == 40 && site.hasThis then [.reference] else [])
    let pops := expected.length
    if !callParametersMatch site || pops > stack.length || stack.take pops != expected ||
        site.returnsValue != (site.returnType != .void) then none else
      return (if opcode == 115 then [ScalarKind.other] else if site.returnsValue then [callResult site] else []) ++ stack.drop pops
  if opcode == 42 then
    if raw.returnType == .void then
      if stack.isEmpty then return [] else none
    else match stack with
      | [value] => if storageCompatible value (scalarType raw.returnType) then return [] else none
      | _ => none
  let (pops, pushes) ← rawStackEffect opcode
  if pops > stack.length then none else
    if pushes == 0 then return stack.drop pops
    else if pushes == 1 then return (← pushedKind raw instruction) :: stack.drop pops
    else none

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

private def checkScalarSite (raw : RawMethod) (features : FeatureCertificate) (certificate : ScalarCertificate) :
    (RawInstruction × Option FoldRole) × Nat → Option FeatureState → Option (List ScalarKind) → Op → Bool
  | _, none, none, .unsupported _ => true
  | ((instruction, role), pc), some feature, some stack, emitted =>
    stack.length == feature.stack.length && stack.length <= raw.maxStack &&
      spanCreateMatches instruction emitted && scalarEmissionMatches role instruction stack emitted &&
      (scalarStoreFault raw instruction stack emitted ||
      match scalarTransfer raw instruction stack, featureSuccessors pc instruction feature with
      | some after, some successors =>
        successors.all fun target => match features[target]? with
          | some (some _) => certificate[target]? == some (some after)
          | _ => false
      | _, _ => false)
  | _, _, _, _ => false

def ScalarFlowValid (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Op) : Prop :=
  raw.code.length = features.length ∧ raw.code.length = certificate.length ∧ raw.code.length = code.length ∧
  certificate[0]? = some (some []) ∧
  all3 (fun (instruction, feature) stack emitted => checkScalarSite raw features certificate instruction feature stack emitted)
    ((raw.code.zip (foldRoles raw.locals raw.code)).zipIdx.zip features) certificate code = true

instance (raw : RawMethod) (features : FeatureCertificate) (certificate : ScalarCertificate) (code : List Op) :
    Decidable (ScalarFlowValid raw features certificate code) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem ScalarFlowValid.instruction_checked {raw : RawMethod} {features : FeatureCertificate}
    {certificate : ScalarCertificate} {code : List Op}
    (valid : ScalarFlowValid raw features certificate code)
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole} {feature : FeatureState}
    {stack : List ScalarKind} {emitted : Op}
    (rawAt : raw.code[pc]? = some instruction) (roleAt : (foldRoles raw.locals raw.code)[pc]? = some role)
    (featureAt : features[pc]? = some (some feature))
    (stackAt : certificate[pc]? = some (some stack)) (emittedAt : code[pc]? = some emitted) :
    scalarEmissionMatches role instruction stack emitted = true := by
  have pairAt : ((raw.code.zip (foldRoles raw.locals raw.code)).zipIdx.zip features)[pc]? =
      some (((instruction, role), pc), some feature) := by
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨by simp [List.getElem?_zipIdx, List.getElem?_zip_eq_some, rawAt, roleAt], featureAt⟩
  have checked := all3_at valid.2.2.2.2 pairAt stackAt emittedAt
  simp only [checkScalarSite, Bool.and_eq_true] at checked
  exact checked.1.2

#print axioms ScalarFlowValid.instruction_checked

end CIL.Extraction
