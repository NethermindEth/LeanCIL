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
    if scope != "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" then .other
    else if name ∈ ["System.IntPtr", "System.UIntPtr"] then .native
    else if name ∈ ["System.Int64", "System.UInt64"] then .word64
    else if name ∈ ["System.Boolean", "System.Char", "System.SByte", "System.Byte", "System.Int16",
      "System.UInt16", "System.Int32", "System.UInt32"] then .word32 else .other
  | _ => .other

private def numeric (kind : ScalarKind) : Bool := kind ∈ [.word32, .word64, .native]

private def scalarBinary : Nat → Bool
  | 88 | 89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 214 | 215 | 216 | 217 | 218 | 219
  | 65025 | 65026 | 65027 | 65028 | 65029 => true
  | _ => false

private def comparison (opcode : Nat) : Bool := 65025 <= opcode && opcode <= 65029

private def conversion : Nat → Bool
  | 103 | 104 | 105 | 106 | 109 | 110 | 130 | 131 | 132 | 133 | 134 | 135 | 136 | 137 | 138 | 139
  | 179 | 180 | 181 | 182 | 183 | 184 | 185 | 186 | 209 | 210 | 211 | 212 | 213 | 224 => true
  | _ => false

def scalarCovered (opcode : Nat) : Bool :=
  (21 <= opcode && opcode <= 33) || scalarBinary opcode || conversion opcode ||
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

private def mixedNative (left right : ScalarKind) : Bool :=
  (left == .native && right == .word32) || (left == .word32 && right == .native)

private def compatibleBinary (left right : ScalarKind) : Bool :=
  numeric left && numeric right && (left == right || mixedNative left right)

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
  else if instruction.operand != .none then false
  else if scalarBinary instruction.opcode then match stack with
    | right :: left :: _ => compatibleBinary left right &&
        match mixedNative left right, emitted with
        | true, .nativeBinary operation => scalarEncodingMatches instruction.opcode operation
        | false, operation => scalarEncodingMatches instruction.opcode operation
        | _, _ => false
    | _ => false
  else if instruction.opcode ∈ [98, 99, 100] then match stack with
    | right :: left :: _ => numeric left && right ∈ [.word32, .native] && scalarEncodingMatches instruction.opcode emitted
    | _ => false
  else match stack with
    | value :: _ => numeric value && scalarEncodingMatches instruction.opcode emitted
    | _ => false

private def resultKind (opcode : Nat) : ScalarKind :=
  if opcode ∈ [211, 212, 213, 138, 139, 224] then .native
  else if opcode ∈ [106, 110, 133, 137, 185, 186] then .word64 else .word32

private def splitTextChars (separator : List Char) : Nat → List Char → List Char → List (List Char)
  | 0, current, tail => [current.reverse ++ tail]
  | _ + 1, current, [] => [current.reverse]
  | remaining + 1, current, text@(c :: tail) =>
    if separator.isPrefixOf text then
      current.reverse :: splitTextChars separator remaining [] (text.drop separator.length)
    else splitTextChars separator remaining (c :: current) tail

private def splitText (text separator : String) : List String :=
  if separator.toList.isEmpty then [text]
  else (splitTextChars separator.toList (text.toList.length + 1) [] text.toList).map String.ofList

private def replaceTextChars (pattern replacement : List Char) : Nat → List Char → List Char
  | 0, text => text
  | _ + 1, [] => []
  | remaining + 1, text@(c :: tail) =>
    if pattern.isPrefixOf text then
      replacement ++ replaceTextChars pattern replacement remaining (text.drop pattern.length)
    else c :: replaceTextChars pattern replacement remaining tail

private def replaceText (text pattern replacement : String) : String :=
  if pattern.toList.isEmpty then text
  else String.ofList (replaceTextChars pattern.toList replacement.toList (text.toList.length + 1) text.toList)

private def scalarTypeName : TypeExpr → Option String
  | .void => some "System.Void"
  | .atom _ name | .constructor _ name => some name
  | .aggregate identity _ | .enum identity _ => (splitText identity "::")[1]?
  | .parameter index => some ("!!" ++ toString index)
  | .byref element => (· ++ "&") <$> scalarTypeName element
  | .pointer element => (· ++ "*") <$> scalarTypeName element
  | .apply constructor argument => do
    let name ← scalarTypeName constructor
    let element ← scalarTypeName argument
    return if name.endsWith ">" then (name.dropEnd 1).toString ++ "," ++ element ++ ">"
      else name ++ "<" ++ element ++ ">"

private def parameterTokens (depth : Nat) (current : List Char) : List Char → Option (List String)
  | [] => if depth != 0 then none else if current.isEmpty then some [] else some [String.ofList current.reverse]
  | ',' :: [] => none
  | ',' :: tail =>
    if depth == 0 then
      if current.isEmpty then none else (String.ofList current.reverse :: ·) <$> parameterTokens 0 [] tail
    else parameterTokens depth (',' :: current) tail
  | '<' :: tail => parameterTokens (depth + 1) ('<' :: current) tail
  | '>' :: tail => if depth == 0 then none else parameterTokens (depth - 1) ('>' :: current) tail
  | c :: tail => parameterTokens depth (c :: current) tail

private def parameterTypeMatches (token : String) (type : TypeExpr) : Bool :=
  if scalarTypeName type == some token then true
  else match type with
    | .byref element => token.startsWith "!" && !token.startsWith "!!" && token.endsWith "&" && scalarType element == .other
    | .pointer element => token.startsWith "!" && !token.startsWith "!!" && token.endsWith "*" && scalarType element == .other
    | _ => token.startsWith "!" && !token.startsWith "!!" && scalarType type == .other

private def normalizeExternalIdentity (site : CallSite) (identity : String) : Option String := do
  let normalized ← site.typeArguments.zipIdx.reverse.foldlM (fun text (type, index) => do
    let name ← scalarTypeName type
    return replaceText text ("!!" ++ toString index) name) identity
  let owner ← scalarTypeName site.declaringType
  match splitText owner "<" with
  | [] | [_] => return normalized
  | _ :: tail =>
    let suffix := String.intercalate "<" tail
    if !suffix.endsWith ">" then none else
      let arguments ← parameterTokens 0 [] (suffix.dropEnd 1).toString.toList
      return arguments.zipIdx.reverse.foldl (fun text (name, index) =>
        replaceText text ("!" ++ toString index) name) normalized

private def externalParametersMatch (site : CallSite) (identity : String) : Bool :=
  ((do
    let normalized ← normalizeExternalIdentity site identity
    let [_, tail] := splitText normalized "(" | none
    if !tail.endsWith ")" then none else
      let tokens ← parameterTokens 0 [] (tail.dropEnd 1).toString.toList
      return tokens.length == site.parameterTypes.length &&
        (tokens.zip site.parameterTypes).all fun (token, type) => parameterTypeMatches token type) : Option Bool).getD false

private def callParametersMatch (site : CallSite) : Bool :=
  site.parameterCount == site.parameterTypes.length && match site.target with
    | .managed _ => true
    | .external identity => externalParametersMatch site identity

private def externalResult (site : CallSite) (identity : String) : ScalarKind :=
  match normalizeExternalIdentity site identity with
  | none => .other
  | some normalized =>
    let signature := (splitText normalized "::")[1]?.getD ""
    match site.returnType with
    | .atom _ name => if signature.startsWith (name ++ " ") then scalarType site.returnType else .other
    | .byref _ =>
      if ((splitText signature " ")[0]?.getD "").endsWith "&" then .reference else .other
    | .enum identity _ =>
      let name := (splitText identity "::")[1]?.getD ""
      if name != "" && signature.startsWith (name ++ " ") then scalarType site.returnType else .other
    | _ => .other

private def callResult (site : CallSite) : ScalarKind :=
  match site.target with
  | .managed _ => scalarType site.returnType
  | .external identity => externalResult site identity

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
    if value == scalarType type then return tail else none
  if let some (.store index) := argumentOperation instruction then
    let expected ← argumentKind raw index
    let value :: tail := stack | none
    if value == expected then return tail else none
  if opcode == 37 then
    let value :: tail := stack | none
    return value :: value :: tail
  if opcode == 40 || opcode == 115 then
    let .call site := instruction.operand | none
    let expected := site.parameterTypes.reverse.map scalarType ++
      (if opcode == 40 && site.hasThis then [.reference] else [])
    let pops := expected.length
    if !callParametersMatch site || pops > stack.length || stack.take pops != expected ||
        site.returnsValue != (site.returnType != .void) then none else
      return (if opcode == 115 then [ScalarKind.other] else if site.returnsValue then [callResult site] else []) ++ stack.drop pops
  if opcode == 42 then
    if raw.returnType == .void then
      if stack.isEmpty then return [] else none
    else match stack with
      | [value] => if value == scalarType raw.returnType then return [] else none
      | _ => none
  let (pops, pushes) ← rawStackEffect opcode
  if pops > stack.length then none else
    if pushes == 0 then return stack.drop pops
    else if pushes == 1 then return (← pushedKind raw instruction) :: stack.drop pops
    else none

private def checkScalarSite (raw : RawMethod) (features : FeatureCertificate) (certificate : ScalarCertificate) :
    RawInstruction × Nat → Option FeatureState → Option (List ScalarKind) → Op → Bool
  | (_, _), none, none, .unsupported _ => true
  | (instruction, pc), some feature, some stack, emitted =>
    stack.length == feature.stack.length && stack.length <= raw.maxStack &&
      (!scalarCovered instruction.opcode || scalarOpMatches instruction stack emitted) &&
      match scalarTransfer raw instruction stack, featureSuccessors pc instruction feature with
      | some after, some successors =>
        successors.all fun target => match features[target]? with
          | some (some _) => certificate[target]? == some (some after)
          | _ => false
      | _, _ => false
  | _, _, _, _ => false

def ScalarFlowValid (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Op) : Prop :=
  raw.code.length = features.length ∧ raw.code.length = certificate.length ∧ raw.code.length = code.length ∧
  certificate[0]? = some (some []) ∧
  all3 (fun (instruction, feature) stack emitted => checkScalarSite raw features certificate instruction feature stack emitted)
    (raw.code.zipIdx.zip features) certificate code = true

instance (raw : RawMethod) (features : FeatureCertificate) (certificate : ScalarCertificate) (code : List Op) :
    Decidable (ScalarFlowValid raw features certificate code) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem ScalarFlowValid.instruction_checked {raw : RawMethod} {features : FeatureCertificate}
    {certificate : ScalarCertificate} {code : List Op}
    (valid : ScalarFlowValid raw features certificate code)
    {pc : Nat} {instruction : RawInstruction} {feature : FeatureState} {stack : List ScalarKind} {emitted : Op}
    (rawAt : raw.code[pc]? = some instruction) (featureAt : features[pc]? = some (some feature))
    (stackAt : certificate[pc]? = some (some stack)) (emittedAt : code[pc]? = some emitted)
    (covered : scalarCovered instruction.opcode = true) :
    scalarOpMatches instruction stack emitted = true := by
  have pairAt : (raw.code.zipIdx.zip features)[pc]? = some ((instruction, pc), some feature) := by
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨by simp [List.getElem?_zipIdx, rawAt], featureAt⟩
  have checked := all3_at valid.2.2.2.2 pairAt stackAt emittedAt
  simp only [checkScalarSite, covered, Bool.not_true, Bool.false_or, Bool.and_eq_true] at checked
  exact checked.1.2

#print axioms ScalarFlowValid.instruction_checked

end CIL.Extraction
