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

private def scalarEncoding : Nat → Option Op
  | 88 => some .add | 89 => some .sub | 90 => some .mul
  | 91 => some (.divide true false) | 92 => some (.divide false false)
  | 93 => some (.divide true true) | 94 => some (.divide false true)
  | 95 => some .band | 96 => some .bor | 97 => some .bxor
  | 98 => some .shl | 99 => some .shr | 100 => some .shrUn
  | 101 => some .neg | 102 => some .bnot
  | 103 => some .convI1 | 104 => some .convI2 | 105 => some .convI4 | 106 => some .convI8
  | 109 => some .convU4 | 110 => some .convU8
  | 130 => some (.checkedConvert 8 true true) | 131 => some (.checkedConvert 16 true true)
  | 132 => some (.checkedConvert 32 true true) | 133 => some (.checkedConvert 64 true true)
  | 134 => some (.checkedConvert 8 false true) | 135 => some (.checkedConvert 16 false true)
  | 136 => some (.checkedConvert 32 false true) | 137 => some (.checkedConvert 64 false true)
  | 138 => some (.checkedConvert 64 true true) | 139 => some (.checkedConvert 64 false true)
  | 179 => some (.checkedConvert 8 true false) | 180 => some (.checkedConvert 8 false false)
  | 181 => some (.checkedConvert 16 true false) | 182 => some (.checkedConvert 16 false false)
  | 183 => some (.checkedConvert 32 true false) | 184 => some (.checkedConvert 32 false false)
  | 185 => some (.checkedConvert 64 true false) | 186 => some (.checkedConvert 64 false false)
  | 209 => some .convU2 | 210 => some .convU1 | 211 => some .convI8
  | 212 => some (.checkedConvert 64 true false) | 213 => some (.checkedConvert 64 false false)
  | 214 => some (.checkedArithmetic .add true) | 215 => some (.checkedArithmetic .add false)
  | 216 => some (.checkedArithmetic .mul true) | 217 => some (.checkedArithmetic .mul false)
  | 218 => some (.checkedArithmetic .sub true) | 219 => some (.checkedArithmetic .sub false)
  | 224 => some .convU
  | 65025 => some .eq | 65026 => some .gt | 65027 => some .gtu
  | 65028 => some .lt | 65029 => some .ltu
  | _ => none

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
  if 21 <= instruction.opcode && instruction.opcode <= 33 then literal instruction == some emitted
  else if instruction.operand != .none then false
  else match scalarEncoding instruction.opcode with
    | none => false
    | some operation =>
      if scalarBinary instruction.opcode then match stack with
        | right :: left :: _ => compatibleBinary left right &&
            emitted == (if mixedNative left right then .nativeBinary operation else operation)
        | _ => false
      else if instruction.opcode ∈ [98, 99, 100] then match stack with
        | right :: left :: _ => numeric left && right ∈ [.word32, .native] && emitted == operation
        | _ => false
      else match stack with
        | value :: _ => numeric value && emitted == operation
        | _ => false

private def resultKind (opcode : Nat) : ScalarKind :=
  if opcode ∈ [211, 212, 213, 138, 139, 224] then .native
  else if opcode ∈ [106, 110, 133, 137, 185, 186] then .word64 else .word32

private def externalResult (site : CallSite) (identity : String) : ScalarKind :=
  let signature := (identity.splitOn "::")[1]?.getD ""
  let token := (signature.splitOn " ")[0]?.getD ""
  if token.startsWith "!!" && !token.endsWith "&" then
    let index := ((token.splitOn "!!")[1]?.getD "").toNat?
    match index with
    | some index => if site.typeArguments[index]? == some site.returnType then scalarType site.returnType else .other
    | none => .other
  else match site.returnType with
  | .atom _ name => if signature.startsWith (name ++ " ") then scalarType site.returnType else .other
  | .byref _ =>
    if ((signature.splitOn " ")[0]?.getD "").endsWith "&" then .reference else .other
  | .enum identity _ =>
    let name := (identity.splitOn "::")[1]?.getD ""
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
    else if instruction.opcode == 33 || instruction.opcode == 76 then some .word64
    else if instruction.opcode ∈ [20, 34, 35, 114, 208, 65030] then some .other
    else some .word32

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
  if opcode == 37 then
    let value :: tail := stack | none
    return value :: value :: tail
  if opcode == 40 || opcode == 115 then
    let .call site := instruction.operand | none
    let pops := site.parameterCount + (if opcode == 40 && site.hasThis then 1 else 0)
    if pops > stack.length then none else
      return (if opcode == 115 then [ScalarKind.other] else if site.returnsValue then [callResult site] else []) ++ stack.drop pops
  if opcode == 42 then
    let pops := if raw.returnType == .void then 0 else 1
    if pops > stack.length then none else return stack.drop pops
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
