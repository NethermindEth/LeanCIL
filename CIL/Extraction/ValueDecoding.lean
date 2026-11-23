import CIL.Extraction.Prefixes

/-!
# Value opcodes decoded from raw instructions

`Instruction.ofRaw?` gives the one instruction a raw value-family instruction denotes: stack
shuffling, return, constants, `ldnull`, arguments, locals, branches, integer arithmetic,
conversions, comparisons, integer indirect loads and stores, block copies and fills, array
allocations, lengths and element loads and stores, dynamic frame storage, the `readonly.` and
`unaligned.` prefixes, the class type tests `castclass` and `isinst`, the
instance field accesses `ldfld`, `ldflda` and `stfld` of a class or a struct, direct and
constrained calls, and construction by `newobj`, with every short and macro form folded into its
constructor. `valueEncodingMatches` accepts an emitted instruction exactly when it is that decoded
instruction, and `Instruction.valueOpcode` is the set of opcodes `ofRaw?` decodes for some
operand. Instantiation changes a decoded instruction only in the type a type operand names,
the method a call or construction names, or through a field operand
(`Instruction.ofRaw?_substitute`), so a closed generic body decodes like its original with each
type test and typed array instruction at the instantiated type, each call and construction of
the instantiated method, and each instance field access at its instantiated owner and held type
(`Instruction.ofRaw?_substitute_instance_field`).
`Instruction.ofRaw` is the total decoding: it writes a hole, `.unadmitted` of the raw opcode,
exactly where `ofRaw?` admits nothing (`Instruction.ofRaw_eq_unadmitted_iff`). Both take the raw
instruction before the decoded one, where a prefix would stand, and `Instruction.ofRawCode`
decodes code in one pass that carries it (`Instruction.ofRawCode_getElem?`).
-/

namespace CIL.Extraction

/-- One-byte opcodes are below this value; two-byte opcodes `0xFE nn` are `0xFE00 + nn`. -/
def oneByteOpcodes : Nat := 256

/-- The local a `ldloc`, `stloc` or `ldloca` instruction names, in any of its forms. -/
def localIndex (instruction : RawInstruction) : Option Nat :=
  match instruction.opcode, instruction.operand with
  -- `ldloc.0` to `ldloc.3` and `stloc.0` to `stloc.3`.
  | 6, .none | 10, .none => some 0
  | 7, .none | 11, .none => some 1
  | 8, .none | 12, .none => some 2
  | 9, .none | 13, .none => some 3
  -- `ldloc`, `ldloca` and `stloc`, short and long forms.
  | 17, .local n | 18, .local n | 19, .local n
  | 65036, .local n | 65037, .local n | 65038, .local n => some n
  | _, _ => none

/-- The indices an index operand of `opcode` can encode: an unsigned int8 after a one-byte
    opcode and an unsigned int16 after a two-byte one (ECMA-335 III.1.2). -/
def operandIndexBound (opcode : Nat) : Nat :=
  if opcode < oneByteOpcodes then 2 ^ 8 else 2 ^ 16

/-- The local a local-variable instruction names, when the instruction's encoding can carry it. -/
def encodedLocal (instruction : RawInstruction) : Option Nat :=
  (localIndex instruction).filter (· < operandIndexBound instruction.opcode)

/-- Operand kinds that instantiation rewrites; of these, value opcodes take only a type or a
    field. -/
def RawOperand.mentionsType : RawOperand → Bool
  | .type _ | .field .. | .call _ | .indirectCall .. => true
  | _ => false

/-- Whether an operand is a type, the operand of the class type tests. -/
def RawOperand.isType : RawOperand → Bool
  | .type _ => true
  | _ => false

/-- Whether an operand is a call site, the operand of `call` and `newobj`. -/
def RawOperand.isCall : RawOperand → Bool
  | .call _ => true
  | _ => false

/-- Substitution keeps an operand's kind, a type, call or field operand included, and leaves an
    operand that mentions no type unchanged. -/
theorem substituteOperand_mentionsType {arguments : List TypeExpr} {layouts : List RawLayout}
    {arity : Nat} {original operand : RawOperand}
    (substituted : substituteOperand arguments layouts arity original = some operand) :
    operand.mentionsType = original.mentionsType ∧ operand.isType = original.isType ∧
      operand.isCall = original.isCall ∧
      (FieldRef.ofOperand? operand).isSome = (FieldRef.ofOperand? original).isSome ∧
      (original.mentionsType = false → operand = original) := by
  cases original with
  | type type =>
    simp only [substituteOperand, Option.map_eq_map, Option.map_eq_some_iff] at substituted
    obtain ⟨_, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, rfl, nofun⟩
  | field owner index type name isStatic =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at substituted
    obtain ⟨_, _, _, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, rfl, nofun⟩
  | call site =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure]
      at substituted
    obtain ⟨_, _, substituted⟩ := substituted
    split at substituted <;>
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at substituted <;>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := substituted <;>
      exact ⟨rfl, rfl, rfl, rfl, nofun⟩
  | indirectCall returnType parameters hasThis explicitThis convention =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at substituted
    obtain ⟨_, _, _, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, rfl, nofun⟩
  | _ =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    exact ⟨by rw [substituted], by rw [substituted], by rw [substituted], by rw [substituted],
      fun _ => substituted.symm⟩

#print axioms substituteOperand_mentionsType

/-- The five raw opcodes that access a value through a type token. -/
def objectOpcode (opcode : Nat) : Bool := opcode ∈ [0x70, 0x71, 0x81, 0xfe15, 0xfe1c]

end CIL.Extraction

namespace CIL

open Extraction

/-- The opcodes `Instruction.ofRaw?` decodes for some operand. -/
def Instruction.valueOpcode (opcode : Nat) : Bool :=
  opcode == 0 || (2 <= opcode && opcode <= 33) || opcode == 37 || opcode == 38 ||
    (40 <= opcode && opcode <= 41) ||
    (42 <= opcode && opcode <= 77) || (82 <= opcode && opcode <= 85) ||
    (88 <= opcode && opcode <= 106) || (109 <= opcode && opcode <= 117) ||
    (123 <= opcode && opcode <= 125) || (129 <= opcode && opcode <= 139) ||
    opcode == 141 || (142 <= opcode && opcode <= 151) ||
    (154 <= opcode && opcode <= 159) || (162 <= opcode && opcode <= 164) ||
    (179 <= opcode && opcode <= 186) || (208 <= opcode && opcode <= 219) || opcode == 223 ||
    opcode == 224 || (65025 <= opcode && opcode <= 65030) ||
    (65033 <= opcode && opcode <= 65039) || opcode == 0xfe15 || opcode == 0xfe16 ||
    opcode == 0xfe1c || opcode == 0xfe1e || opcode == 0xfe12 || opcode == 0xfe17 ||
    opcode == 0xfe18

/-- `ldelema` (143) of the element type `type` after `previous`: a read-only address after
    `readonly.`, which it takes, and nothing after any other prefix. -/
def Instruction.ldelemaAfter? (previous : Option RawInstruction) (type : TypeExpr) :
    Option Instruction :=
  if previous.any fun before => before.opcode == 65054 then some (.ldelema type true)
  else if previous.any fun before => isPrefixOpcode before.opcode then none
  else some (.ldelema type false)

/-- The object, class or array operation a type operand denotes after its prefix. -/
def Instruction.ofType? (previous : Option RawInstruction) (opcode : Nat) (type : TypeExpr) :
    Option Instruction :=
  match opcode with
  | 0x70 => some (.cpobj type)
  | 0x71 => some (.ldobj type)
  | 0x74 => some (.castclass type)
  | 0x75 => some (.isinst type)
  | 0x81 => some (.stobj type)
  | 0x8d => some (.newarr type)
  | 0x8f => Instruction.ldelemaAfter? previous type
  | 0xa3 => some (.ldelem_any type)
  | 0xa4 => some (.stelem_any type)
  | 0xd0 => some (.ldtoken (.type type))
  | 0xfe15 => some (.initobj type)
  | 0xfe16 => some .nop
  | 0xfe1c => some (.sizeof type)
  | _ => none

/-- Every successful type-operand decoding names one of the supported opcodes. -/
theorem Instruction.ofType?_opcode {previous : Option RawInstruction} {opcode : Nat}
    {type : TypeExpr} {instruction : Instruction}
    (named : Instruction.ofType? previous opcode type = some instruction) :
    opcode = 116 ∨ opcode = 117 ∨ opcode = 141 ∨ opcode = 163 ∨ opcode = 164 ∨
      opcode = 143 ∨ opcode = 0x70 ∨ opcode = 0x71 ∨ opcode = 0x81 ∨
      opcode = 0xFE15 ∨ opcode = 0xFE1C ∨ opcode = 0xFE16 ∨ opcode = 0xD0 := by
  unfold Instruction.ofType? at named
  repeat' split at named
  all_goals first | contradiction | simp

#print axioms Instruction.ofType?_opcode

/-- The transfer or dispatch modifier carried by a direct call. -/
private def callPrefixes : Option RawInstruction → CallPrefixes
  | some ⟨_, 0xFE14, .none⟩ => { tail := true }
  | some ⟨_, 0xFE16, .type receiver⟩ => { constrained := some receiver }
  | _ => {}

/-- The closed signature shared by a managed address and an indirect call. -/
def ManagedSignature.ofTypes (result : TypeExpr) (parameters : List TypeExpr) : ManagedSignature :=
  ⟨callableType result, parameters.map callableType⟩

/-- A method-token instruction names its raw site and carries its supported prefix. -/
def Instruction.ofCallSite? (previous : Option RawInstruction) (opcode : Nat)
    (site : CallSite) : Option Instruction :=
  if opcode == 40 then some (.call site.method (callPrefixes previous))
  else if opcode == 115 then some (.newobj site.method)
  else if opcode == 111 && (callPrefixes previous).constrained.isSome then
    some (.call site.method (callPrefixes previous))
  else if opcode == 111 && site.hasThis && !(previous.any (isPrefixOpcode ·.opcode)) then
    some (.callvirt site.method)
  else if opcode == 65030 then
    if site.hasThis then none else
    match site.target, managedOwner site.declaringType with
    | .managed token, some (owner, _) =>
      some (.ldftn ⟨owner, token, site.typeArguments.map callableType⟩
        (ManagedSignature.ofTypes site.returnType site.parameterTypes))
    | _, _ => none
  else none

/-- Call sites decode at `call` (40), `callvirt` (111), `newobj` (115) and `ldftn` (65030). -/
theorem Instruction.ofCallSite?_opcode {previous : Option RawInstruction} {opcode : Nat}
    {site : CallSite} {instruction : Instruction}
    (named : Instruction.ofCallSite? previous opcode site = some instruction) :
    opcode = 40 ∨ opcode = 115 ∨ opcode = 111 ∨ opcode = 65030 := by
  unfold Instruction.ofCallSite? at named
  repeat' split at named
  all_goals first | contradiction | simp_all

#print axioms Instruction.ofCallSite?_opcode

/-- The instance field instruction `opcode` denotes on `field`: `ldfld` (123), `ldflda` (124)
    or `stfld` (125). -/
def Instruction.instanceField? (opcode : Nat) (field : FieldRef) : Option Instruction :=
  if opcode == 123 then some (.ldfld field) else if opcode == 124 then some (.ldflda field)
  else if opcode == 125 then some (.stfld field) else none

/-- Only `ldfld` (123), `ldflda` (124) and `stfld` (125) denote an instance field instruction. -/
theorem Instruction.instanceField?_opcode {opcode : Nat} {field : FieldRef}
    {instruction : Instruction}
    (accessed : Instruction.instanceField? opcode field = some instruction) :
    opcode = 123 ∨ opcode = 124 ∨ opcode = 125 := by
  unfold Instruction.instanceField? at accessed
  split at accessed
  · exact .inl (beq_iff_eq.mp ‹_›)
  · split at accessed
    · exact .inr (.inl (beq_iff_eq.mp ‹_›))
    · split at accessed
      · exact .inr (.inr (beq_iff_eq.mp ‹_›))
      · cases accessed

#print axioms Instruction.instanceField?_opcode

/-- Whether `emitted` is the instruction `decoded`, operands included. Defined only for the
    value constructors `ofRaw?` produces; every other `decoded` gives `false`. -/
def Instruction.sameValue (decoded emitted : Instruction) : Bool :=
  match decoded with
  -- Stack shuffling and return.
  | .nop => (emitted matches .nop)
  | .dup => (emitted matches .dup)
  | .pop => (emitted matches .pop)
  | .ret => (emitted matches .ret)
  -- Constants, arguments and locals compare their operand.
  | .ldc_i4 expected => match emitted with | .ldc_i4 actual => expected == actual | _ => false
  | .ldc_i8 expected => match emitted with | .ldc_i8 actual => expected == actual | _ => false
  | .ldnull => (emitted matches .ldnull)
  | .ldtoken (.type expected) => match emitted with
    | .ldtoken (.type actual) => expected == actual
    | _ => false
  | .ldstr text => match emitted with
    | .ldstr actual => decide (text = actual)
    | _ => false
  | .cpblk expected => match emitted with
    | .cpblk actual => expected == actual
    | _ => false
  | .initblk expected => match emitted with
    | .initblk actual => expected == actual
    | _ => false
  | .ldarg expected => match emitted with | .ldarg actual => expected == actual | _ => false
  | .ldarga expected => match emitted with | .ldarga actual => expected == actual | _ => false
  | .starg expected => match emitted with | .starg actual => expected == actual | _ => false
  | .ldloc expected => match emitted with | .ldloc actual => expected == actual | _ => false
  | .stloc expected => match emitted with | .stloc actual => expected == actual | _ => false
  | .ldloca expected => match emitted with | .ldloca actual => expected == actual | _ => false
  -- Branches compare their target.
  | .br expected => match emitted with | .br actual => expected == actual | _ => false
  | .brfalse expected => match emitted with | .brfalse actual => expected == actual | _ => false
  | .brtrue expected => match emitted with | .brtrue actual => expected == actual | _ => false
  | .beq expected => match emitted with | .beq actual => expected == actual | _ => false
  | .bge expected => match emitted with | .bge actual => expected == actual | _ => false
  | .bgt expected => match emitted with | .bgt actual => expected == actual | _ => false
  | .ble expected => match emitted with | .ble actual => expected == actual | _ => false
  | .blt expected => match emitted with | .blt actual => expected == actual | _ => false
  | .bne_un expected => match emitted with | .bne_un actual => expected == actual | _ => false
  | .bge_un expected => match emitted with | .bge_un actual => expected == actual | _ => false
  | .bgt_un expected => match emitted with | .bgt_un actual => expected == actual | _ => false
  | .ble_un expected => match emitted with | .ble_un actual => expected == actual | _ => false
  | .blt_un expected => match emitted with | .blt_un actual => expected == actual | _ => false
  | .switch expected => match emitted with | .switch actual => expected == actual | _ => false
  -- Indirect loads and stores compare their kind.
  | .ldind expected => match emitted with | .ldind actual => expected == actual | _ => false
  | .stind expected => match emitted with | .stind actual => expected == actual | _ => false
  -- Array lengths and elements compare their kind.
  | .ldlen => (emitted matches .ldlen)
  | .ldelem expected => match emitted with | .ldelem actual => expected == actual | _ => false
  | .ldelem_ref => (emitted matches .ldelem_ref)
  | .stelem expected => match emitted with | .stelem actual => expected == actual | _ => false
  | .stelem_ref => (emitted matches .stelem_ref)
  -- Arithmetic, bitwise operations and shifts.
  | .add => (emitted matches .add)
  | .sub => (emitted matches .sub)
  | .mul => (emitted matches .mul)
  | .div => (emitted matches .div)
  | .div_un => (emitted matches .div_un)
  | .rem => (emitted matches .rem)
  | .rem_un => (emitted matches .rem_un)
  | .and => (emitted matches .and)
  | .or => (emitted matches .or)
  | .xor => (emitted matches .xor)
  | .shl => (emitted matches .shl)
  | .shr => (emitted matches .shr)
  | .shr_un => (emitted matches .shr_un)
  | .neg => (emitted matches .neg)
  | .not => (emitted matches .not)
  -- Conversions.
  | .conv_i1 => (emitted matches .conv_i1)
  | .conv_i2 => (emitted matches .conv_i2)
  | .conv_i4 => (emitted matches .conv_i4)
  | .conv_i8 => (emitted matches .conv_i8)
  | .conv_u1 => (emitted matches .conv_u1)
  | .conv_u2 => (emitted matches .conv_u2)
  | .conv_u4 => (emitted matches .conv_u4)
  | .conv_u8 => (emitted matches .conv_u8)
  | .conv_i => (emitted matches .conv_i)
  | .conv_u => (emitted matches .conv_u)
  | .conv_ovf expected => match emitted with | .conv_ovf actual => expected == actual | _ => false
  | .conv_ovf_un expected =>
    match emitted with | .conv_ovf_un actual => expected == actual | _ => false
  -- Overflow-checked arithmetic and comparisons.
  | .add_ovf => (emitted matches .add_ovf)
  | .add_ovf_un => (emitted matches .add_ovf_un)
  | .sub_ovf => (emitted matches .sub_ovf)
  | .sub_ovf_un => (emitted matches .sub_ovf_un)
  | .mul_ovf => (emitted matches .mul_ovf)
  | .mul_ovf_un => (emitted matches .mul_ovf_un)
  | .ceq => (emitted matches .ceq)
  | .cgt => (emitted matches .cgt)
  | .cgt_un => (emitted matches .cgt_un)
  | .clt => (emitted matches .clt)
  | .clt_un => (emitted matches .clt_un)
  -- Each object instruction names its closed storage type.
  | .ldobj expected => match emitted with | .ldobj actual => expected == actual | _ => false
  | .stobj expected => match emitted with | .stobj actual => expected == actual | _ => false
  | .cpobj expected => match emitted with | .cpobj actual => expected == actual | _ => false
  | .initobj expected => match emitted with | .initobj actual => expected == actual | _ => false
  | .sizeof expected => match emitted with | .sizeof actual => expected == actual | _ => false
  -- Type tests compare the class they test.
  | .castclass expected =>
    match emitted with | .castclass actual => expected == actual | _ => false
  | .isinst expected => match emitted with | .isinst actual => expected == actual | _ => false
  -- Typed array instructions compare the element type they name.
  | .newarr expected => match emitted with | .newarr actual => expected == actual | _ => false
  | .ldelem_any expected =>
    match emitted with | .ldelem_any actual => expected == actual | _ => false
  | .stelem_any expected =>
    match emitted with | .stelem_any actual => expected == actual | _ => false
  | .ldelema expected readOnly => match emitted with
    | .ldelema actual actualReadOnly => expected == actual && readOnly == actualReadOnly
    | _ => false
  -- Instance field instructions compare the field they name.
  | .ldfld expected => match emitted with | .ldfld actual => expected == actual | _ => false
  | .ldflda expected => match emitted with | .ldflda actual => expected == actual | _ => false
  | .stfld expected => match emitted with | .stfld actual => expected == actual | _ => false
  -- A call compares the method it names and its prefixes, a construction its constructor.
  | .callvirt expected => match emitted with
    | .callvirt actual => expected == actual
    | _ => false
  | .ldftn identity signature => match emitted with
    | .ldftn target sig => identity == target && signature == sig
    | _ => false
  | .calli signature tail => match emitted with
    | .calli sig isTail => signature == sig && tail == isTail
    | _ => false
  | .call expected prefixes => match emitted with
    | .call actual actualPrefixes => expected == actual && prefixes == actualPrefixes
    | _ => false
  | .newobj expected => match emitted with | .newobj actual => expected == actual | _ => false
  -- Dynamic frame storage.
  | .localloc => (emitted matches .localloc)
  -- Constructors outside the value family are never a decoded value.
  | _ => false

/-- An opcode result together with its reflexive value-encoding comparison. -/
private abbrev DecodedValue := { value : Instruction // value.sameValue value = true }

/-- The value emitted by an admitted opcode, with its encoding checked at the constructor. -/
private def emit (value : Instruction)
    (valid : value.sameValue value = true := by
      first
      | rfl
      | exact Nat.beq_refl _
      | exact decide_eq_true (Eq.refl _)
      | exact @List.instReflBEq Nat _ ⟨Nat.beq_refl _⟩ |>.rfl) :
    Option DecodedValue := some ⟨value, valid⟩

/-- The value of an instruction with an immediate, branch, slot or absent operand. -/
private def plainValue? (previous : Option RawInstruction) (raw : RawInstruction) :
    Option DecodedValue :=
  match raw.opcode, raw.operand with
  -- Stack shuffling and return.
  | 0, .none => emit .nop
  | 37, .none => emit .dup
  | 38, .none => emit .pop
  | 42, .none => emit .ret
  -- Constants, with the operand ranges ECMA-335 gives each form.
  | 20, .none => emit .ldnull
  | 114, .text text => emit (.ldstr text)
  | 21, .none => emit (.ldc_i4 (BitVec.ofInt 32 (-1)))
  | 31, .integer value =>
    if -128 <= value && value < 128 then emit (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 32, .integer value =>
    if -(2^31) <= value && value < 2^31 then emit (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 33, .integer value =>
    if -(2^63) <= value && value < 2^63 then emit (.ldc_i8 (BitVec.ofInt 64 value)) else none
  | 22, .none | 23, .none | 24, .none | 25, .none | 26, .none | 27, .none | 28, .none
  | 29, .none | 30, .none => emit (.ldc_i4 (BitVec.ofNat 32 (raw.opcode - 22)))
  -- Argument loads, addresses and stores; an index wider than its form encodes gives `none`.
  | 2, .none => emit (.ldarg 0) | 3, .none => emit (.ldarg 1)
  | 4, .none => emit (.ldarg 2) | 5, .none => emit (.ldarg 3)
  | 14, .argument index | 65033, .argument index =>
    if index < operandIndexBound raw.opcode then emit (.ldarg index) else none
  | 15, .argument index | 65034, .argument index =>
    if index < operandIndexBound raw.opcode then emit (.ldarga index) else none
  | 16, .argument index | 65035, .argument index =>
    if index < operandIndexBound raw.opcode then emit (.starg index) else none
  -- Locals; `encodedLocal` validates the operand of every form and its width.
  | 6, _ | 7, _ | 8, _ | 9, _ | 17, _ | 65036, _ =>
    (encodedLocal raw).bind fun index => emit (.ldloc index)
  | 10, _ | 11, _ | 12, _ | 13, _ | 19, _ | 65038, _ =>
    (encodedLocal raw).bind fun index => emit (.stloc index)
  | 18, _ | 65037, _ => (encodedLocal raw).bind fun index => emit (.ldloca index)
  -- Branches, short and long forms, keep their resolved target.
  | 43, .target target | 56, .target target => emit (.br target)
  | 44, .target target | 57, .target target => emit (.brfalse target)
  | 45, .target target | 58, .target target => emit (.brtrue target)
  | 46, .target target | 59, .target target => emit (.beq target)
  | 47, .target target | 60, .target target => emit (.bge target)
  | 48, .target target | 61, .target target => emit (.bgt target)
  | 49, .target target | 62, .target target => emit (.ble target)
  | 50, .target target | 63, .target target => emit (.blt target)
  | 51, .target target | 64, .target target => emit (.bne_un target)
  | 52, .target target | 65, .target target => emit (.bge_un target)
  | 53, .target target | 66, .target target => emit (.bgt_un target)
  | 54, .target target | 67, .target target => emit (.ble_un target)
  | 55, .target target | 68, .target target => emit (.blt_un target)
  | 69, .targets targets => emit (.switch targets)
  -- Integer indirect loads and stores; the floating and reference kinds decode to nothing.
  | 70, .none => emit (.ldind .i1) | 71, .none => emit (.ldind .u1)
  | 72, .none => emit (.ldind .i2) | 73, .none => emit (.ldind .u2)
  | 74, .none => emit (.ldind .i4) | 75, .none => emit (.ldind .u4)
  | 76, .none => emit (.ldind .i8) | 77, .none => emit (.ldind .i)
  | 82, .none => emit (.stind .i1) | 83, .none => emit (.stind .i2)
  | 84, .none => emit (.stind .i4) | 85, .none => emit (.stind .i8)
  | 223, .none => emit (.stind .i)
  -- Array lengths and elements; the floating kinds decode to nothing.
  | 142, .none => emit .ldlen
  | 144, .none => emit (.ldelem .i1) | 145, .none => emit (.ldelem .u1)
  | 146, .none => emit (.ldelem .i2) | 147, .none => emit (.ldelem .u2)
  | 148, .none => emit (.ldelem .i4) | 149, .none => emit (.ldelem .u4)
  | 150, .none => emit (.ldelem .i8) | 151, .none => emit (.ldelem .i)
  | 154, .none => emit .ldelem_ref
  | 155, .none => emit (.stelem .i) | 156, .none => emit (.stelem .i1)
  | 157, .none => emit (.stelem .i2) | 158, .none => emit (.stelem .i4)
  | 159, .none => emit (.stelem .i8)
  | 162, .none => emit .stelem_ref
  -- Arithmetic, bitwise operations and shifts.
  | 88, .none => emit .add | 89, .none => emit .sub | 90, .none => emit .mul
  | 91, .none => emit .div | 92, .none => emit .div_un
  | 93, .none => emit .rem | 94, .none => emit .rem_un
  | 95, .none => emit .and | 96, .none => emit .or | 97, .none => emit .xor
  | 98, .none => emit .shl | 99, .none => emit .shr | 100, .none => emit .shr_un
  | 101, .none => emit .neg | 102, .none => emit .not
  -- Conversions.
  | 103, .none => emit .conv_i1 | 104, .none => emit .conv_i2
  | 105, .none => emit .conv_i4 | 106, .none => emit .conv_i8
  | 109, .none => emit .conv_u4 | 110, .none => emit .conv_u8
  | 209, .none => emit .conv_u2 | 210, .none => emit .conv_u1
  | 211, .none => emit .conv_i | 224, .none => emit .conv_u
  -- Overflow-checked conversions from an unsigned source.
  | 130, .none => emit (.conv_ovf_un .i1) | 131, .none => emit (.conv_ovf_un .i2)
  | 132, .none => emit (.conv_ovf_un .i4) | 133, .none => emit (.conv_ovf_un .i8)
  | 134, .none => emit (.conv_ovf_un .u1) | 135, .none => emit (.conv_ovf_un .u2)
  | 136, .none => emit (.conv_ovf_un .u4) | 137, .none => emit (.conv_ovf_un .u8)
  | 138, .none => emit (.conv_ovf_un .i) | 139, .none => emit (.conv_ovf_un .u)
  -- Overflow-checked conversions from a signed source.
  | 179, .none => emit (.conv_ovf .i1) | 180, .none => emit (.conv_ovf .u1)
  | 181, .none => emit (.conv_ovf .i2) | 182, .none => emit (.conv_ovf .u2)
  | 183, .none => emit (.conv_ovf .i4) | 184, .none => emit (.conv_ovf .u4)
  | 185, .none => emit (.conv_ovf .i8) | 186, .none => emit (.conv_ovf .u8)
  | 212, .none => emit (.conv_ovf .i) | 213, .none => emit (.conv_ovf .u)
  -- Overflow-checked arithmetic.
  | 214, .none => emit .add_ovf | 215, .none => emit .add_ovf_un
  | 216, .none => emit .mul_ovf | 217, .none => emit .mul_ovf_un
  | 218, .none => emit .sub_ovf | 219, .none => emit .sub_ovf_un
  -- Comparisons.
  | 65025, .none => emit .ceq | 65026, .none => emit .cgt | 65027, .none => emit .cgt_un
  | 65028, .none => emit .clt | 65029, .none => emit .clt_un
  -- Dynamic frame storage; whether it is zeroed is the method's localsinit flag, not an operand.
  | 65039, .none => emit .localloc
  -- Block copies and fills, at the alignment an `unaligned.` before them gives.
  | 65047, .none => (blockAlignment previous).bind fun alignment =>
    emit (.cpblk alignment)
  | 65048, .none => (blockAlignment previous).bind fun alignment =>
    emit (.initblk alignment)
  -- The prefixes their consumers record; `invalidPredecessor` refuses a consumer that takes
  -- neither, and `rawPrefixesValid` a prefix with no consumer.
  | 65054, .none => if previous.any fun before => isPrefixOpcode before.opcode then none
    else emit .nop
  | 65042, operand => if (prefixAlignment operand).isSome then emit .nop else none
  | _, _ => none


/-- The instruction a value-family raw instruction denotes: one constructor per ECMA opcode,
    with short and macro forms folded into it. A type operand gives the type test or typed array
    instruction its opcode names, a struct or nongeneric class field the instruction its opcode
    names and a call site the `call` of the method it names, whose target the method's link table
    gives, at `call` or constrained `callvirt`, and its construction at `newobj`. Any other
    opcode, another operand kind that instantiation rewrites, or a malformed or out-of-range
    operand gives `none`. A hole is never a decoding, so `Instruction.ofRaw` can write one where
    this admits nothing.

    `previous` is the raw instruction before `raw`, `none` at the first pc. An instruction
    after a prefix it does not take does not decode. `ldelema` takes `readonly.` and records
    it, so after `readonly.` only `ldelema` decodes, and `ldelema` after any other prefix does
    not. `readonly.` decodes to `nop`, and not after any prefix. `unaligned.` with an operand of
    1, 2 or 4 decodes to `nop`, and only the takers `prefixTakes` names decode after it. The
    integer `ldind` and `stind` forms decode as without it, since the model accesses memory at
    alignment 1; `cpblk` and `initblk` decode to the block operation at the alignment it gives,
    or `defaultBlockAlignment` without it (`blockAlignment`). A constrained prefix decodes to
    `nop` and its call records the receiver. -/
def Instruction.ofRaw? (previous : Option RawInstruction) (raw : RawInstruction) :
    Option Instruction :=
  Option.filter (fun decoded => !(decoded matches .unadmitted _)) <|
  if invalidPredecessor previous raw then none else
  match raw.operand with
  | .type type => Instruction.ofType? previous raw.opcode type
  | .field owner _ _ _ false =>
    if owner.objectApplication then none else
      (FieldRef.ofOperand? raw.operand).bind (Instruction.instanceField? raw.opcode)
  | .call site => Instruction.ofCallSite? previous raw.opcode site
  | .indirectCall result parameters hasThis explicitThis convention =>
    if raw.opcode == 41 && !hasThis && !explicitThis && convention == 0 then
      some (.calli (ManagedSignature.ofTypes result parameters)
        (callPrefixes previous).tail)
    else none
  | _ =>
  if raw.operand.mentionsType || !Instruction.valueOpcode raw.opcode then none else
  (plainValue? previous raw).map Subtype.val

/-- `ofRaw?` decodes only the opcodes of `Instruction.valueOpcode`. -/
theorem Instruction.valueOpcode_of_ofRaw? {previous : Option RawInstruction} {raw : RawInstruction}
    {instruction : Instruction} (decoded : Instruction.ofRaw? previous raw = some instruction) :
    Instruction.valueOpcode raw.opcode = true := by
  cases opcodeValue : Instruction.valueOpcode raw.opcode
  · have found := (Option.filter_eq_some_iff.mp decoded).1
    split at found
    · cases found
    · split at found
      · rcases Instruction.ofType?_opcode found
          with opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs |
          opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs <;>
          rw [opcodeIs] at opcodeValue <;> exact absurd opcodeValue (by decide)
      · split at found
        · cases found
        obtain ⟨_, _, accessed⟩ := Option.bind_eq_some_iff.mp found
        rcases Instruction.instanceField?_opcode accessed with opcodeIs | opcodeIs | opcodeIs <;>
          rw [opcodeIs] at opcodeValue <;> exact absurd opcodeValue (by decide)
      · rcases Instruction.ofCallSite?_opcode found with
          opcodeIs | opcodeIs | opcodeIs | opcodeIs <;>
          rw [opcodeIs] at opcodeValue <;> exact absurd opcodeValue (by decide)
      · split at found
        · simp_all [Instruction.valueOpcode]
        · cases found
      · rw [opcodeValue, Bool.not_false, Bool.or_true,
          ite_eq_left_of_eq_true _ _ (eq_true rfl)] at found
        cases found
  · rfl

#print axioms Instruction.valueOpcode_of_ofRaw?

/-- No raw instruction decodes to a hole: a hole is what `Instruction.ofRaw` writes where
    `ofRaw?` admits nothing. -/
theorem Instruction.ofRaw?_ne_unadmitted (previous : Option RawInstruction) (raw : RawInstruction)
    (opcode : Nat) : Instruction.ofRaw? previous raw ≠ some (.unadmitted opcode) := fun decoded =>
  Bool.false_ne_true (Option.filter_eq_some_iff.mp decoded).2

#print axioms Instruction.ofRaw?_ne_unadmitted

/-- `readonly.` decodes only without an operand, and to `nop`. -/
theorem Instruction.ofRaw?_readOnly {previous : Option RawInstruction} {raw : RawInstruction}
    {decoded : Instruction} (readOnly : raw.opcode = 65054)
    (decodes : Instruction.ofRaw? previous raw = some decoded) :
    raw.operand = .none ∧ decoded = .nop := by
  obtain ⟨offset, opcode, operand⟩ := raw
  dsimp only at readOnly
  subst readOnly
  have found := (Option.filter_eq_some_iff.mp decodes).1
  split at found
  · cases found
  · split at found
    · rcases Instruction.ofType?_opcode found
        with opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs |
          opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs | opcodeIs <;>
        cases opcodeIs
    · split at found
      · cases found
      obtain ⟨_, _, accessed⟩ := Option.bind_eq_some_iff.mp found
      rcases Instruction.instanceField?_opcode accessed with opcodeIs | opcodeIs | opcodeIs <;>
        cases opcodeIs
    · rcases Instruction.ofCallSite?_opcode found with
        opcodeIs | opcodeIs | opcodeIs | opcodeIs <;>
        cases opcodeIs
    · cases found
    · cases operand
      case none =>
        change (if previous.any (fun before => isPrefixOpcode before.opcode) then none
          else emit .nop).map Subtype.val = some decoded at found
        split at found
        · cases found
        · cases found
          exact ⟨rfl, rfl⟩
      all_goals cases found

#print axioms Instruction.ofRaw?_readOnly

/-- `ldelema` decodes to an element address that is read-only exactly when `previous` is
    `readonly.`. -/
theorem Instruction.ofRaw?_ldelema {previous : Option RawInstruction} {raw : RawInstruction}
    {decoded : Instruction} (address : raw.opcode = 143)
    (decodes : Instruction.ofRaw? previous raw = some decoded) :
    ∃ type, decoded = .ldelema type (previous.any fun before => before.opcode == 65054) := by
  obtain ⟨offset, opcode, operand⟩ := raw
  dsimp only at address
  subst address
  have found := (Option.filter_eq_some_iff.mp decodes).1
  split at found
  · cases found
  · split at found
    · rename_i type _
      have after : Instruction.ldelemaAfter? previous type = some decoded := found
      unfold Instruction.ldelemaAfter? at after
      refine ⟨type, ?_⟩
      split at after
      · rename_i prefixed
        cases after
        simp [prefixed]
      · rename_i unprefixed
        split at after
        · cases after
        · cases after
          simp [unprefixed]
    · split at found
      · cases found
      obtain ⟨_, _, accessed⟩ := Option.bind_eq_some_iff.mp found
      rcases Instruction.instanceField?_opcode accessed with opcodeIs | opcodeIs | opcodeIs <;>
        cases opcodeIs
    · rcases Instruction.ofCallSite?_opcode found with
        opcodeIs | opcodeIs | opcodeIs | opcodeIs <;>
        cases opcodeIs
    · cases found
    · cases operand <;> cases found

#print axioms Instruction.ofRaw?_ldelema

/-- The instruction a raw instruction after `previous` denotes: its value decoding where `ofRaw?`
    admits one, and otherwise a hole carrying the raw opcode, which faults when stepped. -/
def Instruction.ofRaw (previous : Option RawInstruction) (raw : RawInstruction) : Instruction :=
  (Instruction.ofRaw? previous raw).getD (.unadmitted raw.opcode)

/-- Decode an ordinary closed site. Type handles require a recognized comparison, and object
    transfers and sizes require an admitted closed operand. -/
def Instruction.ofClosedValue (previous : Option RawInstruction) (raw : RawInstruction) :
    Instruction :=
  if (match raw.operand with
    | .type type => raw.opcode == 208 || objectOpcode raw.opcode && !objectApplicationAdmitted type
    | _ => false) then .unadmitted raw.opcode
  else Instruction.ofRaw previous raw

/-- Decoding gives a hole exactly when `ofRaw?` admits nothing, and the hole carries the raw
    opcode; an instruction `ofRaw?` admits is never a hole. -/
theorem Instruction.ofRaw_eq_unadmitted_iff (previous : Option RawInstruction)
    (raw : RawInstruction) (opcode : Nat) :
    Instruction.ofRaw previous raw = .unadmitted opcode ↔
      Instruction.ofRaw? previous raw = none ∧ opcode = raw.opcode := by
  unfold Instruction.ofRaw
  cases decoded : Instruction.ofRaw? previous raw with
  | none =>
    simp only [Option.getD_none, Instruction.unadmitted.injEq, true_and]
    exact eq_comm
  | some instruction =>
    simp only [Option.getD_some, reduceCtorEq, false_and, iff_false]
    intro hole
    subst hole
    exact Instruction.ofRaw?_ne_unadmitted previous raw opcode decoded

#print axioms Instruction.ofRaw_eq_unadmitted_iff

/-- An instruction `ofRaw?` admits decodes to itself. -/
theorem Instruction.ofRaw_of_ofRaw? {previous : Option RawInstruction} {raw : RawInstruction}
    {instruction : Instruction} (decoded : Instruction.ofRaw? previous raw = some instruction) :
    Instruction.ofRaw previous raw = instruction := by
  rw [Instruction.ofRaw, decoded, Option.getD_some]

#print axioms Instruction.ofRaw_of_ofRaw?

/-- An opcode outside the value opcodes decodes to a hole carrying it. -/
theorem Instruction.ofRaw_of_not_valueOpcode {previous : Option RawInstruction}
    {raw : RawInstruction} (outside : Instruction.valueOpcode raw.opcode = false) :
    Instruction.ofRaw previous raw = .unadmitted raw.opcode := by
  cases decoded : Instruction.ofRaw? previous raw with
  | none => rw [Instruction.ofRaw, decoded, Option.getD_none]
  | some _ =>
    rw [Instruction.valueOpcode_of_ofRaw? decoded] at outside
    cases outside

#print axioms Instruction.ofRaw_of_not_valueOpcode

/-- The raw instruction before `pc` that `rawAt` gives; `none` at the first pc, which has no
    instruction before it. -/
def rawBefore (rawAt : Nat → Option RawInstruction) (pc : Nat) : Option RawInstruction :=
  if pc == 0 then none else rawAt (pc - 1)

/-- A site can consult its enclosing method's bindings and profile. -/
abbrev SiteDecoder := Nat → Option RawInstruction → RawInstruction → Instruction

/-- The instruction at `pc`, with the preceding raw instruction available for prefixes. -/
def Instruction.ofRawAt (code : List RawInstruction) (pc : Nat)
    (decode : Nat → Option RawInstruction → RawInstruction → Instruction :=
      fun _ => Instruction.ofRaw) : Option Instruction :=
  code[pc]?.map (decode pc (rawBefore (code[·]?) pc))

/-- Decode each instruction at its pc, carrying the raw predecessor for prefix checks. -/
def Instruction.ofRawCode (previous : Option RawInstruction) (code : List RawInstruction)
    (decode : Nat → Option RawInstruction → RawInstruction → Instruction :=
      fun _ => Instruction.ofRaw) (start : Nat := 0) : List Instruction :=
  match code with
  | [] => []
  | raw :: rest => decode start previous raw :: ofRawCode (some raw) rest decode (start + 1)

/-- The sequential decoder and indexed decoder see the same pc and raw predecessor. -/
theorem Instruction.ofRawCode_getElem? (code : List RawInstruction) (pc : Nat)
    (decode : Nat → Option RawInstruction → RawInstruction → Instruction :=
      fun _ => Instruction.ofRaw) :
    (Instruction.ofRawCode none code decode)[pc]? = Instruction.ofRawAt code pc decode := by
  suffices walked : ∀ (code : List RawInstruction) (previous : Option RawInstruction)
      (start pc : Nat), (Instruction.ofRawCode previous code decode start)[pc]? =
        code[pc]?.map (decode (start + pc) (if pc == 0 then previous else code[pc - 1]?)) by
    simpa [Instruction.ofRawAt, rawBefore] using walked code none 0 pc
  intro code
  induction code with
  | nil => intro previous start pc; simp [Instruction.ofRawCode]
  | cons raw rest walkedRest =>
    intro previous start pc
    cases pc with
    | zero => simp [Instruction.ofRawCode]
    | succ pc =>
      rw [Instruction.ofRawCode, List.getElem?_cons_succ, walkedRest, List.getElem?_cons_succ]
      rw [Nat.add_right_comm start 1 pc]
      cases pc <;> rfl

#print axioms Instruction.ofRawCode_getElem?

/-- A decoded value is the emitted instruction exactly when `sameValue` accepts the pair. -/
theorem Instruction.sameValue_eq {decoded emitted : Instruction}
    (same : decoded.sameValue emitted = true) : emitted = decoded := by
  cases decoded <;> simp only [Instruction.sameValue] at same
  all_goals first
    | exact absurd same Bool.false_ne_true
    | (repeat' split at same) <;> simp_all

#print axioms Instruction.sameValue_eq

/-- Every instruction produced by the partial decoder matches its own value encoding. -/
theorem Instruction.sameValue_self_of_ofRaw? {previous : Option RawInstruction}
    {raw : RawInstruction} {emitted : Instruction}
    (decoded : Instruction.ofRaw? previous raw = some emitted) :
    emitted.sameValue emitted = true := by
  have found := (Option.filter_eq_some_iff.mp decoded).1
  split at found
  · cases found
  · split at found
    · unfold Instruction.ofType? at found
      repeat' split at found
      all_goals try unfold Instruction.ldelemaAfter? at found
      all_goals repeat' split at found
      all_goals cases found <;> simp [Instruction.sameValue]
    · split at found
      · cases found
      obtain ⟨_, _, found⟩ := Option.bind_eq_some_iff.mp found
      unfold Instruction.instanceField? at found
      repeat' split at found
      all_goals cases found <;> simp [Instruction.sameValue]
    · unfold Instruction.ofCallSite? at found
      repeat' split at found
      all_goals cases found <;> simp [Instruction.sameValue]
    · split at found <;> cases found <;> simp [Instruction.sameValue]
    · split at found
      · cases found
      · obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp found
        exact value.property

#print axioms Instruction.sameValue_self_of_ofRaw?

/-- Instantiation preserves the operand information that a preceding modifier checks. -/
private theorem invalidPredecessor_substitute {previous : Option RawInstruction}
    {raw : RawInstruction} {operand : RawOperand} {arguments : List TypeExpr}
    {layouts : List RawLayout} {arity : Nat}
    (substituted : substituteOperand arguments layouts arity raw.operand = some operand) :
    invalidPredecessor previous { raw with operand } = invalidPredecessor previous raw := by
  cases previous with
  | none => rfl
  | some modifier =>
    simp only [invalidPredecessor, Option.any_some]
    congr 2
    obtain ⟨offset, opcode, original⟩ := raw
    cases original <;> simp only [substituteOperand, Option.map_eq_map, Option.map_eq_some_iff,
      Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at substituted
    case' type =>
      obtain ⟨_, _, rfl⟩ := substituted
    case' field owner index type name isStatic =>
      obtain ⟨_, _, _, _, rfl⟩ := substituted
      cases isStatic
    case' call =>
      obtain ⟨_, _, substituted⟩ := substituted
      split at substituted <;>
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at substituted
      all_goals obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := substituted
    case' indirectCall =>
      obtain ⟨_, _, _, _, rfl⟩ := substituted
    all_goals try (subst operand; rfl)
    all_goals unfold prefixTakes
    all_goals dsimp only
    all_goals split <;> first | rfl | (split <;> simp_all <;> subst_vars <;> rfl)
#print axioms invalidPredecessor_substitute

/-- Substitution decodes managed addresses and indirect signatures from their closed operands.
    Other non-field instructions preserve admission and instantiate their type or method. -/
theorem Instruction.ofRaw?_substitute {previous : Option RawInstruction} {raw : RawInstruction}
    {operand : RawOperand} {arguments : List TypeExpr} {layouts : List RawLayout} {arity : Nat}
    (substituted : substituteOperand arguments layouts arity raw.operand = some operand)
    (unnamed : FieldRef.ofOperand? raw.operand = none) :
    Instruction.ofRaw? previous { raw with operand } =
      match raw.operand, operand with
      | .type _, .type type =>
        (Instruction.ofRaw? previous raw).bind fun _ =>
          Instruction.ofType? previous raw.opcode type
      | .call _, .call site =>
        if raw.opcode == 65030 then
          if invalidPredecessor previous raw then none else
            Instruction.ofCallSite? previous raw.opcode site
        else (Instruction.ofRaw? previous raw).bind fun _ =>
          Instruction.ofCallSite? previous raw.opcode site
      | .indirectCall .., .indirectCall result parameters hasThis explicitThis convention =>
        if !invalidPredecessor previous raw && raw.opcode == 41 && !hasThis &&
            !explicitThis && convention == 0 then
          some (.calli (ManagedSignature.ofTypes result parameters)
            (callPrefixes previous).tail)
        else none
      | _, _ => Instruction.ofRaw? previous raw := by
  have sameGuard := invalidPredecessor_substitute (previous := previous) (raw := raw) substituted
  obtain ⟨sameKind, sameType, sameCall, sameField, unchanged⟩ :=
    substituteOperand_mentionsType substituted
  obtain ⟨offset, opcode, original⟩ := raw
  cases original
  case field => cases unnamed
  case type before =>
    cases operand
    case type type =>
      have staysSpan (span : before.isRuntimeSpan = true) : type.isRuntimeSpan = true := by
        obtain ⟨closed, storage, same⟩ := Option.map_eq_some_iff.mp substituted
        cases same
        exact substituteStorageType_span span storage
      show Option.filter _ (if _ then none else Instruction.ofType? previous opcode type) =
        (Option.filter _ (if _ then none else Instruction.ofType? previous opcode before)).bind
          fun _ => Instruction.ofType? previous opcode type
      rw [sameGuard]
      split
      · rfl
      · unfold Instruction.ofType? Instruction.ldelemaAfter?
        split <;> repeat' first | rfl | split
        all_goals exact False.elim (by solve | simp_all)
    all_goals exact absurd sameType Bool.false_ne_true
  case call before =>
    cases operand
    case call site =>
      have receiver : site.hasThis = before.hasThis := by
        simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure]
          at substituted
        obtain ⟨_, _, substituted⟩ := substituted
        split at substituted <;>
          simp only [Option.bind_eq_some_iff, Option.some.injEq, RawOperand.call.injEq]
            at substituted <;>
          obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := substituted <;> rfl
      simp only [Instruction.ofRaw?, sameGuard]
      by_cases address : opcode = 65030
      · subst opcode
        simp only [beq_self_eq_true, ↓reduceIte]
        split
        · rfl
        · unfold Instruction.ofCallSite?
          simp only [Nat.reduceBEq, Bool.false_and, Bool.false_eq_true, ↓reduceIte, receiver]
          repeat' first | rfl | split
      · simp only [beq_iff_eq, address, ↓reduceIte]
        split
        · rfl
        · unfold Instruction.ofCallSite?
          simp only [receiver, beq_iff_eq, address, ↓reduceIte]
          repeat' first | rfl | split
    all_goals exact absurd sameCall Bool.false_ne_true
  case indirectCall =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at substituted
    obtain ⟨_, _, _, _, rfl⟩ := substituted
    simp only [Instruction.ofRaw?, sameGuard]
    repeat' split <;> simp_all
  -- Any other original either is unchanged or, like its substitute, is refused by the guard.
  all_goals first
    | (cases unchanged rfl <;> rfl)
    | (cases operand <;> first
        | exact absurd sameKind Bool.false_ne_true
        | exact absurd sameType.symm Bool.false_ne_true
        | exact absurd sameCall.symm Bool.false_ne_true
        | exact absurd sameField Bool.false_ne_true
        | exact absurd sameField.symm Bool.false_ne_true
        | rfl)

#print axioms Instruction.ofRaw?_substitute

/-- Instantiation closes an instance field operand's owner and held type, and the instantiated
    instruction, after no prefix it does not take, decodes to the field instruction of the same
    opcode over the closed reference unless the closed owner is a generic class instance. -/
theorem Instruction.ofRaw?_substitute_instance_field {previous : Option RawInstruction}
    {raw : RawInstruction} {operand : RawOperand}
    {arguments : List TypeExpr} {layouts : List RawLayout} {arity : Nat}
    {owner : TypeExpr} {index : Nat} {held : TypeExpr} {fieldName : MetadataName}
    (substituted : substituteOperand arguments layouts arity raw.operand = some operand)
    (named : raw.operand = .field owner index held fieldName false)
    (accepted : invalidPredecessor previous { raw with operand } = false) :
    ∃ closedOwner closed, substituteStorageType layouts arguments owner = some closedOwner ∧
      substituteStorageType layouts arguments held = some closed ∧
      operand = .field closedOwner index closed fieldName false ∧
      Instruction.ofRaw? previous { raw with operand } =
        if closedOwner.objectApplication then none
        else Instruction.instanceField? raw.opcode
          { owner := closedOwner, index, type := closed, name := fieldName } := by
  obtain ⟨offset, opcode, original⟩ := raw
  dsimp only at named
  subst named
  simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at substituted
  obtain ⟨closedOwner, holdsOwner, closed, holdsClosed, rfl⟩ := substituted
  refine ⟨closedOwner, closed, holdsOwner, holdsClosed, rfl, ?_⟩
  show Option.filter _ (if _ then none else
    if closedOwner.objectApplication then none
    else Instruction.instanceField? opcode _) = _
  simp only [accepted, Bool.false_eq_true, ite_false]
  cases closedOwner.objectApplication
  · simp only [Bool.false_eq_true, ite_false]
    unfold Instruction.instanceField?
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

#print axioms Instruction.ofRaw?_substitute_instance_field

end CIL

namespace CIL.Extraction

/-- Whether `emitted` is exactly what `raw` decodes to after `previous`, the raw instruction
    before it. -/
def valueEncodingMatches (previous : Option RawInstruction) (raw : RawInstruction)
    (emitted : Instruction) : Bool :=
  match Instruction.ofRaw? previous raw with
  | some decoded => decoded.sameValue emitted
  | none => false

/-- A matching value encoding is exactly the decoded instruction. -/
theorem valueEncodingMatches_sound {previous : Option RawInstruction} {raw : RawInstruction}
    {emitted : Instruction} (matched : valueEncodingMatches previous raw emitted = true) :
    Instruction.ofRaw? previous raw = some emitted := by
  unfold valueEncodingMatches at matched
  split at matched
  · next decoded decodes => rw [decodes, Instruction.sameValue_eq matched]
  · exact absurd matched Bool.false_ne_true

#print axioms valueEncodingMatches_sound

/-- A value-encoding check accepts exactly the decoded instruction at this site. -/
theorem valueEncodingMatches_iff {previous : Option RawInstruction} {raw : RawInstruction}
    {emitted : Instruction} :
    valueEncodingMatches previous raw emitted = true ↔
      Instruction.ofRaw? previous raw = some emitted := by
  refine ⟨valueEncodingMatches_sound, fun decoded => ?_⟩
  simpa only [valueEncodingMatches, decoded] using Instruction.sameValue_self_of_ofRaw? decoded

#print axioms valueEncodingMatches_iff

end CIL.Extraction
