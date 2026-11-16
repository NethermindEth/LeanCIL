import CIL.Extraction.Generics

/-!
# Value opcodes decoded from raw instructions

`Instruction.ofRaw?` gives the one instruction a raw value-family instruction denotes: stack
shuffling, return, constants, `ldnull`, arguments, locals, branches, integer arithmetic,
conversions, comparisons, integer indirect loads and stores, dynamic frame storage, the class
type tests `castclass` and `isinst` and the class instance field accesses `ldfld`, `ldflda` and
`stfld`, with every short and macro form folded into its constructor. `valueEncodingMatches`
accepts an emitted instruction exactly when it is that decoded instruction, and
`Instruction.valueOpcode` is the set of opcodes `ofRaw?` decodes for some operand.
Instantiation changes a decoded instruction only in the type a type test names or through a field
operand (`Instruction.ofRaw?_substitute`), so a closed generic body decodes like its original
with each type test at the instantiated type, and each class field access at the same owner with
its held type instantiated (`Instruction.ofRaw?_substitute_field`). `Instruction.ofRaw` is the total decoding: it writes a hole, `.unadmitted` of the raw
opcode, exactly where `ofRaw?` admits nothing (`Instruction.ofRaw_eq_unadmitted_iff`).
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

/-- Substitution keeps an operand's kind, a type or a field operand included, and leaves an
    operand that mentions no type unchanged. -/
theorem substituteOperand_mentionsType {arguments : List TypeExpr} {layouts : List RawLayout}
    {arity : Nat} {original operand : RawOperand}
    (substituted : substituteOperand arguments layouts arity original = some operand) :
    operand.mentionsType = original.mentionsType ∧ operand.isType = original.isType ∧
      (FieldRef.ofOperand? operand).isSome = (FieldRef.ofOperand? original).isSome ∧
      (original.mentionsType = false → operand = original) := by
  cases original with
  | type type =>
    simp only [substituteOperand, Option.map_eq_map, Option.map_eq_some_iff] at substituted
    obtain ⟨_, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, nofun⟩
  | field owner index type name isStatic =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at substituted
    obtain ⟨_, _, _, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, nofun⟩
  | call site =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure]
      at substituted
    obtain ⟨_, _, substituted⟩ := substituted
    split at substituted <;>
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at substituted <;>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := substituted <;> exact ⟨rfl, rfl, rfl, nofun⟩
  | indirectCall returnType parameters hasThis explicitThis convention =>
    simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at substituted
    obtain ⟨_, _, _, _, rfl⟩ := substituted
    exact ⟨rfl, rfl, rfl, nofun⟩
  | _ =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    exact ⟨by rw [substituted], by rw [substituted], by rw [substituted],
      fun _ => substituted.symm⟩

#print axioms substituteOperand_mentionsType

end CIL.Extraction

namespace CIL

open Extraction

/-- The opcodes `Instruction.ofRaw?` decodes for some operand. -/
def Instruction.valueOpcode (opcode : Nat) : Bool :=
  opcode == 0 || (2 <= opcode && opcode <= 33) || opcode == 37 || opcode == 38 ||
    (42 <= opcode && opcode <= 77) || (82 <= opcode && opcode <= 85) ||
    (88 <= opcode && opcode <= 106) || opcode == 109 || opcode == 110 || opcode == 116 ||
    opcode == 117 || (123 <= opcode && opcode <= 125) || (130 <= opcode && opcode <= 139) ||
    (179 <= opcode && opcode <= 186) || (209 <= opcode && opcode <= 219) || opcode == 223 ||
    opcode == 224 || (65025 <= opcode && opcode <= 65029) || (65033 <= opcode && opcode <= 65039)

/-- The class type test `opcode` denotes on `type`: `castclass` (116) or `isinst` (117). -/
def Instruction.typeTest? (opcode : Nat) (type : TypeExpr) : Option Instruction :=
  if opcode == 116 then some (.castclass type) else if opcode == 117 then some (.isinst type)
  else none

/-- Only `castclass` (116) and `isinst` (117) denote a type test. -/
theorem Instruction.typeTest?_opcode {opcode : Nat} {type : TypeExpr} {instruction : Instruction}
    (tested : Instruction.typeTest? opcode type = some instruction) :
    opcode = 116 ∨ opcode = 117 := by
  unfold Instruction.typeTest? at tested
  revert tested
  cases castclass : opcode == 116
  · cases isinst : opcode == 117
    · intro tested
      first | cases tested | simp at tested
    · exact fun _ => .inr (beq_iff_eq.mp isinst)
  · exact fun _ => .inl (beq_iff_eq.mp castclass)

#print axioms Instruction.typeTest?_opcode

/-- The class field instruction `opcode` denotes on `field`: `ldfld` (123), `ldflda` (124)
    or `stfld` (125). -/
def Instruction.classField? (opcode : Nat) (field : FieldRef) : Option Instruction :=
  if opcode == 123 then some (.ldfld field) else if opcode == 124 then some (.ldflda field)
  else if opcode == 125 then some (.stfld field) else none

/-- Only `ldfld` (123), `ldflda` (124) and `stfld` (125) denote a class field instruction. -/
theorem Instruction.classField?_opcode {opcode : Nat} {field : FieldRef}
    {instruction : Instruction}
    (accessed : Instruction.classField? opcode field = some instruction) :
    opcode = 123 ∨ opcode = 124 ∨ opcode = 125 := by
  unfold Instruction.classField? at accessed
  split at accessed
  · exact .inl (beq_iff_eq.mp ‹_›)
  · split at accessed
    · exact .inr (.inl (beq_iff_eq.mp ‹_›))
    · split at accessed
      · exact .inr (.inr (beq_iff_eq.mp ‹_›))
      · cases accessed

#print axioms Instruction.classField?_opcode

/-- The instruction a value-family raw instruction denotes: one constructor per ECMA opcode,
    with short and macro forms folded into it. A type operand gives the type test its opcode
    names and an instance field of a class the field instruction its opcode names; any other
    opcode, another operand kind that instantiation rewrites, or a malformed or out-of-range
    operand gives `none`. A hole is never a decoding, so `Instruction.ofRaw` can write one where
    this admits nothing. -/
def Instruction.ofRaw? (raw : RawInstruction) : Option Instruction :=
  Option.filter (fun decoded => !(decoded matches .unadmitted _)) <|
  match raw.operand with
  | .type type => Instruction.typeTest? raw.opcode type
  | .field (.object _ _) _ _ _ false =>
    (FieldRef.ofOperand? raw.operand).bind (Instruction.classField? raw.opcode)
  | _ =>
  if raw.operand.mentionsType || !Instruction.valueOpcode raw.opcode then none else
  match raw.opcode, raw.operand with
  -- Stack shuffling and return.
  | 0, .none => some .nop
  | 37, .none => some .dup
  | 38, .none => some .pop
  | 42, .none => some .ret
  -- Constants, with the operand ranges ECMA-335 gives each form.
  | 20, .none => some .ldnull
  | 21, .none => some (.ldc_i4 (BitVec.ofInt 32 (-1)))
  | 31, .integer value =>
    if -128 <= value && value < 128 then some (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 32, .integer value =>
    if -(2^31) <= value && value < 2^31 then some (.ldc_i4 (BitVec.ofInt 32 value)) else none
  | 33, .integer value =>
    if -(2^63) <= value && value < 2^63 then some (.ldc_i8 (BitVec.ofInt 64 value)) else none
  | 22, .none | 23, .none | 24, .none | 25, .none | 26, .none | 27, .none | 28, .none
  | 29, .none | 30, .none => some (.ldc_i4 (BitVec.ofNat 32 (raw.opcode - 22)))
  -- Argument loads, addresses and stores; an index wider than its form encodes gives `none`.
  | 2, .none => some (.ldarg 0) | 3, .none => some (.ldarg 1)
  | 4, .none => some (.ldarg 2) | 5, .none => some (.ldarg 3)
  | 14, .argument index | 65033, .argument index =>
    if index < operandIndexBound raw.opcode then some (.ldarg index) else none
  | 15, .argument index | 65034, .argument index =>
    if index < operandIndexBound raw.opcode then some (.ldarga index) else none
  | 16, .argument index | 65035, .argument index =>
    if index < operandIndexBound raw.opcode then some (.starg index) else none
  -- Locals; `encodedLocal` validates the operand of every form and its width.
  | 6, _ | 7, _ | 8, _ | 9, _ | 17, _ | 65036, _ => Instruction.ldloc <$> encodedLocal raw
  | 10, _ | 11, _ | 12, _ | 13, _ | 19, _ | 65038, _ => Instruction.stloc <$> encodedLocal raw
  | 18, _ | 65037, _ => Instruction.ldloca <$> encodedLocal raw
  -- Branches, short and long forms, keep their resolved target.
  | 43, .target target | 56, .target target => some (.br target)
  | 44, .target target | 57, .target target => some (.brfalse target)
  | 45, .target target | 58, .target target => some (.brtrue target)
  | 46, .target target | 59, .target target => some (.beq target)
  | 47, .target target | 60, .target target => some (.bge target)
  | 48, .target target | 61, .target target => some (.bgt target)
  | 49, .target target | 62, .target target => some (.ble target)
  | 50, .target target | 63, .target target => some (.blt target)
  | 51, .target target | 64, .target target => some (.bne_un target)
  | 52, .target target | 65, .target target => some (.bge_un target)
  | 53, .target target | 66, .target target => some (.bgt_un target)
  | 54, .target target | 67, .target target => some (.ble_un target)
  | 55, .target target | 68, .target target => some (.blt_un target)
  | 69, .targets targets => some (.switch targets)
  -- Integer indirect loads and stores; the floating and reference kinds decode to nothing.
  | 70, .none => some (.ldind .i1) | 71, .none => some (.ldind .u1)
  | 72, .none => some (.ldind .i2) | 73, .none => some (.ldind .u2)
  | 74, .none => some (.ldind .i4) | 75, .none => some (.ldind .u4)
  | 76, .none => some (.ldind .i8) | 77, .none => some (.ldind .i)
  | 82, .none => some (.stind .i1) | 83, .none => some (.stind .i2)
  | 84, .none => some (.stind .i4) | 85, .none => some (.stind .i8)
  | 223, .none => some (.stind .i)
  -- Arithmetic, bitwise operations and shifts.
  | 88, .none => some .add | 89, .none => some .sub | 90, .none => some .mul
  | 91, .none => some .div | 92, .none => some .div_un
  | 93, .none => some .rem | 94, .none => some .rem_un
  | 95, .none => some .and | 96, .none => some .or | 97, .none => some .xor
  | 98, .none => some .shl | 99, .none => some .shr | 100, .none => some .shr_un
  | 101, .none => some .neg | 102, .none => some .not
  -- Conversions.
  | 103, .none => some .conv_i1 | 104, .none => some .conv_i2
  | 105, .none => some .conv_i4 | 106, .none => some .conv_i8
  | 109, .none => some .conv_u4 | 110, .none => some .conv_u8
  | 209, .none => some .conv_u2 | 210, .none => some .conv_u1
  | 211, .none => some .conv_i | 224, .none => some .conv_u
  -- Overflow-checked conversions from an unsigned source.
  | 130, .none => some (.conv_ovf_un .i1) | 131, .none => some (.conv_ovf_un .i2)
  | 132, .none => some (.conv_ovf_un .i4) | 133, .none => some (.conv_ovf_un .i8)
  | 134, .none => some (.conv_ovf_un .u1) | 135, .none => some (.conv_ovf_un .u2)
  | 136, .none => some (.conv_ovf_un .u4) | 137, .none => some (.conv_ovf_un .u8)
  | 138, .none => some (.conv_ovf_un .i) | 139, .none => some (.conv_ovf_un .u)
  -- Overflow-checked conversions from a signed source.
  | 179, .none => some (.conv_ovf .i1) | 180, .none => some (.conv_ovf .u1)
  | 181, .none => some (.conv_ovf .i2) | 182, .none => some (.conv_ovf .u2)
  | 183, .none => some (.conv_ovf .i4) | 184, .none => some (.conv_ovf .u4)
  | 185, .none => some (.conv_ovf .i8) | 186, .none => some (.conv_ovf .u8)
  | 212, .none => some (.conv_ovf .i) | 213, .none => some (.conv_ovf .u)
  -- Overflow-checked arithmetic.
  | 214, .none => some .add_ovf | 215, .none => some .add_ovf_un
  | 216, .none => some .mul_ovf | 217, .none => some .mul_ovf_un
  | 218, .none => some .sub_ovf | 219, .none => some .sub_ovf_un
  -- Comparisons.
  | 65025, .none => some .ceq | 65026, .none => some .cgt | 65027, .none => some .cgt_un
  | 65028, .none => some .clt | 65029, .none => some .clt_un
  -- Dynamic frame storage; whether it is zeroed is the method's localsinit flag, not an operand.
  | 65039, .none => some .localloc
  | _, _ => none

/-- `ofRaw?` decodes only the opcodes of `Instruction.valueOpcode`. -/
theorem Instruction.valueOpcode_of_ofRaw? {raw : RawInstruction} {instruction : Instruction}
    (decoded : Instruction.ofRaw? raw = some instruction) :
    Instruction.valueOpcode raw.opcode = true := by
  cases opcodeValue : Instruction.valueOpcode raw.opcode
  · unfold Instruction.ofRaw? at decoded
    split at decoded
    · rcases Instruction.typeTest?_opcode (Option.filter_eq_some_iff.mp decoded).1
        with opcodeIs | opcodeIs <;>
        rw [opcodeIs] at opcodeValue <;> exact absurd opcodeValue (by decide)
    · obtain ⟨_, _, accessed⟩ := Option.bind_eq_some_iff.mp
        (Option.filter_eq_some_iff.mp decoded).1
      rcases Instruction.classField?_opcode accessed with opcodeIs | opcodeIs | opcodeIs <;>
        rw [opcodeIs] at opcodeValue <;> exact absurd opcodeValue (by decide)
    · rw [opcodeValue, Bool.not_false, Bool.or_true,
        ite_eq_left_of_eq_true _ _ (eq_true rfl)] at decoded
      cases decoded
  · rfl

#print axioms Instruction.valueOpcode_of_ofRaw?

/-- No raw instruction decodes to a hole: a hole is what `Instruction.ofRaw` writes where
    `ofRaw?` admits nothing. -/
theorem Instruction.ofRaw?_ne_unadmitted (raw : RawInstruction) (opcode : Nat) :
    Instruction.ofRaw? raw ≠ some (.unadmitted opcode) := fun decoded =>
  Bool.false_ne_true (Option.filter_eq_some_iff.mp decoded).2

#print axioms Instruction.ofRaw?_ne_unadmitted

/-- The instruction a raw instruction denotes: its value decoding where `ofRaw?` admits one,
    and otherwise a hole carrying the raw opcode, which faults when stepped. -/
def Instruction.ofRaw (raw : RawInstruction) : Instruction :=
  (Instruction.ofRaw? raw).getD (.unadmitted raw.opcode)

/-- Decoding gives a hole exactly when `ofRaw?` admits nothing, and the hole carries the raw
    opcode; an instruction `ofRaw?` admits is never a hole. -/
theorem Instruction.ofRaw_eq_unadmitted_iff (raw : RawInstruction) (opcode : Nat) :
    Instruction.ofRaw raw = .unadmitted opcode ↔
      Instruction.ofRaw? raw = none ∧ opcode = raw.opcode := by
  unfold Instruction.ofRaw
  cases decoded : Instruction.ofRaw? raw with
  | none =>
    simp only [Option.getD_none, Instruction.unadmitted.injEq, true_and]
    exact eq_comm
  | some instruction =>
    simp only [Option.getD_some, reduceCtorEq, false_and, iff_false]
    intro hole
    subst hole
    exact Instruction.ofRaw?_ne_unadmitted raw opcode decoded

#print axioms Instruction.ofRaw_eq_unadmitted_iff

/-- An instruction `ofRaw?` admits decodes to itself. -/
theorem Instruction.ofRaw_of_ofRaw? {raw : RawInstruction} {instruction : Instruction}
    (decoded : Instruction.ofRaw? raw = some instruction) :
    Instruction.ofRaw raw = instruction := by
  rw [Instruction.ofRaw, decoded, Option.getD_some]

#print axioms Instruction.ofRaw_of_ofRaw?

/-- An opcode outside the value opcodes decodes to a hole carrying it. -/
theorem Instruction.ofRaw_of_not_valueOpcode {raw : RawInstruction}
    (outside : Instruction.valueOpcode raw.opcode = false) :
    Instruction.ofRaw raw = .unadmitted raw.opcode := by
  cases decoded : Instruction.ofRaw? raw with
  | none => rw [Instruction.ofRaw, decoded, Option.getD_none]
  | some _ =>
    rw [Instruction.valueOpcode_of_ofRaw? decoded] at outside
    cases outside

#print axioms Instruction.ofRaw_of_not_valueOpcode

/-- The instruction at `pc` of raw code as `Instruction.ofRaw` decodes it; `none` past the end
    of the code. -/
def Instruction.ofRawAt (code : List RawInstruction) (pc : Nat) : Option Instruction :=
  code[pc]?.map Instruction.ofRaw

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
  -- Type tests compare the class they test.
  | .castclass expected =>
    match emitted with | .castclass actual => expected == actual | _ => false
  | .isinst expected => match emitted with | .isinst actual => expected == actual | _ => false
  -- Class field instructions compare the field they name.
  | .ldfld expected => match emitted with | .ldfld actual => expected == actual | _ => false
  | .ldflda expected => match emitted with | .ldflda actual => expected == actual | _ => false
  | .stfld expected => match emitted with | .stfld actual => expected == actual | _ => false
  -- Dynamic frame storage.
  | .localloc => (emitted matches .localloc)
  -- Constructors outside the value family are never a decoded value.
  | _ => false

/-- A decoded value is the emitted instruction exactly when `sameValue` accepts the pair. -/
theorem Instruction.sameValue_eq {decoded emitted : Instruction}
    (same : decoded.sameValue emitted = true) : emitted = decoded := by
  cases decoded <;> simp only [Instruction.sameValue] at same
  all_goals first
    | exact absurd same Bool.false_ne_true
    | (split at same <;> simp_all)

#print axioms Instruction.sameValue_eq

/-- Instantiation changes a decoded instruction only in the type a type test names or through a
    field operand: an operand that is neither a type nor a field decodes as before, and a type
    test decodes exactly when the original does, to the test of the same opcode on the
    substituted type. -/
theorem Instruction.ofRaw?_substitute {raw : RawInstruction} {operand : RawOperand}
    {arguments : List TypeExpr} {layouts : List RawLayout} {arity : Nat}
    (substituted : substituteOperand arguments layouts arity raw.operand = some operand)
    (unnamed : FieldRef.ofOperand? raw.operand = none) :
    Instruction.ofRaw? { raw with operand } =
      match raw.operand, operand with
      | .type _, .type type =>
        (Instruction.ofRaw? raw).bind fun _ => Instruction.typeTest? raw.opcode type
      | _, _ => Instruction.ofRaw? raw := by
  obtain ⟨sameKind, sameType, sameField, unchanged⟩ := substituteOperand_mentionsType substituted
  obtain ⟨offset, opcode, original⟩ := raw
  cases original
  case field => cases unnamed
  case type before =>
    cases operand
    case type type =>
      show Option.filter _ (Instruction.typeTest? opcode type) =
        (Option.filter _ (Instruction.typeTest? opcode before)).bind fun _ =>
          Instruction.typeTest? opcode type
      unfold Instruction.typeTest?
      cases opcode == 116 <;> cases opcode == 117 <;> rfl
    all_goals exact absurd sameType Bool.false_ne_true
  -- Any other original either is unchanged or, like its substitute, is refused by the guard.
  all_goals first
    | (cases unchanged rfl <;> rfl)
    | (cases operand <;> first
        | exact absurd sameKind Bool.false_ne_true
        | exact absurd sameType.symm Bool.false_ne_true
        | exact absurd sameField Bool.false_ne_true
        | exact absurd sameField.symm Bool.false_ne_true
        | rfl)

#print axioms Instruction.ofRaw?_substitute

/-- Instantiation keeps a class field operand's owner, an object type that no argument
    replaces, and substitutes its held type; the instantiated instruction decodes to the class
    field instruction of the same opcode over the substituted reference. -/
theorem Instruction.ofRaw?_substitute_field {raw : RawInstruction} {operand : RawOperand}
    {arguments : List TypeExpr} {layouts : List RawLayout} {arity : Nat}
    {scope name : String} {index : Nat} {held : TypeExpr} {fieldName : MetadataName}
    (substituted : substituteOperand arguments layouts arity raw.operand = some operand)
    (named : raw.operand = .field (.object scope name) index held fieldName false) :
    ∃ closed, substituteStorageType layouts arguments held = some closed ∧
      operand = .field (.object scope name) index closed fieldName false ∧
      Instruction.ofRaw? { raw with operand } =
        Instruction.classField? raw.opcode
          { owner := .object scope name, index, type := closed, name := fieldName } := by
  obtain ⟨offset, opcode, original⟩ := raw
  dsimp only at named
  subst named
  simp only [substituteOperand, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at substituted
  obtain ⟨owner, closedOwner, closed, holdsClosed, rfl⟩ := substituted
  simp only [substituteStorageType, substituteType, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at closedOwner
  subst closedOwner
  refine ⟨closed, holdsClosed, rfl, ?_⟩
  show Option.filter _ (Instruction.classField? opcode _) = _
  unfold Instruction.classField?
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

#print axioms Instruction.ofRaw?_substitute_field

end CIL

namespace CIL.Extraction

/-- Whether `emitted` is exactly what `raw` decodes to. -/
def valueEncodingMatches (raw : RawInstruction) (emitted : Instruction) : Bool :=
  match Instruction.ofRaw? raw with
  | some decoded => decoded.sameValue emitted
  | none => false

/-- A matching value encoding is exactly the decoded instruction. -/
theorem valueEncodingMatches_sound {raw : RawInstruction} {emitted : Instruction}
    (matched : valueEncodingMatches raw emitted = true) :
    Instruction.ofRaw? raw = some emitted := by
  unfold valueEncodingMatches at matched
  split at matched
  · next decoded decodes => rw [decodes, Instruction.sameValue_eq matched]
  · exact absurd matched Bool.false_ne_true

#print axioms valueEncodingMatches_sound

end CIL.Extraction
