import Tests.BodyEncoding
import Tests.MetadataWorld

/-!
# Method body decoding tests

Hand-made ECMA-335 bodies with tiny and fat headers, short and long branches, a switch,
two-byte opcodes, token operands and float constants must decode to the expected `RawMethod`
fields, with every token operand, the locals and the method definition checked against the
metadata of a hand-built assembly. Each rejection changes one fact about a body that matches and
asserts the error or mismatch it causes. The opcode table is compared in
`operand_kinds_agree_with_cecil` with a static list generated once from `Mono.Cecil.Cil.OpCodes`;
no test reads Cecil at run time.
-/

namespace Tests.BodyDecoding

open CIL CIL.Extraction Tests.BodyEncoding Tests.MetadataBuilder Tests.MetadataWorld

/-- The assembly whose metadata the bodies are checked against. -/
private def pin : AssemblyPin := { identity := ownIdentity }

/-- A decoded method with the given body fields: the world's `Main`, a public static method
    with no parameters. -/
private def method (maxStack : Nat) (initLocals : Bool) (locals : List TypeExpr)
    (code : List RawInstruction) : RawMethod :=
  { token := tokens.main, owner := ownIdentity ++ "::Program", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0x96, implementation := 0,
    returnType := .void, parameters := [], locals := locals, initLocals := initLocals,
    maxStack := maxStack, genericParameters := [], code := code }

/-- A body with the given bytes and token claims, with the metadata of the world's `Main`; its
    names are those of every test method, which all sit in `Main`'s class. -/
private def evidence (bytes : List Nat) (operands : List (Nat × RawOperand) := []) :
    BodyEvidence :=
  evidenceOf bytes operands { own := own.1, others := [lib] } (method 8 false [] [])

/-- One decoded instruction. -/
private def instr (offset opcode : Nat) (operand : RawOperand := .none) : RawInstruction :=
  { offset := offset, opcode := opcode, operand := operand }

/-- The four little-endian bytes of a token. -/
private def token (value : Nat) : List Nat := (Tests.BodyEncoding.littleEndian 4 value)

/-! ## Bodies that decode -/

/-- Tiny body: `ldarg.0; ldarg.1; add; ret`. -/
private def tinyBytes : List Nat := [0x12, 0x02, 0x03, 0x58, 0x2A]

/-- The decoded `tinyBytes`; a tiny header fixes the stack depth at 8 and has no locals. -/
private def tinyMethod : RawMethod :=
  method 8 false [] [instr 0 0x02, instr 1 0x03, instr 2 0x58, instr 3 0x2A]

theorem tiny_header_decodes : bodyMatches (evidence tinyBytes) tinyMethod [] = true := by
  decide +kernel
#print axioms tiny_header_decodes

/-- Fat body with one local: `ldc.i4.s -3; stloc.0; ldloc.s 0; ldc.i4 1000; add; ret`. -/
private def fatBytes : List Nat :=
  [0x13, 0x30, 0x02, 0x00, 12, 0, 0, 0, 0x01, 0x00, 0x00, 0x11,
   0x1F, 0xFD, 0x0A, 0x11, 0x00, 0x20, 0xE8, 0x03, 0x00, 0x00, 0x58, 0x2A]

/-- The decoded `fatBytes`: the signed byte, the macro `stloc.0` and the short local index. -/
private def fatMethod : RawMethod :=
  method 2 true [uint64] [instr 0 0x1F (.integer (-3)), instr 2 0x0A, instr 3 0x11 (.local 0),
    instr 5 0x20 (.integer 1000), instr 10 0x58, instr 11 0x2A]

/-- `fatBytes`, whose signature token `0x11000001` names the world's one `uint64` local. -/
private def fatEvidence : BodyEvidence := evidence fatBytes

theorem fat_header_decodes : bodyMatches fatEvidence fatMethod [] = true := by decide +kernel
#print axioms fat_header_decodes

/-- Short and long branches, forward and backward; targets are instruction indices. -/
private def branchBytes : List Nat :=
  [0x3A, 0x02, 0x2C, 0x04, 0x17, 0x2A, 0x2B, 0xFD, 0x16, 0x38, 0xF3, 0xFF, 0xFF, 0xFF, 0x2A]

/-- The decoded `branchBytes`: short and long forms, with indices in place of byte offsets. -/
private def branchMethod : RawMethod :=
  method 8 false [] [instr 0 0x02, instr 1 0x2C (.target 5), instr 3 0x17, instr 4 0x2A,
    instr 5 0x2B (.target 3), instr 7 0x16, instr 8 0x38 (.target 0), instr 13 0x2A]

theorem branches_decode_to_instruction_indices :
    bodyMatches (evidence branchBytes) branchMethod [] = true := by decide +kernel
#print axioms branches_decode_to_instruction_indices

/-- A `switch` whose targets are measured from the end of its table. -/
private def switchBytes : List Nat :=
  [0x52, 0x02, 0x45, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0xEF, 0xFF, 0xFF, 0xFF, 0x2A, 0x2A]

/-- The decoded `switchBytes`: the case targets are instruction indices. -/
private def switchMethod : RawMethod :=
  method 8 false [] [instr 0 0x02, instr 1 0x45 (.targets [2, 3, 1]), instr 18 0x2A, instr 19 0x2A]

theorem switch_decodes_to_instruction_indices :
    bodyMatches (evidence switchBytes) switchMethod [] = true := by decide +kernel
#print axioms switch_decodes_to_instruction_indices

/-- Two-byte opcodes `0xFE nn`: `ceq`, a long local and the unsigned `unaligned.` prefix. -/
private def twoByteBytes : List Nat :=
  [0x36, 0x02, 0x03, 0xFE, 0x01, 0xFE, 0x0D, 0x05, 0x00, 0xFE, 0x12, 0xFF, 0x2A, 0x2A]

/-- The decoded `twoByteBytes`. -/
private def twoByteMethod : RawMethod :=
  method 8 false [] [instr 0 0x02, instr 1 0x03, instr 2 0xFE01, instr 4 0xFE0D (.local 5),
    instr 8 0xFE12 (.integer 255), instr 11 0x2A, instr 12 0x2A]

theorem two_byte_opcodes_decode :
    bodyMatches (evidence twoByteBytes) twoByteMethod [] = true := by decide +kernel
#print axioms two_byte_opcodes_decode

/-- A method token, a user string, a type token, and float constants of both widths:
    `throw; call; ldstr; ldtoken; ldc.r4; ldc.r8; ret`. -/
private def tokenBytes : List Nat :=
  [0x7A, 0x28] ++ token tokens.writeLine ++ [0x72] ++ token tokens.hello ++ [0xD0] ++
    token tokens.objectRef ++ [0x22, 0x00, 0x00, 0x80, 0xBF, 0x23, 0, 0, 0, 0, 0, 0, 0, 0xC0, 0x2A]

/-- The system type `ldtoken` names in `tokenBytes`. -/
private def objectType : TypeExpr := .atom runtimeScope "System.Object"

/-- The token table of `tokenBytes`: a method, a user string and a type. -/
private def tokenOperands : List (Nat × RawOperand) :=
  [(tokens.writeLine, .call writeLineSite), (tokens.hello, .text "hi"),
   (tokens.objectRef, .type objectType)]

/-- The decoded `tokenBytes`; float constants are the bit patterns of the encoded values. -/
private def tokenMethod : RawMethod :=
  method 8 false [] [instr 0 0x28 (.call writeLineSite), instr 5 0x72 (.text "hi"),
    instr 10 0xD0 (.type objectType), instr 15 0x22 (.text "float:-1082130432"),
    instr 20 0x23 (.text "double:-4611686018427387904"),
    instr 29 0x2A]

theorem token_operands_resolve_through_the_table :
    bodyMatches (evidence tokenBytes tokenOperands) tokenMethod [] = true := by decide +kernel
#print axioms token_operands_resolve_through_the_table

/-- The other operand encodings: long argument, `ldc.i8`, `no.`, `calli`, an instance field and
    `ldtoken` of a method and of a static field. -/
private def formsBytes : List Nat :=
  [0x9E, 0xFE, 0x09, 0x03, 0x00, 0x0E, 0x02, 0x21, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFE, 0x19, 0x07, 0x29] ++ token tokens.indirect ++ [0x7B] ++ token tokens.countField ++
    [0xD0] ++ token tokens.writeLine ++ [0xD0] ++ token tokens.totalField ++ [0x2A]

/-- The instance field `ldfld` names in `formsBytes`. -/
private def someField : RawOperand := countOperand

/-- The static field `ldtoken` names in `formsBytes`. -/
private def staticField : RawOperand := .field (.atom ownIdentity "Program") 1 int32 true

/-- The signature `calli` names in `formsBytes`. -/
private def someSignature : RawOperand := .indirectCall .void [int32] false false 0

/-- The token table of `formsBytes`. -/
private def formsOperands : List (Nat × RawOperand) :=
  [(tokens.indirect, someSignature), (tokens.countField, someField),
   (tokens.writeLine, .call writeLineSite), (tokens.totalField, staticField)]

/-- The decoded `formsBytes`. -/
private def formsMethod : RawMethod :=
  method 8 false [] [instr 0 0xFE09 (.argument 3), instr 4 0x0E (.argument 2),
    instr 6 0x21 (.integer (-2)), instr 15 0xFE19 (.integer 7), instr 18 0x29 someSignature,
    instr 23 0x7B someField, instr 28 0xD0 (.call writeLineSite), instr 33 0xD0 staticField,
    instr 38 0x2A]

theorem other_operand_forms_decode :
    bodyMatches (evidence formsBytes formsOperands) formsMethod [] = true := by decide +kernel
#print axioms other_operand_forms_decode

/-- A branch to a `volatile.` prefix enters the prefixed instruction at its first prefix. -/
theorem branch_to_a_prefix_decodes :
    bodyMatches (evidence [0x1A, 0x2B, 0x00, 0xFE, 0x13, 0x4A, 0x2A])
      (method 8 false [] [instr 0 0x2B (.target 1), instr 2 0xFE13, instr 4 0x4A,
        instr 5 0x2A]) [] = true := by decide +kernel
#print axioms branch_to_a_prefix_decodes

/-! ## The test encoder agrees with the hand-written bytes -/

/-- The encoder writes the bytes written out by hand above, and the metadata it writes makes the
    body decode to the method. -/
theorem encoder_reproduces_the_hand_written_bodies :
    (encodeBody pin tinyMethod).map (·.bytes) = some tinyBytes ∧
    (encodeBody pin fatMethod).map (·.bytes) = some fatBytes ∧
    (encodeBody pin branchMethod).map (·.bytes) = some branchBytes ∧
    (encodeBody pin switchMethod).map (·.bytes) = some switchBytes ∧
    (encodeBody pin twoByteMethod).map (·.bytes) = some twoByteBytes ∧
    (encodeBody pin tinyMethod).any (bodyMatches · tinyMethod []) = true ∧
    (encodeBody pin fatMethod).any (bodyMatches · fatMethod []) = true ∧
    (encodeBody pin twoByteMethod).any (bodyMatches · twoByteMethod []) = true := by
  decide +kernel
#print axioms encoder_reproduces_the_hand_written_bodies

/-! ## Bodies that must not match -/

/-- A method that every test body is checked against unless the test names another. -/
private def plain : RawMethod := method 8 false [] []

/-- Whether the body fails to decode with exactly this error. -/
private def failsWith (body : BodyEvidence) (error : BodyError) (method : RawMethod := plain) :
    Bool :=
  match checkBody body method [] with
  | .error found => found == error
  | .ok _ => false

/-- Whether the body decodes but to something other than the method: the failure is the
    mismatch, not a decoding error. -/
private def mismatches (body : BodyEvidence) (method : RawMethod) : Bool :=
  match checkBody body method [] with
  | .ok _ => !bodyMatches body method []
  | .error _ => false

/-- One opcode byte changed: `sub` where the decoded method says `add`. -/
theorem rejects_changed_opcode_byte :
    mismatches (evidence [0x12, 0x02, 0x03, 0x59, 0x2A]) tinyMethod = true := by decide +kernel
#print axioms rejects_changed_opcode_byte

/-- One operand byte changed: the signed byte is -4 where the decoded method says -3. -/
theorem rejects_changed_operand_byte :
    mismatches (evidence (fatBytes.set 13 0xFC)) fatMethod = true := by decide +kernel
#print axioms rejects_changed_operand_byte

/-- A decoded instruction with a wrong byte offset. -/
theorem rejects_wrong_instruction_offset :
    mismatches (evidence tinyBytes)
      (method 8 false [] [instr 0 0x02, instr 1 0x03, instr 3 0x58, instr 3 0x2A]) = true := by
  decide +kernel
#print axioms rejects_wrong_instruction_offset

/-- A decoded branch naming another instruction index than its bytes reach. -/
theorem rejects_wrong_branch_index :
    mismatches (evidence branchBytes)
      (method 8 false [] [instr 0 0x02, instr 1 0x2C (.target 6), instr 3 0x17, instr 4 0x2A,
        instr 5 0x2B (.target 3), instr 7 0x16, instr 8 0x38 (.target 0), instr 13 0x2A]) =
      true := by
  decide +kernel
#print axioms rejects_wrong_branch_index

/-- `brfalse.s` to byte 1, its own operand: no instruction starts there. -/
private def midInstructionBytes : List Nat := [0x0E, 0x2C, 0xFF, 0x2A]

theorem rejects_branch_into_an_instruction :
    failsWith (evidence midInstructionBytes) (.branchIntoInstruction 0 1) = true := by
  decide +kernel
#print axioms rejects_branch_into_an_instruction

/-- The check is `false` for the same body, whatever instructions the method claims. -/
theorem branch_into_an_instruction_does_not_match :
    bodyMatches (evidence midInstructionBytes)
      (method 8 false [] [instr 0 0x2C (.target 1), instr 2 0x2A]) [] = false := by
  decide +kernel
#print axioms branch_into_an_instruction_does_not_match

/-- A branch to the end of the code reaches no instruction. -/
theorem rejects_branch_to_the_end_of_the_body :
    failsWith (evidence [0x0E, 0x2B, 0x01, 0x2A]) (.branchOutsideBody 0) = true := by
  decide +kernel
#print axioms rejects_branch_to_the_end_of_the_body

/-- A branch past the end of the code. -/
theorem rejects_branch_past_the_body :
    failsWith (evidence [0x0E, 0x2B, 0x05, 0x2A]) (.branchOutsideBody 0) = true := by
  decide +kernel
#print axioms rejects_branch_past_the_body

/-- A branch before the first byte. -/
theorem rejects_branch_before_the_body :
    failsWith (evidence [0x0A, 0x2B, 0xF0]) (.branchOutsideBody 0) = true := by decide +kernel
#print axioms rejects_branch_before_the_body

/-- A branch to the instruction after a `volatile.` prefix: control may enter a prefixed
    instruction only at its first prefix. -/
theorem rejects_branch_to_the_instruction_after_a_prefix :
    failsWith (evidence [0x1A, 0x2B, 0x02, 0xFE, 0x13, 0x4A, 0x2A]) (.branchIntoPrefixed 0 4) =
      true := by
  decide +kernel
#print axioms rejects_branch_to_the_instruction_after_a_prefix

/-- A `switch` case that reaches the instruction after a `readonly.` prefix. -/
theorem rejects_switch_target_after_a_prefix :
    failsWith (evidence [0x36, 0x45, 0x01, 0, 0, 0, 0x03, 0, 0, 0, 0x2A, 0xFE, 0x1E, 0x2A])
      (.branchIntoPrefixed 0 12) = true := by
  decide +kernel
#print axioms rejects_switch_target_after_a_prefix

/-- The table resolves a token to another operand than the metadata names: the call has a
    parameter more than the member the token names. -/
theorem rejects_token_with_different_operand :
    failsWith (evidence tokenBytes
        [(tokens.writeLine, .call { writeLineSite with parameterCount := 2 }),
         (tokens.hello, .text "hi"), (tokens.objectRef, .type objectType)])
      (.metadata (.operandMismatch tokens.writeLine)) = true := by decide +kernel
#print axioms rejects_token_with_different_operand

/-- A token missing from the table fails the check. -/
theorem rejects_missing_token :
    failsWith (evidence tokenBytes [(tokens.writeLine, .call writeLineSite),
      (tokens.hello, .text "hi")]) (.missingToken 10 tokens.objectRef) = true := by
  decide +kernel
#print axioms rejects_missing_token

/-- A call whose token names a type reference, which the table resolves to a type: the entry
    matches its metadata, so the failure is the table of the token. -/
theorem rejects_method_operand_from_the_wrong_table :
    failsWith (evidence ([0x16, 0x28] ++ token tokens.objectRef)
        [(tokens.objectRef, .type objectType)]) (.mismatchedToken 0 tokens.objectRef) = true := by
  decide +kernel
#print axioms rejects_method_operand_from_the_wrong_table

/-- A user-string operand whose token names a type reference. -/
theorem rejects_string_operand_from_the_wrong_table :
    failsWith (evidence ([0x16, 0x72] ++ token tokens.objectRef)
        [(tokens.objectRef, .type objectType)]) (.mismatchedToken 0 tokens.objectRef) = true := by
  decide +kernel
#print axioms rejects_string_operand_from_the_wrong_table

/-- A token the table resolves to an operand the opcode cannot take. -/
theorem rejects_token_with_the_wrong_operand_kind :
    failsWith (evidence ([0x16, 0x28] ++ token tokens.hello) [(tokens.hello, .text "hi")])
      (.mismatchedToken 0 tokens.hello) = true := by
  decide +kernel
#print axioms rejects_token_with_the_wrong_operand_kind

/-- `ldsfld` of a token that names an instance field. -/
theorem rejects_a_static_load_of_an_instance_field :
    failsWith (evidence ([0x16, 0x7E] ++ token tokens.countField)
      [(tokens.countField, someField)]) (.mismatchedToken 0 tokens.countField) = true := by
  decide +kernel
#print axioms rejects_a_static_load_of_an_instance_field

/-- A token that has two entries in the table. -/
theorem rejects_a_token_with_two_entries :
    failsWith (evidence tokenBytes (tokenOperands ++ [(tokens.hello, .text "hi")]))
      (.duplicateToken tokens.hello) = true := by decide +kernel
#print axioms rejects_a_token_with_two_entries

/-- The last operand byte is missing although the header agrees with the bytes. -/
theorem rejects_truncated_operand :
    failsWith (evidence [0x0E, 0x20, 0x01, 0x00]) (.truncatedOperand 0) = true := by
  decide +kernel
#print axioms rejects_truncated_operand

/-- A byte missing from the end leaves the declared code size unmet. -/
theorem rejects_truncated_bytes :
    failsWith (evidence [0x12, 0x02, 0x03, 0x58]) (.codeSizeMismatch 4 3) = true := by
  decide +kernel
#print axioms rejects_truncated_bytes

/-- A fat header cut short. -/
theorem rejects_truncated_header :
    failsWith (evidence [0x13, 0x30, 0x02, 0x00]) .truncatedHeader = true := by decide +kernel
#print axioms rejects_truncated_header

/-- A fat header whose size is four words. -/
theorem rejects_a_fat_header_of_four_words :
    failsWith (evidence [0x03, 0x40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (.unsupportedHeader 3) =
      true := by
  decide +kernel
#print axioms rejects_a_fat_header_of_four_words

/-- A fat header with a reserved flag bit. -/
theorem rejects_a_reserved_header_flag :
    failsWith (evidence [0x23, 0x30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (.unsupportedHeader 35) =
      true := by
  decide +kernel
#print axioms rejects_a_reserved_header_flag

/-- A declared code size that is not the number of code bytes. -/
theorem rejects_wrong_code_size :
    failsWith (evidence [0x16, 0x02, 0x03, 0x58, 0x2A]) (.codeSizeMismatch 5 4) = true := by
  decide +kernel
#print axioms rejects_wrong_code_size

/-- The method claims another stack depth than the header declares. -/
theorem rejects_wrong_max_stack :
    mismatches fatEvidence { fatMethod with maxStack := 3 } = true := by decide +kernel
#print axioms rejects_wrong_max_stack

/-- The header sets the init-locals flag and the method claims it clear. -/
theorem rejects_init_locals_claimed_clear :
    mismatches fatEvidence { fatMethod with initLocals := false } = true := by decide +kernel
#print axioms rejects_init_locals_claimed_clear

/-- The tiny header has no init-locals flag and the method claims it set. -/
theorem rejects_init_locals_claimed_set :
    mismatches (evidence tinyBytes) { tinyMethod with initLocals := true } = true := by
  decide +kernel
#print axioms rejects_init_locals_claimed_set

/-- A fat header whose flags also set the extra-sections bit, as a body with handlers does. -/
theorem rejects_body_with_exception_section :
    failsWith (evidence (0x1B :: fatBytes.tail)) .extraSections fatMethod = true := by
  decide +kernel
#print axioms rejects_body_with_exception_section

/-- A body with an exception section does not match the method that has the same code. -/
theorem body_with_exception_section_does_not_match :
    bodyMatches (evidence (0x1B :: fatBytes.tail)) fatMethod [] = false := by
  decide +kernel
#print axioms body_with_exception_section_does_not_match

/-- The method's locals differ from the types the signature token names. -/
theorem rejects_wrong_locals :
    failsWith fatEvidence (.metadata (.localMismatch 0)) { fatMethod with locals := [] } = true ∧
    failsWith fatEvidence (.metadata (.localMismatch 0)) { fatMethod with locals := [uint32] } =
      true := by decide +kernel
#print axioms rejects_wrong_locals

/-- The header names a standalone signature that is not a local variable signature. -/
theorem rejects_a_local_signature_token_that_names_a_call_signature :
    failsWith (evidence (fatBytes.set 8 0x02)) (.metadata (.unsupportedSignature 0 0)) fatMethod =
      true := by
  decide +kernel
#print axioms rejects_a_local_signature_token_that_names_a_call_signature

/-- A tiny header names no locals, so a method that claims some is refused. -/
theorem rejects_locals_without_a_signature :
    failsWith (evidence tinyBytes) (.metadata (.localMismatch 0))
      { tinyMethod with locals := [int32] } = true := by
  decide +kernel
#print axioms rejects_locals_without_a_signature

/-- A method whose attributes differ from its `MethodDef` row. -/
theorem rejects_a_method_with_other_attributes :
    failsWith (evidence tinyBytes) (.metadata (.methodMismatch tokens.main))
      { tinyMethod with attributes := 0x97 } = true := by decide +kernel
#print axioms rejects_a_method_with_other_attributes

/-- A pin of another version than the method's own assembly states: `BodyDecodes` equates the
    two strings, so the pin the method is attributed to must be the assembly its rows came from. -/
theorem rejects_a_pin_of_another_version :
    (evidence tinyBytes).metadata.own.assembly.identity ≠
      "T, Version=2.0.0.0, Culture=neutral, PublicKeyToken=null" := by decide
#print axioms rejects_a_pin_of_another_version

/-- Names the metadata does not resolve to: the body check refuses an owner or base class the
    evidence lists that the rows do not give. -/
theorem rejects_names_the_metadata_does_not_give :
    failsWith { evidence tinyBytes with names := { owner := [65] } }
      (.metadata (.methodMismatch tokens.main)) tinyMethod = true ∧
    failsWith { evidence tinyBytes with
        names := { (evidence tinyBytes).names with bases := [([65], [66])] } }
      (.metadata (.methodMismatch tokens.main)) tinyMethod = true := by decide +kernel
#print axioms rejects_names_the_metadata_does_not_give

/-- The names the metadata gives are tied to the strings the method states: another owner string
    is not what the bytes spell. -/
theorem rejects_an_owner_string_the_names_do_not_spell :
    ¬ (evidence tinyBytes).names.Spell { tinyMethod with owner := ownIdentity ++ "::Other" } := by
  decide
#print axioms rejects_an_owner_string_the_names_do_not_spell

/-- Byte `0x24` is not an opcode. -/
theorem rejects_unknown_opcode :
    failsWith (evidence [0x06, 0x24]) (.unknownOpcode 0 0x24) = true := by decide +kernel
#print axioms rejects_unknown_opcode

/-- A prefix byte `0xFE` with nothing after it. -/
theorem rejects_dangling_prefix :
    failsWith (evidence [0x06, 0xFE]) (.truncatedOpcode 0) = true := by decide +kernel
#print axioms rejects_dangling_prefix

/-- A `switch` that declares `0xFFFFFFFF` cases and carries none. -/
theorem rejects_a_switch_without_its_cases :
    failsWith (evidence [0x16, 0x45, 0xFF, 0xFF, 0xFF, 0xFF]) (.truncatedOperand 0) = true := by
  decide +kernel
#print axioms rejects_a_switch_without_its_cases

/-- Only bytes can be body bytes. -/
theorem rejects_a_value_above_255 :
    failsWith (evidence [0x06, 0x100]) .invalidByte = true := by decide +kernel
#print axioms rejects_a_value_above_255
/-! ## The opcode table -/

/-- Every opcode of `Mono.Cecil.Cil.OpCodes`, listed once from Cecil's table, with the operand
    encoding its operand type implies: `InlineNone` is `.none`, `ShortInlineI` is `.signed8`
    for `ldc.i4.s` and `.unsigned8` for `unaligned.` and `no.`, and so on. -/
private def cecilOpcodes : List (Nat × OperandKind) := [
  (0x00, .none), (0x01, .none), (0x02, .none), (0x03, .none),
  (0x04, .none), (0x05, .none), (0x06, .none), (0x07, .none),
  (0x08, .none), (0x09, .none), (0x0A, .none), (0x0B, .none),
  (0x0C, .none), (0x0D, .none), (0x0E, .shortArgument), (0x0F, .shortArgument),
  (0x10, .shortArgument), (0x11, .shortLocal), (0x12, .shortLocal), (0x13, .shortLocal),
  (0x14, .none), (0x15, .none), (0x16, .none), (0x17, .none),
  (0x18, .none), (0x19, .none), (0x1A, .none), (0x1B, .none),
  (0x1C, .none), (0x1D, .none), (0x1E, .none), (0x1F, .signed8),
  (0x20, .signed32), (0x21, .signed64), (0x22, .float32), (0x23, .float64),
  (0x25, .none), (0x26, .none), (0x27, .method), (0x28, .method),
  (0x29, .signature), (0x2A, .none), (0x2B, .shortBranch), (0x2C, .shortBranch),
  (0x2D, .shortBranch), (0x2E, .shortBranch), (0x2F, .shortBranch), (0x30, .shortBranch),
  (0x31, .shortBranch), (0x32, .shortBranch), (0x33, .shortBranch), (0x34, .shortBranch),
  (0x35, .shortBranch), (0x36, .shortBranch), (0x37, .shortBranch), (0x38, .longBranch),
  (0x39, .longBranch), (0x3A, .longBranch), (0x3B, .longBranch), (0x3C, .longBranch),
  (0x3D, .longBranch), (0x3E, .longBranch), (0x3F, .longBranch), (0x40, .longBranch),
  (0x41, .longBranch), (0x42, .longBranch), (0x43, .longBranch), (0x44, .longBranch),
  (0x45, .switch), (0x46, .none), (0x47, .none), (0x48, .none),
  (0x49, .none), (0x4A, .none), (0x4B, .none), (0x4C, .none),
  (0x4D, .none), (0x4E, .none), (0x4F, .none), (0x50, .none),
  (0x51, .none), (0x52, .none), (0x53, .none), (0x54, .none),
  (0x55, .none), (0x56, .none), (0x57, .none), (0x58, .none),
  (0x59, .none), (0x5A, .none), (0x5B, .none), (0x5C, .none),
  (0x5D, .none), (0x5E, .none), (0x5F, .none), (0x60, .none),
  (0x61, .none), (0x62, .none), (0x63, .none), (0x64, .none),
  (0x65, .none), (0x66, .none), (0x67, .none), (0x68, .none),
  (0x69, .none), (0x6A, .none), (0x6B, .none), (0x6C, .none),
  (0x6D, .none), (0x6E, .none), (0x6F, .method), (0x70, .type),
  (0x71, .type), (0x72, .string), (0x73, .method), (0x74, .type),
  (0x75, .type), (0x76, .none), (0x79, .type), (0x7A, .none),
  (0x7B, .field), (0x7C, .field), (0x7D, .field), (0x7E, .field),
  (0x7F, .field), (0x80, .field), (0x81, .type), (0x82, .none),
  (0x83, .none), (0x84, .none), (0x85, .none), (0x86, .none),
  (0x87, .none), (0x88, .none), (0x89, .none), (0x8A, .none),
  (0x8B, .none), (0x8C, .type), (0x8D, .type), (0x8E, .none),
  (0x8F, .type), (0x90, .none), (0x91, .none), (0x92, .none),
  (0x93, .none), (0x94, .none), (0x95, .none), (0x96, .none),
  (0x97, .none), (0x98, .none), (0x99, .none), (0x9A, .none),
  (0x9B, .none), (0x9C, .none), (0x9D, .none), (0x9E, .none),
  (0x9F, .none), (0xA0, .none), (0xA1, .none), (0xA2, .none),
  (0xA3, .type), (0xA4, .type), (0xA5, .type), (0xB3, .none),
  (0xB4, .none), (0xB5, .none), (0xB6, .none), (0xB7, .none),
  (0xB8, .none), (0xB9, .none), (0xBA, .none), (0xC2, .type),
  (0xC3, .none), (0xC6, .type), (0xD0, .token), (0xD1, .none),
  (0xD2, .none), (0xD3, .none), (0xD4, .none), (0xD5, .none),
  (0xD6, .none), (0xD7, .none), (0xD8, .none), (0xD9, .none),
  (0xDA, .none), (0xDB, .none), (0xDC, .none), (0xDD, .longBranch),
  (0xDE, .shortBranch), (0xDF, .none), (0xE0, .none), (0xFE00, .none),
  (0xFE01, .none), (0xFE02, .none), (0xFE03, .none), (0xFE04, .none),
  (0xFE05, .none), (0xFE06, .method), (0xFE07, .method), (0xFE09, .longArgument),
  (0xFE0A, .longArgument), (0xFE0B, .longArgument), (0xFE0C, .longLocal), (0xFE0D, .longLocal),
  (0xFE0E, .longLocal), (0xFE0F, .none), (0xFE11, .none), (0xFE12, .unsigned8),
  (0xFE13, .none), (0xFE14, .none), (0xFE15, .type), (0xFE16, .type),
  (0xFE17, .none), (0xFE18, .none), (0xFE19, .unsigned8), (0xFE1A, .none),
  (0xFE1C, .type), (0xFE1D, .none), (0xFE1E, .none)
]

/-- The opcodes that have an operand encoding: every one-byte value and every `0xFE nn`. -/
private def candidates : List Nat := List.range 256 ++ (List.range 256).map (0xFE00 + ·)

theorem operand_kinds_agree_with_cecil :
    cecilOpcodes.all (fun (opcode, kind) => operandKind opcode == some kind) = true ∧
    (candidates.filter fun opcode => (operandKind opcode).isSome).length =
      cecilOpcodes.length := by
  decide +kernel
#print axioms operand_kinds_agree_with_cecil

end Tests.BodyDecoding
