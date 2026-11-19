import CIL.Extraction.Generics

/-!
# Instruction prefixes and branch entry

A prefix modifies the instruction after it, so ECMA-335 forbids a branch into that instruction.
`PrefixEntryFree` states the rule for every pc of raw code, live or not. Body decoding refuses
such a branch, so the code of every method with body evidence satisfies it
(`checkBody_prefixEntryFree`, `MethodEvidenceValid.prefixEntryFree`) and the evidence check
decides nothing more. Raw construction checks branch destinations and prefix structure in the
same walk with `rawPrefixesValid`. Shape evidence checks the prefix operand and taker. A tail
transfer also requires the enclosing return type and the adjacent return.
-/

namespace CIL.Extraction

/-- The address alignment of an aligned block instruction or runtime helper, in bytes. -/
def defaultBlockAlignment : Nat := 8

/-- The opcodes that prefix the instruction after them: `unaligned.`, `volatile.`, `tail.`,
    `constrained.`, `no.` and `readonly.`, all between `0xFE12` and `0xFE1E`. -/
def isPrefixOpcode (opcode : Nat) : Bool :=
  0xFE12 <= opcode && opcode <= 0xFE1E &&
    (opcode == 0xFE12 || opcode == 0xFE13 || opcode == 0xFE14 || opcode == 0xFE16 ||
      opcode == 0xFE19 || opcode == 0xFE1E)

/-- A modeled unaligned access with the operand its opcode encodes. -/
def unalignedTaker (raw : RawInstruction) : Bool :=
  match raw.operand with
  | .none => (70 ≤ raw.opcode && raw.opcode ≤ 77) || (82 ≤ raw.opcode && raw.opcode ≤ 85) ||
      raw.opcode == 223 || raw.opcode == 65047 || raw.opcode == 65048
  | .field _ _ _ _ false => raw.opcode == 123 || raw.opcode == 125
  | .type _ => raw.opcode == 113 || raw.opcode == 129
  | _ => false

/-- The alignment in bytes specified by a well-formed `unaligned.` operand. -/
def prefixAlignment : RawOperand → Option Nat
  | .integer 1 => some 1
  | .integer 2 => some 2
  | .integer 4 => some 4
  | _ => none

/-- The call opcode for a constrained instance or static slot. -/
def constrainedCallOpcode (site : CallSite) : Nat := if site.hasThis then 111 else 40

/-- Whether the model admits the prefix operand and the immediately following instruction.
    Volatile accesses and suppressed runtime checks have no modeled form. -/
def prefixTakes (modifier next : RawInstruction) : Bool :=
  match modifier.opcode, modifier.operand with
  | 0xFE12, operand => (prefixAlignment operand).isSome && unalignedTaker next
  | 0xFE13, _ | 0xFE19, _ => false
  | 0xFE14, .none => match next.opcode, next.operand with
    | 40, .call _ | 41, .indirectCall .. => true
    | 111, .call site => site.hasThis
    | _, _ => false
  | 0xFE16, .type _ => match next.operand with
    | .call site => next.opcode == constrainedCallOpcode site &&
      (site.hasThis || site.staticVirtualInterfaceSlot)
    | _ => false
  | 0xFE1E, .none => next.opcode == 143 && (next.operand matches .type _)
  | _, _ => false

/-- The preceding instruction carries a modifier that the current instruction cannot take. -/
def invalidPredecessor (previous : Option RawInstruction) (raw : RawInstruction) : Bool :=
  previous.any fun before => isPrefixOpcode before.opcode && !prefixTakes before raw

/-- A tail transfer returns the method's result and ends at an adjacent operandless return. -/
private def tailResultValid (result : TypeExpr) (rest : List RawInstruction) : Bool :=
  match rest with
  | call :: ⟨_, 42, .none⟩ :: _ => match call.operand with
    | .call site => site.returnType == result
    | .indirectCall returned .. => returned == result
    | _ => false
  | _ => false

/-- Each modifier takes the next instruction, and a tail transfer returns the enclosing result.
    Raw construction also checks each instruction's branch operands during this walk. -/
def prefixSequenceValid (result : TypeExpr) (code : List RawInstruction)
    (entriesValid : RawInstruction → Bool := fun _ => true) : Bool :=
  match code with
  | [] => true
  | instruction :: rest =>
    entriesValid instruction && (!isPrefixOpcode instruction.opcode ||
      (rest.head?.any (prefixTakes instruction) &&
        (instruction.opcode != 0xFE14 || tailResultValid result rest))) &&
      prefixSequenceValid result rest entriesValid

/-- No branch or switch of the code enters the instruction after a prefix; a branch to the
    prefix itself stays allowed. -/
def PrefixEntryFree (code : List RawInstruction) : Prop :=
  ∀ pc instruction, code[pc]? = some instruction → isPrefixOpcode instruction.opcode = true →
    code.any (branchesTo (pc + 1)) = false

/-- A branch may enter the first pc or any pc without a prefix immediately before it. -/
private def entryAllowed (code : Array RawInstruction) : Nat → Bool
  | 0 => true
  | pc + 1 => !(indexedRead? code pc).any (isPrefixOpcode ·.opcode)

/-- Every destination of the instruction satisfies the given entry rule. -/
private def branchEntriesValid (allowed : Nat → Bool) (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .target target => allowed target
  | .targets targets => targets.all allowed
  | _ => true

/-- The combined walk checks prefix structure and all branch and switch operands. -/
theorem prefixSequenceValid_eq (result : TypeExpr) (code : List RawInstruction)
    (allowed : Nat → Bool) :
    prefixSequenceValid result code (branchEntriesValid allowed) =
      (prefixSequenceValid result code && (branchTargets code).all allowed) := by
  induction code with
  | nil => rfl
  | cons first rest ih =>
    have entries : (branchTargets (first :: rest)).all allowed =
        (branchEntriesValid allowed first && (branchTargets rest).all allowed) := by
      cases first with
      | mk offset opcode operand =>
        cases operand <;> simp [branchTargets, branchEntriesValid]
    simp only [prefixSequenceValid, ih, entries, Bool.true_and]
    ac_rfl
#print axioms prefixSequenceValid_eq

/-- Looking up each destination's preceding instruction decides prefix-entry freedom. -/
theorem prefixEntryFree_iff (code : List RawInstruction) :
    (branchTargets code).all (entryAllowed code.toArray) = true ↔ PrefixEntryFree code := by
  rw [List.all_eq_true]
  constructor
  · intro clear pc instruction found isPrefix
    rw [← branchTargets_contains, Bool.eq_false_iff]
    intro contains
    have blocked := clear _ (List.contains_iff_mem.mp contains)
    simp [entryAllowed, indexedRead?_eq, found, isPrefix] at blocked
  · intro free target member
    cases target with
    | zero => rfl
    | succ pc =>
      simp only [entryAllowed, indexedRead?_eq, List.getElem?_toArray]
      cases found : code[pc]? with
      | none => rfl
      | some instruction =>
        simp only [Option.any_some, Bool.not_eq_true', Bool.eq_false_iff]
        intro isPrefix
        have clear := free pc instruction found isPrefix
        rw [← branchTargets_contains] at clear
        exact Bool.noConfusion ((List.contains_iff_mem.mpr member).symm.trans clear)
#print axioms prefixEntryFree_iff

instance (code : List RawInstruction) : Decidable (PrefixEntryFree code) :=
  decidable_of_iff _ (prefixEntryFree_iff code)

/-- Without prefixes every instruction satisfies its prefix window and every entry is free. -/
private theorem noPrefixes {code : List RawInstruction} (result : TypeExpr)
    (absent : code.any (fun raw => isPrefixOpcode raw.opcode) = false) :
    prefixSequenceValid result code = true ∧ PrefixEntryFree code := by
  constructor
  · induction code with
    | nil => rfl
    | cons raw rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at absent
      simp [prefixSequenceValid, absent.1, ih absent.2]
  · intro pc raw found prefixAt
    have present : code.any (fun instruction => isPrefixOpcode instruction.opcode) = true :=
      List.any_eq_true.mpr ⟨raw, List.mem_of_getElem? found, prefixAt⟩
    exact Bool.noConfusion (absent.symm.trans present)
#print axioms noPrefixes

/-- Only bodies with a prefix need to read predecessors at branch and switch destinations. -/
def rawPrefixesValid (result : TypeExpr) (code : List RawInstruction) : Bool :=
  if code.any (fun raw => isPrefixOpcode raw.opcode) then
    prefixSequenceValid result code (branchEntriesValid (entryAllowed code.toArray))
  else true

/-- Raw method validation checks prefix structure and every branch into a prefix's follower. -/
theorem rawPrefixesValid_iff (result : TypeExpr) (code : List RawInstruction) :
    rawPrefixesValid result code = true ↔
      prefixSequenceValid result code = true ∧ PrefixEntryFree code := by
  unfold rawPrefixesValid
  split
  · rw [prefixSequenceValid_eq, Bool.and_eq_true, prefixEntryFree_iff]
  · rename_i absent
    simp [noPrefixes result (Bool.eq_false_iff.mpr absent)]
#print axioms rawPrefixesValid_iff

/-- Every suffix of prefix-valid code still pairs each prefix with its legal follower. -/
private theorem prefixSequenceValid_drop {result : TypeExpr} {code : List RawInstruction}
    (valid : prefixSequenceValid result code = true) (count : Nat) :
    prefixSequenceValid result (code.drop count) = true := by
  induction count generalizing code with
  | zero => simpa using valid
  | succ count ih =>
    cases code with
    | nil => rfl
    | cons first rest =>
      exact ih (Bool.and_eq_true_iff.mp valid).2
#print axioms prefixSequenceValid_drop

/-- An instruction in a prefix-valid body can take the modifier at the preceding pc. -/
theorem rawPrefixesValid_predecessor {result : TypeExpr} {code : List RawInstruction}
    {pc : Nat} {modifier instruction : RawInstruction}
    (valid : rawPrefixesValid result code = true)
    (before : code[pc]? = some modifier) (here : code[pc+1]? = some instruction) :
    invalidPredecessor (some modifier) instruction = false := by
  have suffix := prefixSequenceValid_drop ((rawPrefixesValid_iff _ _).mp valid).1 pc
  have first := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp before).choose
  have second := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp here).choose
  rw [first, second] at suffix
  simp only [List.getElem?_eq_some_iff] at before here
  obtain ⟨_, rfl⟩ := before
  obtain ⟨_, rfl⟩ := here
  have window := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp suffix).1).2
  simp only [invalidPredecessor, Option.any_some]
  cases prefixed : isPrefixOpcode _ with
  | false => rfl
  | true =>
    simp only [prefixed, Bool.not_true, Bool.false_or, List.head?_cons,
      Option.any_some, Bool.and_eq_true] at window
    simp only [window.1, Bool.not_true, Bool.and_false]
#print axioms rawPrefixesValid_predecessor

end CIL.Extraction
