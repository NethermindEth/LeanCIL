import CIL.Extraction.Generics

/-!
# Branch entry after instruction prefixes

A prefix modifies the instruction after it, so ECMA-335 forbids a branch into that instruction.
`PrefixEntryFree` states the rule for every pc of raw code, live or not. Body decoding refuses
such a branch, so the code of every method with body evidence satisfies it
(`checkBody_prefixEntryFree`, `MethodEvidenceValid.prefixEntryFree`) and the evidence check
decides nothing more. `prefixEntryFreeWith` decides the rule in one pass from
`branchTargetMask`, a bit mask of the branch destinations built once per body
(`prefixEntryFree_iff`), for code no body evidence covers.
-/

namespace CIL.Extraction

/-- The opcodes that prefix the instruction after them: `unaligned.`, `volatile.`, `tail.`,
    `constrained.`, `no.` and `readonly.`, all between `0xFE12` and `0xFE1E`. -/
def isPrefixOpcode (opcode : Nat) : Bool :=
  0xFE12 <= opcode && opcode <= 0xFE1E &&
    (opcode == 0xFE12 || opcode == 0xFE13 || opcode == 0xFE14 || opcode == 0xFE16 ||
      opcode == 0xFE19 || opcode == 0xFE1E)

/-- No branch or switch of the code enters the instruction after a prefix; a branch to the
    prefix itself stays allowed. -/
def PrefixEntryFree (code : List RawInstruction) : Prop :=
  ∀ pc instruction, code[pc]? = some instruction → isPrefixOpcode instruction.opcode = true →
    code.any (branchesTo (pc + 1)) = false

/-- Whether no instruction of `code`, the first at `pc`, is a prefix whose next pc
    `targeted` names. -/
def prefixEntryFreeWith (targeted : Nat → Bool) : Nat → List RawInstruction → Bool
  | _, [] => true
  | pc, instruction :: rest =>
    (!isPrefixOpcode instruction.opcode || !targeted (pc + 1)) &&
      prefixEntryFreeWith targeted (pc + 1) rest

/-- The one-pass rule holds exactly when no prefix of the code, the first at `start`, has a
    targeted next pc. -/
theorem prefixEntryFreeWith_iff (targeted : Nat → Bool) (start : Nat)
    (code : List RawInstruction) :
    prefixEntryFreeWith targeted start code = true ↔
      ∀ pc instruction, code[pc]? = some instruction → isPrefixOpcode instruction.opcode = true →
        targeted (start + pc + 1) = false := by
  induction code generalizing start with
  | nil => simp [prefixEntryFreeWith]
  | cons first rest restFree =>
    simp only [prefixEntryFreeWith, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      restFree]
    constructor
    · rintro ⟨firstFree, restClear⟩ pc instruction found isPrefix
      cases pc with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        rcases firstFree with notPrefix | clear
        · rw [notPrefix] at isPrefix; cases isPrefix
        · simpa using clear
      | succ pc =>
        have := restClear pc instruction (by simpa using found) isPrefix
        rwa [show start + 1 + pc + 1 = start + (pc + 1) + 1 by omega] at this
    · intro clear
      refine ⟨?_, fun pc instruction found isPrefix => ?_⟩
      · cases isPrefix : isPrefixOpcode first.opcode
        · exact .inl rfl
        · exact .inr (by simpa using clear 0 first rfl isPrefix)
      · have := clear (pc + 1) instruction (by simpa using found) isPrefix
        rwa [show start + (pc + 1) + 1 = start + 1 + pc + 1 by omega] at this

#print axioms prefixEntryFreeWith_iff

/-- Set bit `target` of `mask` for each of `targets`. -/
def maskTargets (targets : List Nat) (mask : Nat) : Nat :=
  targets.foldr (fun target mask => mask ||| 1 <<< target) mask

/-- The branch and switch destinations of `code` as a bit mask, built in one pass, whose bits
    the kernel tests in constant work (`testBit_branchTargetMask`). -/
def branchTargetMask : List RawInstruction → Nat
  | [] => 0
  | instruction :: rest =>
    match instruction.operand with
    | .target target => branchTargetMask rest ||| 1 <<< target
    | .targets targets => maskTargets targets (branchTargetMask rest)
    | _ => branchTargetMask rest

/-- A bit of `maskTargets` is set for each listed target and each bit already set. -/
theorem testBit_maskTargets (targets : List Nat) (mask bit : Nat) :
    (maskTargets targets mask).testBit bit = (targets.contains bit || mask.testBit bit) := by
  induction targets with
  | nil => simp [maskTargets]
  | cons first rest restBits =>
    simp only [maskTargets, List.foldr_cons] at restBits ⊢
    rw [Nat.testBit_or, restBits, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases same : first = bit
    · subst same; simp
    · have other : bit ≠ first := fun equal => same equal.symm
      simp [same, other]

#print axioms testBit_maskTargets

/-- Bit `target` of the mask is set exactly when some instruction branches to `target`. -/
theorem testBit_branchTargetMask (code : List RawInstruction) (target : Nat) :
    (branchTargetMask code).testBit target = code.any (branchesTo target) := by
  induction code with
  | nil => simp [branchTargetMask]
  | cons instruction rest restBits =>
    simp only [branchTargetMask, List.any_cons]
    cases operand : instruction.operand
    case target destination =>
      simp only [operand, Nat.testBit_or, restBits, Nat.one_shiftLeft, Nat.testBit_two_pow,
        branchesTo]
      by_cases same : destination = target
      · subst same; simp
      · simp [same]
    case targets destinations =>
      simp [operand, testBit_maskTargets, branchesTo, restBits]
    all_goals simp [operand, branchesTo, restBits]

#print axioms testBit_branchTargetMask

/-- Read through the body's branch-target mask, the one-pass rule decides `PrefixEntryFree`. -/
theorem prefixEntryFree_iff (code : List RawInstruction) :
    prefixEntryFreeWith (branchTargetMask code).testBit 0 code = true ↔ PrefixEntryFree code := by
  rw [prefixEntryFreeWith_iff]
  simp only [testBit_branchTargetMask, Nat.zero_add, PrefixEntryFree]

#print axioms prefixEntryFree_iff

instance (code : List RawInstruction) : Decidable (PrefixEntryFree code) :=
  decidable_of_iff _ (prefixEntryFree_iff code)

end CIL.Extraction
