import Lean

/-!
# Equating names read from bytes with the names an extraction states

A name the extractor writes is a `String` literal; the checker reads the same name from heap bytes.
Comparing them in a `Bool` decision evaluates the string, about ten thousand kernel heartbeats per
character. `spelled?` turns bytes into the `String` they spell with one pass of structural
recursion, and `cil_kernel_rfl` proves an equation between closed terms by letting the kernel
compare them, which expands a string literal to its characters and compares two strings
argument by argument. Decisions over indices, ranges and flags stay `decide +kernel`; a name is
tied to the bytes by an equation `spelled? bytes = some name`. `utf8Characters_encode` proves that
the characters read encode back to exactly the bytes they were read from.
-/

namespace CIL.Extraction

/-- Whether `byte` is a UTF-8 continuation byte. -/
private def isContinuation (byte : Nat) : Bool := 0x80 ≤ byte && byte < 0xC0

/-- The character with the given code point, when the encoding that gave it was the shortest one
    and the code point is a scalar value. A longer encoding of a smaller value is not UTF-8. -/
private def scalar (minimum value : Nat) : Option Char :=
  if value < minimum || (0xD800 ≤ value && value < 0xE000) || 0x10FFFF < value then none
  else some (Char.ofNat value)

/-- The character UTF-8 bytes start with, `first` then `rest`, and the bytes after it, or `none`
    when they do not start with a well-formed character. -/
def utf8Character (first : Nat) (rest : List Nat) : Option (Char × List Nat) :=
  if first < 0x80 then some (Char.ofNat first, rest)
  else if 0xC2 ≤ first && first < 0xE0 then
    match rest with
    | second :: tail =>
      if isContinuation second then
        (·, tail) <$> scalar 0x80 ((first - 0xC0) * 0x40 + (second - 0x80))
      else none
    | [] => none
  else if 0xE0 ≤ first && first < 0xF0 then
    match rest with
    | second :: third :: tail =>
      if isContinuation second && isContinuation third then
        (·, tail) <$> scalar 0x800
          (((first - 0xE0) * 0x40 + (second - 0x80)) * 0x40 + (third - 0x80))
      else none
    | _ => none
  else if 0xF0 ≤ first && first < 0xF5 then
    match rest with
    | second :: third :: fourth :: tail =>
      if isContinuation second && isContinuation third && isContinuation fourth then
        (·, tail) <$> scalar 0x10000
          ((((first - 0xF0) * 0x40 + (second - 0x80)) * 0x40 + (third - 0x80)) * 0x40 +
            (fourth - 0x80))
      else none
    | _ => none
  else none

/-- The characters of UTF-8 bytes, or `none` when they are not well-formed UTF-8. `fuel` is the
    byte count: every character takes at least one byte, so one pass reads it all. -/
def utf8Characters : Nat → List Nat → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, first :: rest =>
    match utf8Character first rest with
    | some (character, tail) => (character :: ·) <$> utf8Characters fuel tail
    | none => none

/-- The UTF-8 bytes of a character, as numbers. -/
private def encodedCharacter (character : Char) : List Nat :=
  (String.utf8EncodeChar character).map UInt8.toNat

/-- A character `scalar` gives has the value it was given, within the bounds it checked. -/
private theorem value_of_scalar {minimum value : Nat} {character : Char}
    (found : scalar minimum value = some character) :
    minimum ≤ value ∧ character.val.toNat = value ∧ value ≤ 0x10FFFF ∧
      (value < 0xD800 ∨ 0xE000 ≤ value) := by
  unfold scalar at found
  split at found
  · simp at found
  · rename_i bounds
    simp only [Option.some.injEq] at found
    subst found
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_or, not_and,
      Nat.not_lt] at bounds
    have valid : value.isValidChar := by
      unfold Nat.isValidChar; omega
    refine ⟨by omega, ?_, by omega, by omega⟩
    simp [Char.ofNat, valid, Char.ofNatAux]

/-- The bytes of a character `scalar` gives, by the value it was given. -/
private theorem encoded_scalar {minimum value : Nat} {character : Char}
    (found : scalar minimum value = some character) :
    encodedCharacter character =
      if value ≤ 0x7F then [value % 256]
      else if value ≤ 0x7FF then [(value / 64 % 0x20 + 0xC0) % 256, (value % 0x40 + 0x80) % 256]
      else if value ≤ 0xFFFF then
        [(value / 4096 % 0x10 + 0xE0) % 256, (value / 64 % 0x40 + 0x80) % 256,
          (value % 0x40 + 0x80) % 256]
      else
        [(value / 262144 % 0x08 + 0xF0) % 256, (value / 4096 % 0x40 + 0x80) % 256,
          (value / 64 % 0x40 + 0x80) % 256, (value % 0x40 + 0x80) % 256] := by
  unfold encodedCharacter String.utf8EncodeChar
  rw [(value_of_scalar found).2.1]
  simp only
  split <;> (try split) <;> (try split) <;> simp

/-- A character read from the front of the bytes encodes to exactly the bytes it consumed. -/
private theorem utf8Character_encode {first : Nat} {rest tail : List Nat} {character : Char}
    (decoded : utf8Character first rest = some (character, tail)) :
    first :: rest = encodedCharacter character ++ tail := by
  unfold utf8Character at decoded
  split at decoded
  · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    have found : scalar 0 first = some (Char.ofNat first) := by
      unfold scalar; rw [ite_eq_right (by simp; omega)]
    rw [encoded_scalar found, ite_eq_left (by omega)]
    simp; omega
  split at decoded
  · rename_i lead
    simp only [Bool.and_eq_true, decide_eq_true_eq] at lead
    match rest, decoded with
    | second :: following, decoded =>
      simp only at decoded
      split at decoded
      · rename_i continuation
        simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at continuation
        obtain ⟨decodedCharacter, found, step⟩ := Option.map_eq_some_iff.mp decoded
        simp only [Prod.mk.injEq] at step
        obtain ⟨sameCharacter, sameTail⟩ := step
        subst sameTail sameCharacter
        have bounds := value_of_scalar found
        rw [encoded_scalar found, ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [List.cons_append, List.nil_append, List.cons.injEq]
        exact ⟨by omega, by omega, trivial⟩
      · cases decoded
  split at decoded
  · rename_i lead
    simp only [Bool.and_eq_true, decide_eq_true_eq] at lead
    match rest, decoded with
    | second :: third :: following, decoded =>
      simp only at decoded
      split at decoded
      · rename_i continuation
        simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at continuation
        obtain ⟨decodedCharacter, found, step⟩ := Option.map_eq_some_iff.mp decoded
        simp only [Prod.mk.injEq] at step
        obtain ⟨sameCharacter, sameTail⟩ := step
        subst sameTail sameCharacter
        have bounds := value_of_scalar found
        rw [encoded_scalar found, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega)]
        simp only [List.cons_append, List.nil_append, List.cons.injEq]
        exact ⟨by omega, by omega, by omega, trivial⟩
      · cases decoded
  split at decoded
  · rename_i lead
    simp only [Bool.and_eq_true, decide_eq_true_eq] at lead
    match rest, decoded with
    | second :: third :: fourth :: following, decoded =>
      simp only at decoded
      split at decoded
      · rename_i continuation
        simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at continuation
        obtain ⟨decodedCharacter, found, step⟩ := Option.map_eq_some_iff.mp decoded
        simp only [Prod.mk.injEq] at step
        obtain ⟨sameCharacter, sameTail⟩ := step
        subst sameTail sameCharacter
        have bounds := value_of_scalar found
        rw [encoded_scalar found, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        simp only [List.cons_append, List.nil_append, List.cons.injEq]
        exact ⟨by omega, by omega, by omega, by omega, trivial⟩
      · cases decoded
  cases decoded

/-- Characters read from UTF-8 bytes encode back to exactly those bytes. -/
theorem utf8Characters_encode : ∀ (fuel : Nat) (bytes : List Nat) (characters : List Char),
    utf8Characters fuel bytes = some characters →
      characters.flatMap (fun character => (String.utf8EncodeChar character).map UInt8.toNat) =
        bytes
  | _, [], characters, decoded => by
    rw [utf8Characters.eq_1] at decoded
    cases decoded; rfl
  | 0, _ :: _, _, decoded => by
    rw [utf8Characters.eq_2] at decoded
    cases decoded
  | fuel + 1, first :: rest, characters, decoded => by
    rw [utf8Characters.eq_3] at decoded
    split at decoded
    · rename_i character tail step
      cases decodedTail : utf8Characters fuel tail with
      | none => simp [decodedTail] at decoded
      | some others =>
        simp only [decodedTail, Option.map_eq_map, Option.map_some, Option.some.injEq] at decoded
        subst decoded
        rw [List.flatMap_cons, utf8Characters_encode fuel tail others decodedTail]
        exact (utf8Character_encode step).symm
    · cases decoded
#print axioms utf8Characters_encode

/-- The string the bytes spell as UTF-8, or `none` when they are not well-formed UTF-8. The
    result is a `String.ofList` of characters, which the kernel compares with a literal without
    computing the literal's bytes. -/
def spelled? (bytes : List Nat) : Option String :=
  (utf8Characters bytes.length bytes).map String.ofList

open Lean Elab Tactic Meta in
/-- Prove an equation `left = right` by `Eq.refl left`, which the kernel accepts when it can
    reduce both sides to the same term. Unlike `rfl`, the elaborator never unfolds either side,
    so a closed computation over a large literal costs the kernel's evaluation once. The proof
    is added as an auxiliary lemma first; when the kernel refuses it, the tactic fails at the
    goal and prints both sides, and no proof is assigned. -/
elab "cil_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType')
  let some (type, left, right) := target.eq?
    | throwError "cil_kernel_rfl: the goal must be an equation, but it is{indentExpr target}"
  if target.hasExprMVar then
    throwError "cil_kernel_rfl: the equation has unassigned metavariables{indentExpr target}"
  let proof := mkApp2 (mkConst ``Eq.refl [← getLevel type]) type left
  let levelsInType := (collectLevelParams {} target).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let lemmaName ←
    try withOptions (Elab.async.set · false) do mkAuxLemma lemmaLevels target proof
    catch _ =>
      throwError "cil_kernel_rfl: the kernel does not accept the two sides as equal\
        \nleft:{indentExpr left}\nright:{indentExpr right}"
  goal.assign (mkConst lemmaName (lemmaLevels.map .param))
  replaceMainGoal []

end CIL.Extraction
