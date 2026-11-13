import Lean

/-!
# Equating names read from bytes with the names an extraction states

A name the extractor writes is a `String` literal; the checker reads the same name from heap bytes.
Comparing them in a `Bool` decision evaluates the string, about ten thousand kernel heartbeats per
character. `spelled?` turns bytes into the `String` they spell with one pass of structural
recursion, and `cil_kernel_rfl` proves an equation between closed terms by letting the kernel
compare them, which expands a string literal to its characters and compares two strings
argument by argument. Decisions over indices, ranges and flags stay `decide +kernel`; a name is
tied to the bytes by an equation `spelled? bytes = some name`.
-/

namespace CIL.Extraction

/-- Whether `byte` is a UTF-8 continuation byte. -/
private def isContinuation (byte : Nat) : Bool := 0x80 ≤ byte && byte < 0xC0

/-- The character with the given code point, when the encoding that gave it was the shortest one
    and the code point is a scalar value. A longer encoding of a smaller value is not UTF-8. -/
private def scalar (minimum value : Nat) : Option Char :=
  if value < minimum || (0xD800 ≤ value && value < 0xE000) || 0x10FFFF < value then none
  else some (Char.ofNat value)

/-- The characters of UTF-8 bytes, or `none` when they are not well-formed UTF-8. `fuel` is the
    byte count: every character takes at least one byte, so one pass reads it all. -/
def utf8Characters : Nat → List Nat → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, first :: rest =>
    let next (consumed : List Nat) (character : Option Char) : Option (List Char) :=
      match character, utf8Characters fuel consumed with
      | some character, some characters => some (character :: characters)
      | _, _ => none
    if first < 0x80 then next rest (some (Char.ofNat first))
    else if 0xC2 ≤ first && first < 0xE0 then
      match rest with
      | second :: tail =>
        if isContinuation second then
          next tail (scalar 0x80 ((first - 0xC0) * 0x40 + (second - 0x80)))
        else none
      | [] => none
    else if 0xE0 ≤ first && first < 0xF0 then
      match rest with
      | second :: third :: tail =>
        if isContinuation second && isContinuation third then
          next tail (scalar 0x800
            (((first - 0xE0) * 0x40 + (second - 0x80)) * 0x40 + (third - 0x80)))
        else none
      | _ => none
    else if 0xF0 ≤ first && first < 0xF5 then
      match rest with
      | second :: third :: fourth :: tail =>
        if isContinuation second && isContinuation third && isContinuation fourth then
          next tail (scalar 0x10000
            ((((first - 0xF0) * 0x40 + (second - 0x80)) * 0x40 + (third - 0x80)) * 0x40 +
              (fourth - 0x80)))
        else none
      | _ => none
    else none

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
