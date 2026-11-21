import CIL.Extraction.SearchTreeLiteral
import Std.Data.HashSet

/-!
# Platform definitions

The carried slices hold the rows of the pinned assemblies only; a type they name but do not
define belongs to a platform assembly. What the metadata checks rely on about such a type is read
from a `PlatformTable`, the list of platform definitions the extraction states: the type's scope,
name parts and kind. Each check that relies on a type outside the carried slices looks its entry
up with `PlatformTable.require` and refuses the type when the entry is missing or states another
kind. The extractor supplies each kind, including enum storage. The kernel checks the lookup
and table equality across bodies. Agreement with the platform image bytes remains trusted.

`platform_table%` emits a balanced tree. When several scopes use identical name parts, the
search key includes the scope. Every lookup compares the exact scope and name parts.
-/

namespace CIL.Extraction

/-- What the metadata checks rely on about a type outside the carried slices. -/
inductive PlatformKind where
  /-- A class the checks rely on for nothing past being a reference type. -/
  | classType
  | interfaceType
  | genericClass (arity : Nat)
  | genericInterface (arity : Nat)
  | genericValue (arity : Nat)
  /-- A value type that is not an enum. -/
  | valueType
  /-- An enum whose one instance field has the integer element type `underlying`. -/
  | enumType (underlying : Nat) (parameters : Nat := 0)
  /-- `System.Object`, which ends every class chain and declares no instance field. -/
  | objectRoot
  /-- `System.ValueType`: a type that extends it is a value type. -/
  | valueTypeRoot
  /-- `System.Enum`: a type that extends it is an enum. -/
  | enumRoot
  /-- The value pair whose instance fields `Item1` and `Item2` are its first and its second. -/
  | valuePair
  /-- The class whose static `IsLittleEndian` field is the profile's byte order. -/
  | byteOrder
  deriving DecidableEq, Repr

/-- Whether a type of this kind is a value type. -/
def PlatformKind.isValue : PlatformKind → Bool
  | .valueType | .genericValue _ | .enumType _ _ | .valuePair => true
  | _ => false

/-- The number of generic parameters declared by the platform definition. -/
def PlatformKind.arity : PlatformKind -> Nat
  | .genericClass count | .genericInterface count | .genericValue count => count
  | .enumType _ count => count
  | .valuePair => 2
  | _ => 0

/-- Whether a signature's value-or-class byte, when it has one, agrees with the kind. -/
def PlatformKind.fitsHint (hint : Option Bool) (kind : PlatformKind) : Bool :=
  hint.all (· == kind.isValue)

/-- One platform type: the identity of the assembly a reference scopes it to, the namespace
    column and simple name of each enclosing type and of the type itself, as bytes, and its
    kind. -/
structure PlatformDefinition where
  scope : List Nat
  parts : List (List Nat)
  kind : PlatformKind
  deriving DecidableEq, Repr

/-- A digit past every byte, which ends each name part in a key. -/
def partEnd : Nat := 256

/-- The base-512 encoding of a sequence of byte strings with a distinct end digit. -/
def platformKey (parts : List (List Nat)) : Nat :=
  parts.foldl (init := 1) fun code part =>
    part.foldl (fun code byte => code * 512 + byte) code * 512 + partEnd

/-- A balanced index of scoped definitions. Shared names require scope bytes in the key. -/
structure PlatformTable where
  includesScope : Bool
  entries : SearchTree (List PlatformDefinition)
  deriving DecidableEq, Repr

/-- The last group at or below the key, or the inherited candidate when the subtree is empty.
    Exact identity comparison discards the candidate when the requested key is absent. -/
private def scopedCandidates (tree : SearchTree (List PlatformDefinition)) (key : Nat)
    (previous : List PlatformDefinition) : List PlatformDefinition :=
  match tree with
  | .leaf => previous
  | .node left limit group right =>
    if Nat.blt key limit then scopedCandidates left key previous
    else scopedCandidates right key group

/-- Each candidate comes from the inherited group or a group in the subtree. -/
private theorem scopedCandidates_mem (tree : SearchTree (List PlatformDefinition)) (key : Nat)
    (previous : List PlatformDefinition) (entry : PlatformDefinition)
    (member : entry ∈ scopedCandidates tree key previous) :
    entry ∈ previous ∨ ∃ pair ∈ tree.toList, entry ∈ pair.2 := by
  induction tree generalizing previous with
  | leaf => exact .inl member
  | node left limit group right leftIH rightIH =>
    simp only [scopedCandidates] at member
    split at member
    · rcases leftIH previous member with inherited | ⟨pair, inside, found⟩
      · exact .inl inherited
      · exact .inr ⟨pair, List.mem_append_left _ inside, found⟩
    · rcases rightIH group member with localMember | ⟨pair, inside, found⟩
      · exact .inr ⟨(limit, group), by simp [SearchTree.toList], localMember⟩
      · exact .inr ⟨pair, List.mem_append_right _ (List.mem_cons_of_mem _ inside), found⟩
#print axioms scopedCandidates_mem

/-- Candidate definitions for the reference. Shared names use a single comparison per node. -/
private def PlatformTable.group? (table : PlatformTable) (scope : List Nat)
    (parts : List (List Nat)) : Option (List PlatformDefinition) :=
  if table.includesScope then
    some (scopedCandidates table.entries (platformKey (scope :: parts)) [])
  else table.entries.find? (platformKey parts)

/-- Every definition of the table, group by group. -/
def PlatformTable.definitions (table : PlatformTable) : List PlatformDefinition :=
  table.entries.toList.flatMap (·.2)

/-- The kind the table states for the type of this scope and these name parts. -/
def PlatformTable.kindOf (table : PlatformTable) (scope : List Nat)
    (parts : List (List Nat)) : Option PlatformKind := do
  let group ← table.group? scope parts
  let entry ← group.find? fun entry => entry.scope == scope && entry.parts == parts
  pure entry.kind

/-- A kind the table states is a definition of the table for exactly that scope and those
    parts, whatever order the tree holds its groups in. -/
theorem PlatformTable.mem_of_kindOf {table : PlatformTable} {scope : List Nat}
    {parts : List (List Nat)} {kind : PlatformKind}
    (found : table.kindOf scope parts = some kind) :
    { scope, parts, kind } ∈ table.definitions := by
  simp only [PlatformTable.kindOf, bind, Option.bind] at found
  split at found
  · cases found
  · rename_i group filed
    dsimp only at found
    split at found
    · cases found
    · rename_i entry selected
      cases found
      have member := List.mem_of_find?_eq_some selected
      have same := List.find?_some selected
      simp only [Bool.and_eq_true, beq_iff_eq] at same
      obtain ⟨sameScope, sameParts⟩ := same
      have included : entry ∈ table.definitions := by
        simp only [PlatformTable.definitions, List.mem_flatMap]
        unfold PlatformTable.group? at filed
        split at filed
        · cases filed
          exact (scopedCandidates_mem _ _ [] entry member).resolve_left (by simp)
        · exact ⟨(_, group), SearchTree.find?_mem_toList _ _ _ filed, member⟩
      cases entry
      cases sameScope
      cases sameParts
      exact included

#print axioms PlatformTable.mem_of_kindOf

/-- The kind of the type of this scope and these parts, which `fits` must accept: a missing
    entry is `missingPlatformDefinition` and another kind `platformKindMismatch`, both for
    `token`. -/
def PlatformTable.require (table : PlatformTable) (token : Nat) (scope : List Nat)
    (parts : List (List Nat)) (fits : PlatformKind → Bool) :
    Except MetadataError PlatformKind :=
  match table.kindOf scope parts with
  | none => .error (.missingPlatformDefinition token)
  | some kind => if fits kind then .ok kind else .error (.platformKindMismatch token)

/-- A required kind is the kind of a definition of the table for that scope and those parts,
    and `fits` accepts it. -/
theorem PlatformTable.require_ok {table : PlatformTable} {token : Nat} {scope : List Nat}
    {parts : List (List Nat)} {fits : PlatformKind → Bool} {kind : PlatformKind}
    (required : table.require token scope parts fits = .ok kind) :
    { scope, parts, kind } ∈ table.definitions ∧ fits kind = true := by
  unfold PlatformTable.require at required
  split at required
  · cases required
  · rename_i stated found
    split at required
    · cases required
      exact ⟨PlatformTable.mem_of_kindOf found, by assumption⟩
    · cases required

#print axioms PlatformTable.require_ok

/-- The table with no definitions, under which every reliance on a platform type fails. -/
instance : EmptyCollection PlatformTable := ⟨⟨false, .leaf⟩⟩

open Lean Meta in
/-- The number a code term spells when it is written as an extraction writes one: a numeral, or
    codes joined by `Nat.lor` and `Nat.shiftLeft`; `none` for any other term. -/
private partial def literalCode? (term : Expr) : MetaM (Option Nat) := do
  match_expr term with
  | Nat.lor high low =>
    match ← literalCode? high, ← literalCode? low with
    | some high, some low => return some (high ||| low)
    | _, _ => return none
  | Nat.shiftLeft code shift =>
    match ← literalCode? code, ← getNatValue? shift with
    | some code, some shift => return some (code <<< shift)
    | _, _ => return none
  | _ => getNatValue? term

open Lean Meta in
/-- The bytes a byte-list term spells when it is written as an extraction writes one: `[]`, a
    list of numerals or `fixedBytes count code`; `none` for any other term. -/
private partial def literalBytes? (term : Expr) : MetaM (Option (List Nat)) := do
  match_expr term with
  | fixedBytes count code =>
    match ← getNatValue? count, ← literalCode? code with
    | some count, some code => return some (fixedBytes count code)
    | _, _ => return none
  | List.nil _ => return some []
  | List.cons _ head tail =>
    match ← getNatValue? head, ← literalBytes? tail with
    | some head, some tail => return some (head :: tail)
    | _, _ => return none
  | _ => return none

open Lean Meta in
/-- The byte lists of a list term of byte-list terms, each read by `literalBytes?`. -/
private partial def literalParts? (term : Expr) : MetaM (Option (List (List Nat))) := do
  match_expr term with
  | List.nil _ => return some []
  | List.cons _ head tail =>
    match ← literalBytes? head, ← literalParts? tail with
    | some head, some tail => return some (head :: tail)
    | _, _ => return none
  | _ => return none

open Lean Meta in
/-- The scope and name parts of a definition term: read from its literals when an extraction
    wrote them, otherwise evaluated, which compiles the term. -/
private def definitionType (cell : Expr) : MetaM (List Nat × List (List Nat)) := do
  if let some (scope, parts, _) := cell.app3? ``PlatformDefinition.mk then
    if let (some scope, some parts) := (← literalBytes? scope, ← literalParts? parts) then
      return (scope, parts)
  let definition ← unsafe evalExpr PlatformDefinition (Lean.mkConst ``PlatformDefinition) cell
  return (definition.scope, definition.parts)

open Lean Meta Elab Term in
/-- `platform_table% [definitions]` is the list written out as a literal search tree whose leaves
    hold the definition terms. Each term is elaborated on its own and its scope and name parts are
    read from its literals, so a long list costs no evaluation and no recursion per definition. Two
    definitions of one scope and name parts are an error, since a lookup would read only the
    first. -/
elab "platform_table% " "[" definitions:term,* "]" : term => do
  let entryType := Lean.mkConst ``PlatformDefinition
  let mut elaborated := #[]
  for definition in definitions.getElems do
    elaborated := elaborated.push (← elabTermEnsuringType definition entryType)
  synthesizeSyntheticMVarsNoPostponing
  let cells ← elaborated.mapM instantiateMVars
  let mut named : Std.HashSet (List Nat × List (List Nat)) := {}
  let mut names : Std.HashSet (List (List Nat)) := {}
  let types ← cells.mapM fun cell => definitionType cell
  for type in types do
    if named.contains type then throwError "platform table: two definitions name one type"
    named := named.insert type
    names := names.insert type.2
  let includesScope := names.size != types.size
  let keys := types.map fun (scope, parts) =>
    platformKey (if includesScope then scope :: parts else parts)
  return mkApp2 (mkConst ``PlatformTable.mk) (toExpr includesScope)
    (← SearchTree.groupedLiteral entryType cells keys)

end CIL.Extraction
