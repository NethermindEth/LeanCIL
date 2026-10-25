import Lean

/-!
# Debug names

PDB local names and source locations, read from `ExtractedSymbols` when a proof imports
it. The extractor writes that module only when a matching portable PDB is present. A name
only chooses a local index that the proof still states and the kernel still checks; without
the module, diagnostics are unchanged and `local_named` reports what is missing.
-/

namespace CIL.DebugNames

open Lean Meta Elab Term

/-- `(slot, startPc, endPc, name)` with `endPc` exclusive. -/
abbrev Scoped := Nat × Nat × Nat × String
/-- `(pc, file, line, column)` of a visible sequence point. -/
abbrev Point := Nat × String × Nat × Nat

/-- The implementation of `evaluate`. -/
private unsafe def evaluateUnsafe (T : Type) [ToExpr T] (value : Expr) : MetaM T :=
  evalExpr T (toTypeExpr T) value

/-- Evaluates a closed expression of type `T` to its value. -/
@[implemented_by evaluateUnsafe]
private opaque evaluate (T : Type) [ToExpr T] (value : Expr) : MetaM T

/-- The constant `name` refers to here, preferring the innermost namespace: batch
verification places each extraction in its own namespace. -/
def visible? (name : Name) : MetaM (Option Name) := do
  let found := (← resolveGlobalName name).filter (·.2.isEmpty) |>.map (·.1)
  return found.foldl
    (fun best n => if best.all (·.getNumParts < n.getNumParts) then some n else best) none

/-- `visible?`, failing with a request to import the extraction when nothing is in scope. -/
def visible (name : Name) : MetaM Name := do
  let some found ← visible? name | throwError "{name} is not in scope; import the extraction"
  return found

/-- One method's entries from `ExtractedSymbols.{table}`, or `none` when it is not imported. -/
def entries (T : Type) [ToExpr T] (table : Name) (method : Nat) : MetaM (Option (List T)) := do
  let some name ← visible? (`ExtractedSymbols ++ table) | return none
  return (← evaluate (List (List T)) (mkConst name))[method]?

/-- `file:line:column` of the nearest sequence point at or before `pc`. -/
def location? (method pc : Nat) : MetaM (Option String) := do
  let some points ← entries Point `points method | return none
  return (points.filter (·.1 ≤ pc)).getLast?.map fun (_, file, line, column) =>
    s!"{file}:{line}:{column}"

/-- A diagnostic line naming the source of `pc`, or nothing without symbols. -/
def sourceLine (method pc : Nat) : MetaM String := do
  return match ← location? method pc with
    | some found => s!"\nsource of actual pc {pc}: {found}"
    | none => ""

/-- Elaborates `term` and evaluates it to a closed `Nat`. -/
private def closedNat (term : Term) : TermElabM Nat := do
  let some value ← (evalNat (← whnf (← elabTermEnsuringType term (some (mkConst ``Nat))))).run
    | throwError "{term} is not a closed natural number"
  return value

/-- One diagnostic line per named scope. -/
private def listing (scopes : List Scoped) : String :=
  "\n".intercalate (scopes.map fun (slot, start, stop, name) =>
    s!"  slot {slot} \"{name}\", pc {start} until {stop}")

/-- The slot of PDB local `name` in a method: the only slot it names, or with `at pc` the
innermost scope containing `pc`. A compiler temporary has no name and keeps its index. -/
def localSlot (method : Nat) (name : String) (pc : Option Nat) : MetaM Nat := do
  let some scopes ← entries Scoped `locals method
    | throwError "local names need `import ExtractedSymbols`, which extraction writes only \
        from a matching portable PDB"
  let named := scopes.filter (·.2.2.2 == name)
  if named.isEmpty then
    throwError "method {method} has no local named \"{name}\"; its named locals:\n{listing scopes}"
  let contains (s : Scoped) (pc : Nat) := s.2.1 ≤ pc && pc < s.2.2.1
  let width (s : Scoped) := s.2.2.1 - s.2.1
  let chosen := match pc with
    | some pc =>
      let around := named.filter (contains · pc)
      let narrowest := (around.map width).min?.getD 0
      around.filter (width · == narrowest) |>.map (·.1) |>.eraseDups
    | none => named.map (·.1) |>.eraseDups
  match chosen, pc with
  | [slot], _ => return slot
  | [], some pc =>
    throwError "no scope of local \"{name}\" in method {method} contains pc {pc}:\n{listing named}"
  | _, none =>
    throwError "local \"{name}\" names {chosen.length} slots in method {method}; \
      select one with `at pc`:\n{listing named}"
  | _, some pc =>
    throwError "local \"{name}\" names {chosen.length} slots at pc {pc} in method {method}:\
      \n{listing named}"

/-- `local_named method "name"` is the slot of a PDB-named local, and `at pc` resolves it in
the innermost scope containing `pc`, e.g. `.local (local_named root "carry" at reduce)`. -/
syntax (name := localNamed) "local_named " term:max ppSpace str (" at " term:max)? : term

/-- Elaborates `local_named` to the slot number as a literal. -/
@[term_elab localNamed] def elabLocalNamed : TermElab := fun stx _ => do
  match stx with
  | `(local_named $method $name $[at $pc]?) =>
    let pc ← pc.mapM closedNat
    return mkNatLit (← localSlot (← closedNat method) name.getString pc)
  | _ => throwUnsupportedSyntax

end CIL.DebugNames
