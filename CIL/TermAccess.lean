import Lean

/-!
# Total access to terms and arrays in tactic code

Tactics, commands and linters read the arguments of `Expr` applications and the entries of
arrays through these accessors. Core's `xs[i]!`, `Expr.getArg!`, `Expr.appArg!` and
`Expr.appFn!` return a default value after printing a panic if the term has an unexpected
shape; the caller then continues with that value. Each accessor here either reports
the absent part as `none`, for code that probes a term's shape, or fails with an error naming
its reader and the term, for code that has committed to a shape.
-/

namespace CIL

open Lean

/-- The argument `fromEnd` places before the last one of the application `term`. -/
private def argumentFromEnd? : Expr → Nat → Option Expr
  | .app _ argument, 0 => some argument
  | .app function _, fromEnd + 1 => argumentFromEnd? function fromEnd
  | _, _ => none

/-- The argument of the application `term` at `index`, counted from its head; `none` when
    `term` applies its head to no more than `index` arguments. -/
def argument? (term : Expr) (index : Nat) : Option Expr :=
  let count := term.getAppNumArgs
  if index < count then argumentFromEnd? term (count - index - 1) else none

/-- The last argument of `term`; `none` when `term` is not an application. -/
def lastArgument? : Expr → Option Expr
  | .app _ argument => some argument
  | _ => none

/-- What `term` applies to its last argument; `none` when `term` is not an application. -/
def appliedFunction? : Expr → Option Expr
  | .app function _ => some function
  | _ => none

/-- The arguments of `term` when it applies the constant `function` to exactly `arity`
    arguments, so an array pattern of that length always matches them. -/
def argumentsOf? (term : Expr) (function : Name) (arity : Nat) : Option (Array Expr) :=
  if term.isAppOfArity function arity then some term.getAppArgs else none

section Committed

variable {m : Type → Type} [Monad m] [MonadError m]

/-- The argument of `term` at `index`, or an error from `reader` showing the term that is not
    an application with that argument. -/
def argumentAt (reader : String) (term : Expr) (index : Nat) : m Expr :=
  match argument? term index with
  | some argument => pure argument
  | none => throwError "{reader}: expected an application with an argument at index {index}, \
      but found{indentExpr term}"

/-- The last argument of `term`, or an error from `reader` showing the term that is not an
    application. -/
def lastArgument (reader : String) (term : Expr) : m Expr :=
  match lastArgument? term with
  | some argument => pure argument
  | none => throwError "{reader}: expected an application, but found{indentExpr term}"

/-- What `term` applies to its last argument, or an error from `reader` showing the term that
    is not an application. -/
def appliedFunction (reader : String) (term : Expr) : m Expr :=
  match appliedFunction? term with
  | some function => pure function
  | none => throwError "{reader}: expected an application, but found{indentExpr term}"

/-- The entry of `entries` at `index`, or an error from `reader` giving the number of entries
    there are. -/
def entryAt {α : Type} (reader : String) (entries : Array α) (index : Nat) : m α :=
  match entries[index]? with
  | some entry => pure entry
  | none => throwError "{reader}: expected an entry at index {index}, but there are \
      {entries.size}"

end Committed

/-- The name `base`, or `base_index` from the first suffix on, for the hypotheses a step
    introduces. -/
def suffixedName (index : Nat) (base : String) : Name :=
  Name.mkSimple (if index == 0 then base else s!"{base}_{index}")

/-- The least suffix at which no name of `bases` is in use in `context`, found in one pass over
    the context; probing each suffix in turn would scan the context once per suffix. -/
def firstUnusedSuffix (context : LocalContext) (bases : Array String) : Nat := Id.run do
  let mut used : Std.HashSet Nat := {}
  for declaration in context do
    let .str .anonymous text := declaration.userName | continue
    for base in bases do
      if text == base then
        used := used.insert 0
      else if let some digits := text.dropPrefix? (base ++ "_") then
        let digits := digits.toString
        -- Only the spelling `suffixedName` produces counts, not `base_01`.
        if let some suffix := digits.toNat? then
          if suffix != 0 && toString suffix == digits then used := used.insert suffix
  let mut index := 0
  while used.contains index do
    index := index + 1
  return index

end CIL
