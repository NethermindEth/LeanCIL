import Lean
import CIL.Instructions
import CIL.SymbolicExecution
import CIL.DebugNames
import CIL.TermAccess

/-!
# Method identity

Signature-based method identity. Extraction numbers methods by their position in the
reachable call graph, so a helper inserted anywhere renumbers unrelated methods.
`method_named`, `bind_method` and `bind_callee` locate a method by its exact emitted
signature in `Extracted.signatures` instead, and `bind_import` locates an import slot by
its signature in `Extracted.importSignatures`. Each emits `rfl` theorems that the kernel
checks, so a name only locates a method; the body is still bound by `cil_body` or
`cil_embed` and the extraction certificate.
-/

namespace CIL.MethodIdentity

open Lean Meta Elab Term Command
open CIL.DebugNames (visible)

/-- Attach `doc`, the docstring written before a binding command, to the declaration `name`
    the command generated, so hovering the bound name shows the author's description. -/
def documentBinding (doc : Option (TSyntax ``Lean.Parser.Command.docComment)) (name : Ident) :
    CommandElabM Unit := do
  let some doc := doc | return
  let declaration := (← getCurrNamespace) ++ name.getId
  unless (← getEnv).contains declaration do
    throwError "the binding generated no declaration {declaration} to document"
  liftTermElabM <| addDocString declaration mkNullNode doc

/-- The string literals of a closed `List String`, reduced one cell at a time. -/
partial def strings (list : Expr) (found : Array String := #[]) : MetaM (Array String) := do
  match (← whnf list).getAppFnArgs with
  | (``List.cons, #[_, head, tail]) =>
    let .lit (.strVal value) ← whnf head
      | throwError "signature table entry is not a string literal: {head}"
    strings tail (found.push value)
  | (``List.nil, _) => return found
  | _ => throwError "signature table is not a list literal"

/-- The method name between the last `::` and `(`; used only to rank candidates. -/
def methodName (signature : String) : String :=
  (((signature.splitOn "::").getLastD signature).splitOn "(").headD ""

/-- The index of the entry whose signature in `table` is exactly `signature`; `noun` names
    entries in diagnostics. -/
def resolveIn (tableName : Name) (signature : String) (noun : String := "extracted method")
    (short : String := "method") : MetaM Nat := do
  let table ← strings (mkConst (← visible tableName))
  let indices := List.range table.size
  let listing (shown : List Nat) :=
    "\n".intercalate (shown.filterMap fun i => table[i]?.map (s!"  [{i}] {·}"))
  match indices.filter (table[·]? == some signature) with
  | [index] => return index
  | [] =>
    if table.isEmpty then
      throwError "no {noun} has signature\n  {signature}\nthe extraction has no {noun}s"
    let named := indices.filter fun i => table[i]?.map methodName == some (methodName signature)
    let (label, shown) :=
      if named.isEmpty then (s!"{noun}s", indices)
      else (s!"{short}s named {methodName signature}", named)
    throwError "no {noun} has signature\n  {signature}\n{label}:\n{listing (shown.take 12)}"
  | many => throwError "{many.length} {noun}s have signature\n  {signature}\n{listing many}"

/-- The extraction index of the method with exactly this signature. -/
def resolve : String → MetaM Nat := resolveIn `Extracted.signatures

/-- The extraction index of the method with this exact signature, e.g.
`method_named "System.UInt64 Examples.Calls::Twice(System.UInt64)"`. -/
syntax (name := methodNamed) "method_named " str : term

/-- Elaborates `method_named` to the resolved index as a literal. -/
@[term_elab methodNamed] def elabMethodNamed : TermElab := fun stx _ => do
  let some signature := stx[1].isStrLit? | throwUnsupportedSyntax
  return mkNatLit (← resolve signature)

/-- A call instruction found in a method body: `CIL.Instruction.call` or the receiver-checked
    `CIL.Instruction.callInstance`, with its pc, callee index and argument count. -/
structure CallAt where
  pc : Nat
  callee : Nat
  argc : Nat
  opcode : Name
  deriving Inhabited

/-- The instruction a call site holds, as syntax with `index` for its callee. -/
def CallAt.instruction (site : CallAt) (index : Term) : MacroM Term :=
  `($(mkCIdent site.opcode) $index $(quote site.argc))

/-- Every call in a method body, reduced one cell at a time so the cost is linear in the body
and the body is never normalized. -/
def calls (method : Expr) : MetaM (Array CallAt) := do
  let mut cell := mkApp (mkConst ``CIL.Method.code) method
  let mut pc := 0
  let mut found := #[]
  repeat
    match (← whnf cell).getAppFnArgs with
    | (``List.cons, #[_, op, tail]) =>
      if let (opcode, #[callee, argc]) := (← whnf op).getAppFnArgs then
        if opcode == ``CIL.Instruction.call || opcode == ``CIL.Instruction.callInstance then
          if let (some callee, some argc) := (← (evalNat callee).run, ← (evalNat argc).run) then
            found := found.push { pc, callee, argc, opcode }
      cell := tail
      pc := pc + 1
    | _ => break
  return found

/-- The candidate selected by `[occurrence]`, or the only one; never the first of several. -/
def choose (subject : MessageData) (candidates : Array String) (occurrence : Option Nat) :
    MetaM Nat := do
  let listing := "\n".intercalate (candidates.toList.zipIdx.map fun (c, i) => s!"  [{i}] {c}")
  match occurrence with
  | some k =>
    if k < candidates.size then return k
    else throwError "{subject}; [{k}] is out of range:\n{listing}"
  | none =>
    if candidates.size == 1 then return 0
    else throwError "{subject}; select one with [i]:\n{listing}"

/-- Elaborates `fact`, a `code[pc]? = ...` fact proved by `rfl`; unfolding the index
needs recursion depth linear in `pc`, beyond the default for long extracted bodies. -/
def elabAtPc (pc : Nat) (fact : Command) : CommandElabM Unit := do
  elabCommand
    (← `(command| set_option maxRecDepth $(Syntax.mkNumLit (toString (512 + 4 * pc))) in $fact))

/-- Defines `index` and `body` for extraction method `method` and proves by `rfl` that the
    signature table and the program agree with them. -/
def emit (index body : Ident) (signature : StrLit) (method : Nat) : CommandElabM Unit := do
  let extracted := mkIdent (.str `Extracted s!"method{method}")
  let signatures := mkIdent `Extracted.signatures
  let program := mkIdent `Extracted.program
  elabCommand (← `(@[cil_code] def $index : Nat := $(quote method)))
  elabCommand (← `(abbrev $body : CIL.Method := $extracted))
  elabCommand (← `(theorem $(mkIdent (index.getId ++ `signature)) :
    $signatures[$index]? = some $signature := rfl))
  elabCommand (← `(@[cil_code] theorem $(mkIdent (index.getId ++ `found)) :
    $program[$index]? = some $body := rfl))

/-- `bind_method index body := "signature"` defines `index` as the extraction index of
the method with that exact signature and `body` as its extracted body, with
`index.signature` and `index.found` checked by `rfl`. -/
syntax (name := bindMethod) (docComment)? "bind_method " ident ppSpace ident " := " str :
  command

elab_rules : command
  | `($[$doc:docComment]? bind_method $index $body := $signature) => do
    emit index body signature (← liftTermElabM (resolve signature.getString))
    documentBinding doc index

/-- Each call to `method` in `parent`, failing with what it does call. -/
def callSites (parent : Term) (method : Nat) (callee : String) :
    TermElabM (Array CallAt) := do
  let sites ←
    calls (← instantiateMVars (← elabTermEnsuringType parent (some (mkConst ``CIL.Method))))
  let found := sites.filter (·.callee == method)
  if found.isEmpty then
    let table ← strings (mkConst (← visible `Extracted.signatures))
    let called := sites.toList.map (·.callee) |>.eraseDups
    throwError "{parent} does not call\n  {callee}\nit calls:\n\
      {"\n".intercalate (called.map fun i => s!"  [{i}] {table[i]?.getD "?"}")}"
  return found

/-- The call site chosen by `[occurrence]`, or the only one. -/
def callSite (parent : Term) (method : Nat) (callee : String) (occurrence : Option Nat) :
    TermElabM CallAt := do
  let sites ← callSites parent method callee
  let chosen ← choose m!"{parent} calls\n  {callee}\nat {sites.size} sites"
    (sites.map fun site => s!"pc {site.pc}") occurrence
  entryAt "callSite" sites chosen

/-- `bind_callee index body := "signature" from parent` binds as `bind_method` does and
also requires `parent` to call that method; `index.call` states the instruction at its
call site, and `[k]` selects one of several. Expected bodies take `index` as a parameter,
`.call index argc`, so a renumbered extraction never changes them. -/
syntax (name := bindCallee)
  (docComment)? "bind_callee " ident ppSpace ident " := " str " from " term:max (" [" num "]")? :
    command

elab_rules : command
  | `($[$doc:docComment]? bind_callee $index $body := $signature from $parent
      $[[$occurrence]]?) => do
    let (method, site) ← liftTermElabM do
      let method ← resolve signature.getString
      return (method, ← callSite parent method signature.getString (occurrence.map (·.getNat)))
    emit index body signature method
    documentBinding doc index
    let instruction ← liftMacroM (site.instruction index)
    elabAtPc site.pc (← `(@[cil_code] theorem $(mkIdent (index.getId ++ `call)) :
      ($parent).code[$(quote site.pc)]? = some $instruction := rfl))

/-- `bind_callee index body := call argc from parent` binds the method `parent` calls with
`argc` arguments, for helpers whose names are not stable; `[k]` selects one of several such
calls. It emits the same theorems as the signature form, with the signature from the table. -/
syntax (name := bindCalleeShape)
  (docComment)? "bind_callee " ident ppSpace ident " := " &"call " num " from " term:max
    (" [" num "]")? : command

elab_rules : command
  | `($[$doc:docComment]? bind_callee $index $body := call $argc from $parent
      $[[$occurrence]]?) => do
    let (site, signature) ← liftTermElabM do
      let sites ←
        calls (← instantiateMVars (← elabTermEnsuringType parent (some (mkConst ``CIL.Method))))
      let table ← strings (mkConst (← visible `Extracted.signatures))
      let describe := fun (site : CallAt) =>
        s!"pc {site.pc}: {table[site.callee]?.getD "?"} with {site.argc}"
      let shaped := sites.filter (·.argc == argc.getNat)
      if shaped.isEmpty then
        throwError "{parent} makes no call with {argc.getNat} arguments; it calls:
{"
".intercalate (sites.toList.map fun s => "  " ++ describe s)}"
      let chosen ← choose m!"{parent} makes {shaped.size} calls with {argc.getNat} arguments"
        (shaped.map fun site => s!"pc {site.pc}: {table[site.callee]?.getD "?"}")
        (occurrence.map (·.getNat))
      let site ← entryAt "bind_callee" shaped chosen
      return (site, table[site.callee]?.getD "")
    emit index body (Syntax.mkStrLit signature) site.callee
    documentBinding doc index
    let instruction ← liftMacroM (site.instruction index)
    elabAtPc site.pc (← `(@[cil_code] theorem $(mkIdent (index.getId ++ `call)) :
      ($parent).code[$(quote site.pc)]? = some $instruction := rfl))

/-- The number of cells in a closed list, reduced one cell at a time without normalizing its
    elements. -/
partial def cells (list : Expr) (count : Nat := 0) : MetaM Nat := do
  match (← whnf list).getAppFnArgs with
  | (``List.cons, #[_, _, tail]) => cells tail (count + 1)
  | (``List.nil, _) => return count
  | _ => throwError "program is not a list literal"

/-- `bind_import index := "signature"` defines `index` as import slot `j`,
    `Extracted.program.length + j`, by its exact signature. -/
syntax (name := bindImport) (docComment)? "bind_import " ident " := " str : command

elab_rules : command
  | `($[$doc:docComment]? bind_import $index := $signature) => do
    let (slot, length) ← liftTermElabM do
      let slot ←
        resolveIn `Extracted.importSignatures signature.getString "imported method" "import"
      return (slot, ← cells (mkConst (← visible `Extracted.program)))
    let program := mkIdent `Extracted.program
    elabCommand (← `(@[cil_code] def $index : Nat := $(quote (length + slot))))
    documentBinding doc index
    elabCommand (← `(theorem $(mkIdent (index.getId ++ `slot)) :
      $index = ($program).length + $(quote slot) := rfl))
    elabCommand (← `(theorem $(mkIdent (index.getId ++ `signature)) :
      $(mkIdent `Extracted.importSignatures)[$(quote slot)]? = some $signature := rfl))
    elabCommand
      (← `(theorem $(mkIdent (index.getId ++ `unlinked)) : ($program)[$index]? = none := rfl))

end CIL.MethodIdentity
