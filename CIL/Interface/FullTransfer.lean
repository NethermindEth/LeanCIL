import CIL.Interface.Closure

/-!
# Full-verification term transfer

Full import verification composes a library's certified theorem with the caller's proof in
one environment. `capture` writes, as Lean source, every declaration the roots depend on
outside the shared modules, renamed under a target namespace. Each declaration becomes a
`run_cmd` that rebuilds the exact kernel term and adds it with kernel type checking forced
on, so the transfer reproduces checked terms rather than trusting their source.
-/

namespace CIL.Interface.FullTransfer
open Lean

/-- `value` as a quoted string literal, escaped by the JSON encoder. -/
private def quoted (value : String) : String := (Json.str value).compress

/-- Lean source that constructs the name. -/
private def nameSource : Name -> String
  | .anonymous => "Lean.Name.anonymous"
  | .str parent value => "(Lean.Name.str " ++ nameSource parent ++ " " ++ quoted value ++ ")"
  | .num parent value => "(Lean.Name.num " ++ nameSource parent ++ " " ++ toString value ++ ")"

private def listSource (values : List String) : String :=
  "[" ++ String.intercalate ", " values ++ "]"

/-- A constant keeps its name if a shared module declares it and otherwise moves under
    `targetNamespace`; a missing constant is an error. -/
private def mapped (environment : Environment) (shared : Std.HashSet Name)
    (targetNamespace name : Name) : Except String Name := do
  unless environment.contains name do
    throw ("Missing full-verification dependency: " ++ name.toString)
  if shared.contains (CIL.Interface.definingModule environment name) then return name
  return targetNamespace ++ name

/-- Exact name components; unlike display strings, numeric and hygienic segments round-trip. -/
private inductive TransferName where
  | anonymous
  | str (parent : TransferName) (text : String)
  | num (parent : TransferName) (number : Nat)
  deriving ToJson, FromJson

/-- Encode every name component without flattening it to display text. -/
private def encodeName : Name → TransferName
  | .anonymous => .anonymous
  | .str parent text => .str (encodeName parent) text
  | .num parent number => .num (encodeName parent) number

/-- Restore numeric and string name segments exactly. -/
private def decodeName : TransferName → Name
  | .anonymous => .anonymous
  | .str parent text => .str (decodeName parent) text
  | .num parent number => .num (decodeName parent) number

/-- Universe expressions admitted by checked transfer, excluding metavariables. -/
private inductive TransferLevel where
  | zero
  | succ (value : TransferLevel)
  | max (left right : TransferLevel)
  | imax (left right : TransferLevel)
  | param (name : TransferName)
  deriving ToJson, FromJson

/-- Encode a closed universe expression, rejecting unresolved metavariables. -/
private def encodeLevel : Level → Except String TransferLevel
  | .zero => pure .zero
  | .succ value => return .succ (← encodeLevel value)
  | .max left right => return .max (← encodeLevel left) (← encodeLevel right)
  | .imax left right => return .imax (← encodeLevel left) (← encodeLevel right)
  | .param name => pure (.param (encodeName name))
  | .mvar _ => throw "Full verification cannot transfer universe metavariables"

/-- Restore the complete universe expression. -/
private def decodeLevel : TransferLevel → Level
  | .zero => .zero
  | .succ value => .succ (decodeLevel value)
  | .max left right => .max (decodeLevel left) (decodeLevel right)
  | .imax left right => .imax (decodeLevel left) (decodeLevel right)
  | .param name => .param (decodeName name)

/-- An expression node whose children refer only to preceding table entries. -/
private inductive TransferNode where
  | bvar (index : Nat)
  | alias (index : Nat)
  | sort (level : TransferLevel)
  | const (name : TransferName) (levels : List TransferLevel)
  | app (fn argument : Nat)
  | lam (name : TransferName) (type body binder : Nat)
  | forallE (name : TransferName) (type body binder : Nat)
  | letE (name : TransferName) (type value body : Nat) (nondep : Bool)
  | natLit (value : Nat)
  | strLit (value : String)
  | proj (type : TransferName) (index value : Nat)
  deriving ToJson, FromJson

/-- Preserve all four kernel binder annotations. -/
private def encodeBinder : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- Reject unknown annotations rather than treating them as explicit binders. -/
private def decodeBinder : Nat → Except String BinderInfo
  | 0 => pure .default
  | 1 => pure .implicit
  | 2 => pure .strictImplicit
  | 3 => pure .instImplicit
  | _ => throw "Invalid full-verification binder annotation"

/-- Reject forward, cyclic and missing node references rather than supplying a default term. -/
private def preceding (nodes : Array Expr) (index : Nat) : Except String Expr :=
  match nodes[index]? with
  | some expression => pure expression
  | none => throw "Invalid full-verification expression reference"

/-- Restore one exact expression node from the already decoded prefix. -/
private def decodeNode (nodes : Array Expr) : TransferNode → Except String Expr
  | .bvar index => pure (.bvar index)
  | .alias index => preceding nodes index
  | .sort level => pure (.sort (decodeLevel level))
  | .const name levels => pure (.const (decodeName name) (levels.map decodeLevel))
  | .app fn argument => return .app (← preceding nodes fn) (← preceding nodes argument)
  | .lam name type body binder => return (.lam (decodeName name)
      (← preceding nodes type) (← preceding nodes body) (← decodeBinder binder))
  | .forallE name type body binder => return (.forallE (decodeName name)
      (← preceding nodes type) (← preceding nodes body) (← decodeBinder binder))
  | .letE name type value body nondep => return (.letE (decodeName name)
      (← preceding nodes type) (← preceding nodes value) (← preceding nodes body) nondep)
  | .natLit value => pure (.lit (.natVal value))
  | .strLit value => pure (.lit (.strVal value))
  | .proj type index value => return .proj (decodeName type) index (← preceding nodes value)

/-- Decode the transferred type and body. This only constructs expressions: generated
    declarations still require kernel type checking and independent replay. -/
def decode (source : String) (type body : Nat) : Except String (Expr × Expr) := do
  let table : Array TransferNode ← fromJson? (← Json.parse source)
  let mut nodes := #[]
  for node in table do nodes := nodes.push (← decodeNode nodes node)
  return (← preceding nodes type, ← preceding nodes body)

/-- Shared expression nodes within one transferred declaration. -/
private structure ExpressionSource where
  nodes : ExprStructMap Nat := {}
  table : Array TransferNode := #[]

/-- Encode exact expression structure once, with constants renamed by the checked mapping.
    Metadata is dropped; free and meta variables are rejected. -/
private def exprSource (environment : Environment) (shared : Std.HashSet Name)
    (targetNamespace : Name) (expression : Expr) :
    StateT ExpressionSource (Except String) Nat := do
  if let some index := (← get).nodes[ExprStructEq.mk expression]? then return index
  let node : TransferNode ← match expression with
    | .bvar index => pure (.bvar index)
    | .fvar _ => throw "Full verification cannot transfer free variables"
    | .mvar _ => throw "Full verification cannot transfer metavariables"
    | .sort level => pure (.sort (← encodeLevel level))
    | .const name levels => pure (.const
        (encodeName (← mapped environment shared targetNamespace name))
        (← liftM (levels.mapM encodeLevel)))
    | .app fn argument => pure (.app (← exprSource environment shared targetNamespace fn)
        (← exprSource environment shared targetNamespace argument))
    | .lam name type body info => pure (.lam (encodeName name)
        (← exprSource environment shared targetNamespace type)
        (← exprSource environment shared targetNamespace body) (encodeBinder info))
    | .forallE name type body info => pure (.forallE (encodeName name)
        (← exprSource environment shared targetNamespace type)
        (← exprSource environment shared targetNamespace body) (encodeBinder info))
    | .letE name type value body nondep => pure (.letE (encodeName name)
        (← exprSource environment shared targetNamespace type)
        (← exprSource environment shared targetNamespace value)
        (← exprSource environment shared targetNamespace body) nondep)
    | .lit (.natVal value) => pure (.natLit value)
    | .lit (.strVal value) => pure (.strLit value)
    | .mdata _ value => pure (.alias (← exprSource environment shared targetNamespace value))
    | .proj type index value => pure (.proj
        (encodeName (← mapped environment shared targetNamespace type)) index
        (← exprSource environment shared targetNamespace value))
  let state ← get
  let index := state.table.size
  set { state with nodes := state.nodes.insert ⟨expression⟩ index, table := state.table.push node }
  return index

/-- The body of a definition, theorem or opaque; unsafe and partial declarations and other
    kinds are rejected. -/
private def value (info : ConstantInfo) : Except String Expr :=
  if info.isUnsafe || info.isPartial then
    .error ("Unsafe full-verification declaration: " ++ info.name.toString)
  else match info with
  | .defnInfo info => .ok info.value
  | .thmInfo info => .ok info.value
  | .opaqueInfo info => .ok info.value
  | _ => .error ("Unsupported full-verification declaration kind: " ++ info.name.toString)

/-- A `run_cmd` that adds `info` under its new name with kernel checking on, and fails if
    that name already exists. -/
private def declarationSource (environment : Environment) (shared : Std.HashSet Name)
    (targetNamespace : Name) (info : ConstantInfo) : Except String String := do
  let target := nameSource (targetNamespace ++ info.name)
  let (type, expressions) ← (exprSource environment shared targetNamespace info.type).run {}
  let (body, expressions) ←
    (exprSource environment shared targetNamespace (← value info)).run expressions
  let common := "name := " ++ target ++ ", levelParams := " ++
    listSource (info.levelParams.map nameSource) ++ ", type := transferredType, value := transferredBody"
  let declaration <- match info with
    | .defnInfo info =>
      let hints := match info.hints with
        | .opaque => "Lean.ReducibilityHints.opaque"
        | .abbrev => "Lean.ReducibilityHints.abbrev"
        | .regular height =>
          "(Lean.ReducibilityHints.regular (UInt32.ofNat " ++ toString height.toNat ++ "))"
      pure ("Lean.Declaration.defnDecl { " ++ common ++ ", hints := " ++ hints ++
        ", safety := .safe }")
    | .thmInfo _ => pure ("Lean.Declaration.thmDecl { " ++ common ++ " }")
    | .opaqueInfo _ => pure ("Lean.Declaration.opaqueDecl { " ++ common ++ ", isUnsafe := false }")
    | _ => throw "Unsupported full-verification declaration"
  return "run_cmd Lean.Elab.Command.liftCoreM do\n" ++
    "  let (transferredType, transferredBody) ←\n" ++
    "    match CIL.Interface.FullTransfer.decode " ++ quoted (toJson expressions.table).compress ++
      " " ++ toString type ++ " " ++ toString body ++ " with\n" ++
    "    | .ok terms => pure terms\n" ++
    "    | .error error => throwError error\n" ++
    "  if (<- Lean.getEnv).contains " ++ target ++
      " then throwError \"Full-verification destination already exists\"\n" ++
    "  Lean.withOptions (fun options => options.setBool `debug.skipKernelTC false) do\n" ++
    "    Lean.addDecl (" ++ declaration ++ ")\n"

/-- Progress of the depth-first transfer: `active` holds the declarations being visited,
    for cycle detection, and `sources` the emitted declarations in dependency order. -/
private structure TransferState where
  visited : Std.HashSet Name := {}
  active : Std.HashSet Name := {}
  imports : Std.HashSet Name := {}
  sources : Array String := #[]

/-- Emits `name` after its dependencies; a shared declaration is imported instead. -/
private partial def visit (environment : Environment) (shared : Std.HashSet Name)
    (targetNamespace name : Name) (state : TransferState) : Except String TransferState := do
  if state.visited.contains name then return state
  let some info := environment.find? name |
    throw ("Missing full-verification declaration: " ++ name.toString)
  if shared.contains (CIL.Interface.definingModule environment name) then
    return { state with
      visited := state.visited.insert name
      imports := state.imports.insert (CIL.Interface.definingModule environment name) }
  if state.active.contains name then
    throw ("Cyclic full-verification declaration: " ++ name.toString)
  let body <- value info
  let mut state := { state with active := state.active.insert name }
  for dependency in expressionDependencies info.type ++ expressionDependencies body do
    state <- visit environment shared targetNamespace dependency state
  let source <- declarationSource environment shared targetNamespace info
  return { state with
    visited := state.visited.insert name, active := state.active.erase name,
    sources := state.sources.push source }

/-- A Lean source file: imports of the shared modules reached, then every non-shared
    declaration that `roots` depend on, in dependency order under `targetNamespace`. -/
def capture (environment : Environment) (sharedModules : Array Name) (targetNamespace : Name)
    (roots : Array Name) : Except String String := do
  let shared := sharedModules.foldl (fun found name => found.insert name) ({} : Std.HashSet Name)
  let mut state : TransferState := {}
  for root in roots do state <- visit environment shared targetNamespace root state
  let imports := state.imports.toArray.toList.mergeSort
    (fun left right => left.toString <= right.toString)
  return String.intercalate "\n" (imports.map (fun name => "import " ++ name.toString)) ++
    "\nimport CIL.Interface.FullTransfer\n\n" ++
      String.intercalate "\n" state.sources.toList

end CIL.Interface.FullTransfer
