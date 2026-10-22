import CIL.Interface.Closure

namespace CIL.Interface.FullTransfer
open Lean

private def quoted (value : String) : String := (Json.str value).compress

private def nameSource : Name -> String
  | .anonymous => "Lean.Name.anonymous"
  | .str parent value => "(Lean.Name.str " ++ nameSource parent ++ " " ++ quoted value ++ ")"
  | .num parent value => "(Lean.Name.num " ++ nameSource parent ++ " " ++ toString value ++ ")"

private def listSource (values : List String) : String := "[" ++ String.intercalate ", " values ++ "]"

private def levelSource : Level -> Except String String
  | .zero => pure "Lean.Level.zero"
  | .succ value => return "(Lean.Level.succ " ++ (<- levelSource value) ++ ")"
  | .max left right => return "(Lean.Level.max " ++ (<- levelSource left) ++ " " ++ (<- levelSource right) ++ ")"
  | .imax left right => return "(Lean.Level.imax " ++ (<- levelSource left) ++ " " ++ (<- levelSource right) ++ ")"
  | .param name => pure ("(Lean.Level.param " ++ nameSource name ++ ")")
  | .mvar _ => throw "Full verification cannot transfer universe metavariables"

private def mapped (environment : Environment) (shared : Std.HashSet Name) (targetNamespace name : Name) : Except String Name := do
  unless environment.contains name do throw ("Missing full-verification dependency: " ++ name.toString)
  if shared.contains (CIL.Interface.definingModule environment name) then return name
  return targetNamespace ++ name

private def binderSource : BinderInfo -> String
  | .default => "Lean.BinderInfo.default"
  | .implicit => "Lean.BinderInfo.implicit"
  | .strictImplicit => "Lean.BinderInfo.strictImplicit"
  | .instImplicit => "Lean.BinderInfo.instImplicit"

private def exprSource (environment : Environment) (shared : Std.HashSet Name) (targetNamespace : Name) : Expr -> Except String String
  | .bvar index => pure ("(Lean.Expr.bvar " ++ toString index ++ ")")
  | .fvar _ => throw "Full verification cannot transfer free variables"
  | .mvar _ => throw "Full verification cannot transfer metavariables"
  | .sort level => return "(Lean.Expr.sort " ++ (<- levelSource level) ++ ")"
  | .const name levels => return ("(Lean.Expr.const " ++ nameSource (<- mapped environment shared targetNamespace name) ++ " " ++
      listSource (<- levels.mapM levelSource) ++ ")")
  | .app fn argument => return ("(Lean.Expr.app " ++ (<- exprSource environment shared targetNamespace fn) ++ " " ++
      (<- exprSource environment shared targetNamespace argument) ++ ")")
  | .lam name type body info => return ("(Lean.Expr.lam " ++ nameSource name ++ " " ++
      (<- exprSource environment shared targetNamespace type) ++ " " ++ (<- exprSource environment shared targetNamespace body) ++ " " ++ binderSource info ++ ")")
  | .forallE name type body info => return ("(Lean.Expr.forallE " ++ nameSource name ++ " " ++
      (<- exprSource environment shared targetNamespace type) ++ " " ++ (<- exprSource environment shared targetNamespace body) ++ " " ++ binderSource info ++ ")")
  | .letE name type value body nondep => return ("(Lean.Expr.letE " ++ nameSource name ++ " " ++
      (<- exprSource environment shared targetNamespace type) ++ " " ++ (<- exprSource environment shared targetNamespace value) ++ " " ++
      (<- exprSource environment shared targetNamespace body) ++ " " ++ toString nondep ++ ")")
  | .lit (.natVal value) => pure ("(Lean.Expr.lit (Lean.Literal.natVal " ++ toString value ++ "))")
  | .lit (.strVal value) => pure ("(Lean.Expr.lit (Lean.Literal.strVal " ++ quoted value ++ "))")
  | .mdata _ value => exprSource environment shared targetNamespace value
  | .proj type index value => return ("(Lean.Expr.proj " ++ nameSource (<- mapped environment shared targetNamespace type) ++ " " ++
      toString index ++ " " ++ (<- exprSource environment shared targetNamespace value) ++ ")")

private def dependencies : Expr -> List Name
  | .const name _ => [name]
  | .app fn argument => dependencies fn ++ dependencies argument
  | .lam _ type body _ | .forallE _ type body _ => dependencies type ++ dependencies body
  | .letE _ type value body _ => dependencies type ++ dependencies value ++ dependencies body
  | .mdata _ value => dependencies value
  | .proj type _ value => type :: dependencies value
  | _ => []

private def value (info : ConstantInfo) : Except String Expr :=
  if info.isUnsafe || info.isPartial then .error ("Unsafe full-verification declaration: " ++ info.name.toString)
  else match info with
  | .defnInfo info => .ok info.value
  | .thmInfo info => .ok info.value
  | .opaqueInfo info => .ok info.value
  | _ => .error ("Unsupported full-verification declaration kind: " ++ info.name.toString)

private def declarationSource (environment : Environment) (shared : Std.HashSet Name) (targetNamespace : Name)
    (info : ConstantInfo) : Except String String := do
  let target := nameSource (targetNamespace ++ info.name)
  let type <- exprSource environment shared targetNamespace info.type
  let body <- exprSource environment shared targetNamespace (<- value info)
  let common := "name := " ++ target ++ ", levelParams := " ++ listSource (info.levelParams.map nameSource) ++
    ", type := " ++ type ++ ", value := " ++ body
  let declaration <- match info with
    | .defnInfo info =>
      let hints := match info.hints with
        | .opaque => "Lean.ReducibilityHints.opaque"
        | .abbrev => "Lean.ReducibilityHints.abbrev"
        | .regular height => "(Lean.ReducibilityHints.regular (UInt32.ofNat " ++ toString height.toNat ++ "))"
      pure ("Lean.Declaration.defnDecl { " ++ common ++ ", hints := " ++ hints ++ ", safety := .safe }")
    | .thmInfo _ => pure ("Lean.Declaration.thmDecl { " ++ common ++ " }")
    | .opaqueInfo _ => pure ("Lean.Declaration.opaqueDecl { " ++ common ++ ", isUnsafe := false }")
    | _ => throw "Unsupported full-verification declaration"
  return "run_cmd Lean.Elab.Command.liftCoreM do\n" ++
    "  if (<- Lean.getEnv).contains " ++ target ++ " then throwError \"Full-verification destination already exists\"\n" ++
    "  Lean.withOptions (fun options => options.setBool `debug.skipKernelTC false) do\n" ++
    "    Lean.addDecl (" ++ declaration ++ ")\n"

private structure TransferState where
  visited : Std.HashSet Name := {}
  active : Std.HashSet Name := {}
  imports : Std.HashSet Name := {}
  sources : Array String := #[]

private partial def visit (environment : Environment) (shared : Std.HashSet Name) (targetNamespace name : Name)
    (state : TransferState) : Except String TransferState := do
  if state.visited.contains name then return state
  let some info := environment.find? name | throw ("Missing full-verification declaration: " ++ name.toString)
  if shared.contains (CIL.Interface.definingModule environment name) then
    return { state with
      visited := state.visited.insert name
      imports := state.imports.insert (CIL.Interface.definingModule environment name) }
  if state.active.contains name then throw ("Cyclic full-verification declaration: " ++ name.toString)
  let body <- value info
  let mut state := { state with active := state.active.insert name }
  for dependency in dependencies info.type ++ dependencies body do
    state <- visit environment shared targetNamespace dependency state
  let source <- declarationSource environment shared targetNamespace info
  return { state with visited := state.visited.insert name, active := state.active.erase name, sources := state.sources.push source }

def capture (environment : Environment) (sharedModules : Array Name) (targetNamespace : Name) (roots : Array Name) : Except String String := do
  let shared := sharedModules.foldl (fun found name => found.insert name) ({} : Std.HashSet Name)
  let mut state : TransferState := {}
  for root in roots do state <- visit environment shared targetNamespace root state
  let imports := state.imports.toArray.toList.mergeSort (fun left right => left.toString <= right.toString)
  return String.intercalate "\n" (imports.map (fun name => "import " ++ name.toString)) ++
    "\nimport Lean\n\n" ++ String.intercalate "\n" state.sources.toList

end CIL.Interface.FullTransfer
