import Lean

/-!
# Contract closures

A library publishes its method contracts in an interface module. A consumer must know
that a contract means exactly what it meant when the library was certified, so
`contractClosure` serializes everything an exported contract depends on outside the
trusted modules (`CIL`, `Init`, `Std`, `Lean`) as canonical JSON, independent of binder and
universe-parameter names; `closureDigest` is computed from it. `validateInterfaceDeclarations`
rejects `sorry`, unapproved axioms, and unsafe, partial or valueless declarations anywhere
an interface module reaches. `leancil-audit` runs both on kernel-replayed `.olean` files.
-/

namespace CIL.Interface
open Lean

/-- A JSON array whose first element is the node's tag. -/
private def node (tag : String) (items : List Json := []) : Json :=
  Json.arr (#[Json.str tag] ++ items.toArray)

private def number (value : Nat) : Json := toJson value

/-- A name, component by component. -/
private def canonicalName : Name -> Json
  | .anonymous => node "anonymous"
  | .str parent value => node "str" [canonicalName parent, Json.str value]
  | .num parent value => node "num" [canonicalName parent, number value]

/-- Universe parameters are serialized by position, so renaming one changes nothing. -/
private def parameterIndex (parameters : List Name) (name : Name) : Except String Nat :=
  match parameters.idxOf? name with
  | some index => .ok index
  | none => .error ("Unbound universe parameter: " ++ name.toString)

/-- A universe level; metavariables are rejected. -/
private def canonicalLevel (parameters : List Name) : Level -> Except String Json
  | .zero => pure (node "zero")
  | .succ level => return node "succ" [<- canonicalLevel parameters level]
  | .max left right =>
    return node "max" [<- canonicalLevel parameters left, <- canonicalLevel parameters right]
  | .imax left right =>
    return node "imax" [<- canonicalLevel parameters left, <- canonicalLevel parameters right]
  | .param name => return node "parameter" [number (<- parameterIndex parameters name)]
  | .mvar _ => .error "Unresolved universe metavariable in contract closure"

private def binder : BinderInfo -> String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

/-- An expression under `depth` binders. Bound variables are de Bruijn indices, binder names
    and metadata are dropped, and free, loose or meta variables are rejected. -/
private def expression (parameters : List Name) (depth : Nat) : Expr -> Except String Json
  | .bvar index =>
    if index < depth then pure (node "bound" [number index])
    else .error "Unbound de Bruijn variable in contract closure"
  | .fvar _ => .error "Free variable in contract closure"
  | .mvar _ => .error "Metavariable in contract closure"
  | .sort level => return node "sort" [<- canonicalLevel parameters level]
  | .const name levels =>
    return node "constant" [canonicalName name, toJson (<- levels.mapM (canonicalLevel parameters))]
  | .app fn argument =>
    return node "application"
      [<- expression parameters depth fn, <- expression parameters depth argument]
  | .lam _ type body info =>
    return node "lambda" [Json.str (binder info), <- expression parameters depth type,
      <- expression parameters (depth + 1) body]
  | .forallE _ type body info =>
    return node "forall" [Json.str (binder info), <- expression parameters depth type,
      <- expression parameters (depth + 1) body]
  | .letE _ type value body _ =>
    return node "let" [<- expression parameters depth type, <- expression parameters depth value,
      <- expression parameters (depth + 1) body]
  | .lit (.natVal value) => pure (node "natural" [number value])
  | .lit (.strVal value) => pure (node "string" [Json.str value])
  | .mdata _ value => expression parameters depth value
  | .proj type index value =>
    return node "projection"
      [canonicalName type, number index, <- expression parameters depth value]

/-- The canonical form of a closed expression, tagged with its format version. -/
def canonicalExpression (value : Expr) (levelParams : List Name := []) : Except String String :=
  return (node "leancil-expression-1" [<- expression levelParams 0 value]).compress

/-- The module that declares `constant`; the current file's own constants map to
    `mainModule`. -/
def definingModule (environment : Environment) (constant : Name) : Name :=
  match environment.getModuleIdxFor? constant with
  | some index => environment.header.moduleNames[index]!
  | none => environment.mainModule

/-- Modules whose declarations a closure names but does not serialize. -/
private def trustedModule (name : Name) : Bool :=
  name == `CIL || (`CIL).isPrefixOf name || name == `Init || (`Init).isPrefixOf name ||
  name == `Std || (`Std).isPrefixOf name || name == `Lean || (`Lean).isPrefixOf name

/-- Every constant an expression mentions, with repetitions. -/
def expressionConstants : Expr -> List Name
  | .const name _ => [name]
  | .app fn argument => expressionConstants fn ++ expressionConstants argument
  | .lam _ type body _ | .forallE _ type body _ =>
    expressionConstants type ++ expressionConstants body
  | .letE _ type value body _ =>
    expressionConstants type ++ expressionConstants value ++ expressionConstants body
  | .mdata _ value => expressionConstants value
  | .proj type _ value => type :: expressionConstants value
  | _ => []

/-- The parts of a declaration that determine its meaning: its type, a definition's or
    opaque's value, and a recursor's computation rules. Proofs are excluded. -/
private def semanticExpressions (info : ConstantInfo) : List Expr :=
  info.type :: match info with
  | .defnInfo value => [value.value]
  | .opaqueInfo value => [value.value]
  | .recInfo value => value.rules.map (fun rule => rule.rhs)
  | _ => []

/-- Declarations that come with this one: an inductive family's members and constructors,
    a constructor's inductive, a recursor's family and rule constructors. -/
private def related (info : ConstantInfo) : List Name :=
  match info with
  | .inductInfo value => value.all ++ value.ctors
  | .ctorInfo value => [value.induct]
  | .recInfo value => value.all ++ value.rules.map (fun rule => rule.ctor)
  | _ => []

/-- The only axioms a contract interface may depend on, transitively. -/
def approvedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]

/-- Rejects `sorry`, unsafe and partial declarations, unapproved axioms, and opaques that
    are their own value. -/
private def permitted (info : ConstantInfo) : Except String Unit := do
  if info.name == `sorryAx then throw "sorry in contract interface"
  if info.isUnsafe || info.isPartial then
    throw ("Unsafe or partial declaration in contract interface: " ++ info.name.toString)
  match info with
  | .axiomInfo _ =>
    if !approvedAxioms.contains info.name then
      throw ("Axiom in contract interface: " ++ info.name.toString)
  | .opaqueInfo value =>
    if value.value.getAppFn.constName? == some info.name then
      throw ("Valueless opaque in contract interface: " ++ info.name.toString)
  | _ => pure ()

/-- The canonical form of one untrusted declaration; a theorem contributes only its type. -/
private def declaration (info : ConstantInfo) : Except String Json := do
  let type <- expression info.levelParams 0 info.type
  let header := [canonicalName info.name, number info.numLevelParams, type]
  match info with
  | .defnInfo value =>
    return node "definition" (header ++ [<- expression info.levelParams 0 value.value])
  | .opaqueInfo value =>
    return node "opaque" (header ++ [<- expression info.levelParams 0 value.value])
  | .thmInfo _ => return node "theorem" header
  | .inductInfo value =>
    return node "inductive" (header ++ [number value.numParams, number value.numIndices,
      toJson (value.all.map canonicalName), toJson (value.ctors.map canonicalName),
      number value.numNested, toJson value.isRec, toJson value.isReflexive])
  | .ctorInfo value => return node "constructor" (header ++ [canonicalName value.induct,
      number value.cidx, number value.numParams, number value.numFields])
  | .recInfo value =>
    let rules <- value.rules.mapM fun rule => do
      return node "rule"
        [canonicalName rule.ctor, number rule.nfields, <- expression info.levelParams 0 rule.rhs]
    return node "recursor" (header ++ [toJson (value.all.map canonicalName),
      number value.numParams, number value.numIndices, number value.numMotives,
      number value.numMinors, number value.getMajorIdx, number value.getFirstIndexIdx,
      number value.getFirstMinorIdx, canonicalName value.getMajorInduct, toJson value.k,
      toJson rules])
  | .axiomInfo _ => throw ("Unexpected local axiom in canonical closure: " ++ info.name.toString)
  | .quotInfo _ => throw ("Unexpected local quotient declaration: " ++ info.name.toString)

/-- The constants a theorem's proof mentions. -/
private def proofDependencies : ConstantInfo -> List Name
  | .thmInfo value => expressionConstants value.value
  | _ => []

private def semanticDependencies (info : ConstantInfo) : List Name :=
  related info ++ (semanticExpressions info).flatMap expressionConstants

/-- One walk over everything `roots` reach, visiting each declaration once. Untrusted
declarations, and the trusted ones they name, must be `permitted`; every reachable axiom,
trusted or not, must be approved. With `serialize`, untrusted declarations reached through
types, values and inductive families (not proofs) are serialized. Kernel declarations are
read directly, never an axiom summary. -/
private def walk (environment : Environment) (roots : List Name) (serialize : Bool) :
    Except String (List (String × Json)) := do
  let lookup (name : Name) : Except String ConstantInfo := match environment.find? name with
    | some info => pure info
    | none => throw ("Missing declaration in contract closure: " ++ name.toString)
  let mut visited : Std.HashSet Name := {}
  let mut entries : List (String × Json) := []
  let mut semantic := if serialize then roots else []
  let mut proofs := if serialize then [] else roots
  -- Both untrusted stacks drain first, so trusted declarations are walked for axioms only.
  let mut trusted : List Name := []
  repeat
    if let name :: rest := semantic then
      semantic := rest
      unless visited.contains name do
        let info <- lookup name
        permitted info
        if trustedModule (definingModule environment name) then
          trusted := name :: trusted
        else
          visited := visited.insert name
          entries := (canonicalName name |>.compress, <- declaration info) :: entries
          semantic := semanticDependencies info ++ semantic
          proofs := proofDependencies info ++ proofs
    else if let name :: rest := proofs then
      proofs := rest
      unless visited.contains name do
        let info <- lookup name
        permitted info
        if trustedModule (definingModule environment name) then
          trusted := name :: trusted
        else
          visited := visited.insert name
          proofs := semanticDependencies info ++ proofDependencies info ++ proofs
    else if let name :: rest := trusted then
      trusted := rest
      unless visited.contains name do
        visited := visited.insert name
        let info <- lookup name
        if let .axiomInfo _ := info then
          unless approvedAxioms.contains name do
            throw ("Unapproved transitive axiom in contract interface: " ++ name.toString)
        trusted := semanticDependencies info ++ proofDependencies info ++ trusted
    else break
  return entries

/-- Every declaration of `interfaceModules`, and everything it reaches including proofs,
    passes the interface checks. -/
def validateInterfaceDeclarations (environment : Environment) (interfaceModules : Array Name) :
    Except String Unit := do
  if interfaceModules.isEmpty then return
  let declarations := environment.constants.toList.filterMap fun (name, _) =>
    if interfaceModules.contains (definingModule environment name) then some name else none
  discard <| walk environment declarations false

/-- The kind (`method` or `outcome`) and canonical closure of an exported contract constant,
    whose type must be `MethodContract` or `OutcomeContract`. Entries are sorted by name. -/
def contractClosure (environment : Environment) (constant : Name) :
    Except String (String × String) := do
  let some info := environment.find? constant |
    throw ("Missing contract constant: " ++ constant.toString)
  let kind <- match info.type.getAppFn.constName? with
    | some name =>
      if name == `CIL.Safety.MethodContract then pure "method"
      else if name == `CIL.Safety.OutcomeContract then pure "outcome"
      else throw "Export must have the canonical MethodContract or OutcomeContract type"
    | none => throw "Export must be a closed contract constant"
  let entries <- walk environment [constant] true
  let ordered := entries.mergeSort (fun left right => left.1 <= right.1)
  return (kind, (node "leancil-contract-closure-1" [canonicalName constant, Json.str kind,
    toJson (ordered.map Prod.snd)]).compress)

open Elab Command in
/-- Prints a contract closure for authoring; verification computes it in `leancil-audit` instead. -/
elab "#leancil_contract_closure " constant:ident : command => do
  let name <- resolveGlobalConstNoOverload constant
  let (kind, canonical) <- match contractClosure (<- getEnv) name with
    | .ok value => pure value
    | .error message => throwError "{message}"
  logInfo (Json.mkObj [("constant", toJson name.toString), ("kind", toJson kind),
    ("canonical", toJson canonical)]).compress

end CIL.Interface
