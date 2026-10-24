import Lean
import CIL.Interface.Closure

/-!
# Olean audit

`leancil-audit REQUEST RESULT` audits compiled `.olean` files without elaborating any source.

It imports `modules` with `loadExts := false`, so no imported environment extension, attribute,
elaborator, notation or `initialize` runs; only constant declarations are read. The toolchain's
library precedes `LEAN_PATH`, so a user module cannot shadow `Init`, `Std` or `Lean`.

REQUEST (JSON):
  { "modules":   ["Proof", ...],
    "theorems":  [{ "name": N, "type": E?, "levelParams": [u, ...]?, "axioms": [N, ...],
                    "statement": bool?, "refutation": bool? }],
    "constants": [{ "name": N, "value": E, "type": E?, "axioms": [N, ...]? }],
    "interfaces": [M, ...]?, "closures": [{ "name": N }]?,
    "namespaces": { "prefixes": [P, ...], "axioms": [N, ...] }? }
A theorem must be a `theorem` whose type matches `E` (when given) and whose axiom closure is
in `axioms`. A constant must be a definition whose value (and type) match. Every declaration
of the `interfaces` modules must pass `CIL.Interface.validateInterfaceDeclarations`, and each
`closures` entry reports `CIL.Interface.contractClosure`: its contract kind and canonical
closure. `namespaces` audits every `theorem` that one of `modules` declares under a namespace
prefix `P` (`A.` or `A`: whole name components, private names by their user name), and fails
when any prefix matches none or any axiom closure leaves `axioms`.
Expected expressions `E`:
  "_"                                any expression
  {"const": N, "levels": [L, ...]}   constant; `levels` defaults to []
  {"app": [E, E1, ..., En]}          `E` applied to exactly the trailing n arguments
  {"nat": n}                         the canonical numeral `@OfNat.ofNat Nat n (instOfNatNat n)`
  {"lit": n} / {"str": s}            raw literals
  {"sort": L} / {"bvar": i}
  {"forall": [E, E]} / {"lam": [E, E]}   binder type and body; names and binder info ignored
Levels L: n (the n-th successor of zero), {"param": u}, {"succ": L}, {"max": [L, L]},
{"imax": [L, L]}.
Comparison is structural after removing metadata: no unfolding, instances or elaboration.

RESULT (JSON):
  { "modules": { N: olean path },
    "theorems":  [{ "name": N, "error": string?, "axioms": [N, ...], "statement": string?,
                    "refutes": { "contract": N, "line": n, "column": n }? }],
    "constants": [{ "name": N, "error": string?, "axioms": [N, ...] }],
    "interfaces": { "error": string? },
    "closures": [{ "name": N, "error": string?, "kind": string?, "canonical": string? }],
    "namespaces": { "count": n, "prefixes": { P: n }, "modules": { M: n }, "axioms": [N, ...],
                    "rejected": [{ "name": N, "axioms": [N, ...], "error": string }],
                    "error": string? }? }
Per-item failures are reported in `error`; a missing module or malformed request exits nonzero.
-/

namespace LeanCILAudit
open Lean

/-- The declaration name written as `s`. -/
def name (s : String) : Name := s.toName

/-- Decodes an expected universe level `L`. -/
partial def level (j : Json) : Except String Level := do
  if let .ok n := j.getNat? then return (List.range n).foldl (fun l _ => .succ l) .zero
  if let .ok p := j.getObjValAs? String "param" then return .param (name p)
  if let .ok l := j.getObjVal? "succ" then return .succ (← level l)
  if let .ok #[a, b] := j.getObjValAs? (Array Json) "max" then return .max (← level a) (← level b)
  if let .ok #[a, b] := j.getObjValAs? (Array Json) "imax" then return .imax (← level a) (← level b)
  throw s!"Invalid level {j.compress}"

/-- The canonical `Nat` numeral `@OfNat.ofNat Nat n (instOfNatNat n)`. -/
def canonicalNat (n : Nat) : Expr :=
  mkApp3 (.const `OfNat.ofNat [.zero]) (.const `Nat []) (.lit (.natVal n))
    (mkApp (.const `instOfNatNat []) (.lit (.natVal n)))

/-- Whether `e` (without metadata) matches the expected expression `j`. -/
partial def fits (j : Json) (e : Expr) : Except String Bool := do
  if j == .str "_" then return true
  if let .ok c := j.getObjValAs? String "const" then
    let levels ← match j.getObjValAs? (Array Json) "levels" with
      | .ok ls => ls.toList.mapM level
      | .error _ => pure []
    return e == .const (name c) levels
  if let .ok parts := j.getObjValAs? (Array Json) "app" then
    let some head := parts[0]? | throw "Empty application"
    let args := parts.extract 1
    let mut fn := e
    let mut actual := #[]
    for _ in args do
      let .app f a := fn | return false
      actual := actual.push a
      fn := f
    unless ← fits head fn do return false
    for spec in args, arg in actual.reverse do
      unless ← fits spec arg do return false
    return true
  if let .ok n := j.getObjValAs? Nat "nat" then return e == canonicalNat n
  if let .ok n := j.getObjValAs? Nat "lit" then return e == .lit (.natVal n)
  if let .ok s := j.getObjValAs? String "str" then return e == .lit (.strVal s)
  if let .ok l := j.getObjVal? "sort" then return e == .sort (← level l)
  if let .ok i := j.getObjValAs? Nat "bvar" then return e == .bvar i
  for (key, binder) in [("forall", true), ("lam", false)] do
    if let .ok #[t, b] := j.getObjValAs? (Array Json) key then
      match e, binder with
      | .forallE _ ty body _, true | .lam _ ty body _, false =>
        return (← fits t ty) && (← fits b body)
      | _, _ => return false
  throw s!"Invalid expression {j.compress}"

/-- Expressions of a declaration whose constants it depends on, as the kernel sees it. -/
def parts : ConstantInfo → Array Expr
  | .axiomInfo v => #[v.type]
  | .defnInfo v => #[v.type, v.value]
  | .thmInfo v => #[v.type, v.value]
  | .opaqueInfo v => #[v.type, v.value]
  | .ctorInfo v => #[v.type, .const v.induct []]
  | .recInfo v => #[v.type] ++ v.all.toArray.map (Expr.const · [])
  | .inductInfo v => #[v.type] ++ v.ctors.toArray.map (Expr.const · [])
  | .quotInfo v => #[v.type]

/-- Axioms reachable from any of `roots`, in one walk that shares visited declarations; olean
    axiom summaries are ignored. -/
def axiomClosureOf (env : Kernel.Environment) (roots : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut pending := roots
  let mut axioms : NameSet := {}
  while h : pending.size > 0 do
    let c := pending[pending.size - 1]
    pending := pending.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some info := env.find? c | continue
    if info matches .axiomInfo _ then axioms := axioms.insert c
    for e in parts info do
      for d in e.getUsedConstants do
        unless seen.contains d do pending := pending.push d
  return axioms.toArray.qsort Name.lt

/-- Axioms reachable from `root`, walking kernel declarations only. -/
def axiomClosure (env : Kernel.Environment) (root : Name) : Array Name := axiomClosureOf env #[root]

/-- `e` with every metadata node removed, so comparison sees only kernel structure. -/
partial def stripMData (e : Expr) : Expr := e.replace fun
  | .mdata _ b => some (stripMData b)
  | _ => none

/-- The contract predicates whose negation a refutation theorem may state. -/
def contracts : List Name :=
  [`CIL.Safety.MethodContract.Holds, `CIL.Safety.OutcomeContract.Holds,
    `CIL.Safety.OutcomeContract.HoldsCLR]

/-- The context for pretty-printing and source ranges; no elaboration runs in it. -/
def coreContext : Core.Context :=
  { fileName := "<leancil-audit>", fileMap := default, maxHeartbeats := 200000 * 1000,
    maxRecDepth := 4096, options := ({} : Options).insert `pp.fieldNotation (.ofBool false) }

/-- Runs a `CoreM` action against the imported environment. -/
def run (env : Environment) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO coreContext { env }
  return a

/-- `thm : type`, pretty-printed for the report. -/
def statement (env : Environment) (thm : Name) (type : Expr) : IO String :=
  run env do return s!"{thm} : {← Meta.MetaM.run' (PrettyPrinter.ppExpr type)}"

/-- When `type` negates a contract predicate applied to arguments, that contract and the
    source position of `thm`; otherwise `none`. -/
def refutation (env : Environment) (thm : Name) (type : Expr) : IO (Option Json) := do
  let .app (.const `Not _) claim := type | return none
  let .const contract _ := claim.getAppFn | return none
  unless contracts.contains contract do return none
  let some ranges ← run env (findDeclarationRanges? thm)
    | throw (IO.userError s!"Missing refutation location for {thm}")
  return some <| Json.mkObj [("contract", toJson contract.toString),
    ("line", toJson ranges.selectionRange.pos.line),
    ("column", toJson ranges.selectionRange.pos.column)]

/-- The names listed under `key`; empty when it is absent or not a string array. -/
def names (j : Json) (key : String) : Array Name :=
  (j.getObjValAs? (Array String) key).toOption.getD #[] |>.map name

/-- An error naming every axiom in `found` that is not `allowed`, or `none`. -/
def checkAxioms (allowed : Array Name) (found : Array Name) : Option String :=
  let bad := found.filter (!allowed.contains ·)
  if bad.isEmpty then none
  else some s!"Unapproved proof axioms: {", ".intercalate (bad.toList.map toString)}"

/-- Audits one `theorems` entry: kind, level parameters and type, and axiom closure. -/
def theorem? (env : Environment) (req : Json) : IO Json := do
  let thm := name (← IO.ofExcept (req.getObjValAs? String "name"))
  let kernel := env.toKernelEnv
  let result (fields : List (String × Json)) :=
    Json.mkObj ([("name", toJson thm.toString)] ++ fields)
  let some (.thmInfo info) := kernel.find? thm
    | return result [("error", toJson "Expected a theorem")]
  let type := stripMData info.type
  let found := axiomClosure kernel thm
  let mut fields := [("axioms", toJson (found.map toString))]
  if req.getObjValAs? Bool "statement" matches .ok true then
    fields := fields ++ [("statement", toJson (← statement env thm info.type))]
  if req.getObjValAs? Bool "refutation" matches .ok true then
    if let some r ← refutation env thm type then fields := fields ++ [("refutes", r)]
  if let .ok spec := req.getObjVal? "type" then
    unless info.levelParams == (names req "levelParams").toList &&
        (← IO.ofExcept (fits spec type)) do
      return result (fields ++ [("error", toJson s!"Theorem statement mismatch: {thm}")])
  if let some error := checkAxioms (names req "axioms") found then
    return result (fields ++ [("error", toJson error)])
  return result fields

/-- Audits one `constants` entry: a definition whose value and type match, and optionally its
    axiom closure. -/
def constant? (env : Environment) (req : Json) : IO Json := do
  let c := name (← IO.ofExcept (req.getObjValAs? String "name"))
  let kernel := env.toKernelEnv
  let result (fields : List (String × Json)) :=
    Json.mkObj ([("name", toJson c.toString)] ++ fields)
  let some (.defnInfo info) := kernel.find? c
    | return result [("error", toJson s!"Expected a definition: {c}")]
  let found := axiomClosure kernel c
  let fields := [("axioms", toJson (found.map toString))]
  let typeOk ← match req.getObjVal? "type" with
    | .ok spec => IO.ofExcept (fits spec (stripMData info.type))
    | .error _ => pure true
  unless typeOk &&
      (← IO.ofExcept (fits (← IO.ofExcept (req.getObjVal? "value")) (stripMData info.value))) do
    return result (fields ++ [("error", toJson s!"Constant value mismatch: {c}")])
  if req.getObjVal? "axioms" matches .ok _ then
    if let some error := checkAxioms (names req "axioms") found then
      return result (fields ++ [("error", toJson error)])
  return result fields

/-- Validates every declaration of the `interfaces` modules. -/
def interfaces (env : Environment) (req : Json) : Json :=
  match CIL.Interface.validateInterfaceDeclarations env (names req "interfaces") with
  | .ok _ => Json.mkObj []
  | .error error => Json.mkObj [("error", toJson error)]

/-- Reports the contract kind and canonical closure of one `closures` entry. -/
def closure? (env : Environment) (req : Json) : IO Json := do
  let c := name (← IO.ofExcept (req.getObjValAs? String "name"))
  return Json.mkObj <| [("name", toJson c.toString)] ++
    match CIL.Interface.contractClosure env c with
    | .ok (kind, canonical) => [("kind", toJson kind), ("canonical", toJson canonical)]
    | .error error => [("error", toJson error)]

/-- The namespace of a prefix such as `A.` or `A`; the empty prefix would match every theorem. -/
def namespacePrefix (p : String) : Except String Name :=
  let n := name (if p.endsWith "." then p.dropEnd 1 |>.toString else p)
  if n.isAnonymous then throw s!"Invalid namespace prefix {repr p}" else pure n

/-- Every `theorem` declared in `modules` whose name, or user name if private, lies under a
    prefix. -/
def namespaces (env : Environment) (modules : Array Name) (req : Json) : IO Json := do
  let given ← IO.ofExcept <|
    (req.getObjValAs? (Array String) "prefixes").bind (·.mapM namespacePrefix)
  -- `A.` and `A` name one namespace; a duplicate would count each theorem twice under one key.
  let prefixes := given.foldl (fun acc p => if acc.contains p then acc else acc.push p) #[]
  let allowed := names req "axioms"
  let kernel := env.toKernelEnv
  if prefixes.isEmpty then return Json.mkObj [("error", toJson "No namespace prefixes to audit")]
  let mut seen : NameSet := {}
  let mut roots := #[]
  let mut perPrefix : Std.HashMap Name Nat := {}
  let mut perModule : Array (String × Json) := #[]
  for m in env.header.moduleNames, data in env.header.moduleData do
    unless modules.contains m do continue
    let mut count := 0
    for c in data.constNames do
      if seen.contains c then continue
      let user := (privateToUserName? c).getD c
      let matching := prefixes.filter (·.isPrefixOf user)
      if matching.isEmpty then continue
      let some (.thmInfo _) := kernel.find? c | continue
      seen := seen.insert c
      roots := roots.push c
      count := count + 1
      -- Nested prefixes each count the theorem, so neither reports zero.
      for p in matching do perPrefix := perPrefix.insert p (perPrefix.getD p 0 + 1)
    perModule := perModule.push (m.toString, toJson count)
  let found := axiomClosureOf kernel roots
  -- Attribution walks each theorem again, so it runs only when the shared closure is rejected.
  let rejected := if (checkAxioms allowed found).isNone then #[] else
    roots.filterMap fun c =>
      let axioms := axiomClosure kernel c
      (checkAxioms allowed axioms).map fun error =>
        Json.mkObj [("name", toJson c.toString), ("axioms", toJson (axioms.map toString)),
          ("error", toJson error)]
  let empty := prefixes.filter (perPrefix.getD · 0 == 0)
  let error := if !empty.isEmpty then
      some s!"No theorems under namespace prefixes: {", ".intercalate (empty.toList.map toString)}"
    else if !rejected.isEmpty then
      some s!"{rejected.size} of {roots.size} theorems use unapproved proof axioms"
    else none
  return Json.mkObj <| [("count", toJson roots.size),
    ("prefixes",
      Json.mkObj (prefixes.toList.map fun p => (p.toString, toJson (perPrefix.getD p 0)))),
    ("modules", Json.mkObj perModule.toList), ("axioms", toJson (found.map toString)),
    ("rejected", Json.arr rejected)] ++ (error.map fun e => [("error", toJson e)]).getD []

end LeanCILAudit

open Lean LeanCILAudit in
/-- Reads REQUEST, imports `modules` without running any extension, and writes RESULT. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [request, output] := args | throw (IO.userError "Usage: leancil-audit REQUEST RESULT")
  let req ← IO.ofExcept (Json.parse (← IO.FS.readFile request))
  let sysroot ← findSysroot
  -- Toolchain modules first: LEAN_PATH may add modules but never replace core ones.
  searchPathRef.set ((← getBuiltinSearchPath sysroot) ++ (← addSearchPathFromEnv {}))
  let modules := names req "modules"
  if modules.isEmpty then throw (IO.userError "No modules to audit")
  let mut paths : List (String × Json) := []
  for m in modules do paths := paths ++ [(m.toString, toJson (← findOLean m).toString)]
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := false)
  let theorems ← ((req.getObjValAs? (Array Json) "theorems").toOption.getD #[]).mapM (theorem? env)
  let constants ←
    ((req.getObjValAs? (Array Json) "constants").toOption.getD #[]).mapM (constant? env)
  let closures ← ((req.getObjValAs? (Array Json) "closures").toOption.getD #[]).mapM (closure? env)
  let audited ← match req.getObjVal? "namespaces" with
    | .ok spec => pure [("namespaces", ← namespaces env modules spec)]
    | .error _ => pure []
  IO.FS.writeFile output (Json.mkObj ([("modules", Json.mkObj paths),
    ("theorems", toJson theorems), ("constants", toJson constants),
    ("interfaces", interfaces env req), ("closures", toJson closures)] ++ audited)).compress
  return 0
