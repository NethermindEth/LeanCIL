import Lean
import CIL.Interface.Closure
import CIL.Replay
import CIL.Interface.Headers

/-!
# Olean audit

`leancil-audit REQUEST RESULT` audits compiled `.olean` files without elaborating any source.
`--headers INPUT` parses source import headers without elaboration or executing source commands.
`--imports INPUT OUTPUT` reads compiled import headers; `--fingerprints INPUT` writes portable
module parts with only persisted linter diagnostics removed. Neither mode loads extensions.
`--replay INPUT` kernel-checks an exact JSON array of target modules against shared imports.
`--replay-separately INPUT` reports isolated toolchain replay results for each target.
An audit request with `replayTargets` checks those modules first and reuses their checked kernel
environment when declaration names are unique and the audit needs no target module metadata.

It imports `modules` with `loadExts := false`, so no imported environment extension, attribute,
elaborator, notation or `initialize` runs; only constant declarations are read. The toolchain's
library precedes `LEAN_PATH`, so a user module cannot shadow `Init`, `Std` or `Lean`.

REQUEST (JSON):
  { "modules":   ["Proof", ...],
    "theorems":  [{ "name": N, "type": E?, "levelParams": [u, ...]?, "axioms": [N, ...],
                    "statement": bool?, "refutation": bool?, "allowedModules": [M, ...]? }],
    "constants": [{ "name": N, "value": E, "type": E?, "axioms": [N, ...]? }],
    "interfaces": [M, ...]?, "closures": [{ "name": N }]?, "replayTargets": [M, ...]?,
    "namespaces": { "prefixes": [P, ...], "axioms": [N, ...] }? }
A theorem must be a `theorem` whose type matches `E` (when given) and whose axiom closure is
in `axioms`. An `allowedModules` scope requires its declaring module and every reachable
replay-target declaration's module to belong to that set;
scoped replay rejects duplicate declarations instead of selecting another proof's body.
A constant must be a definition whose value (and type) match. Every declaration
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

/-- Constants that a declaration's kernel expressions mention; none for an unknown name. -/
def directDependencies (env : Kernel.Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some info => (parts info).foldl (fun found e => found ++ e.getUsedConstants) #[]
  | none => #[]

/-- Reachable axioms and the first declaration outside `visible`, sharing one dependency walk.
Persisted olean axiom summaries are ignored. `dependencies` must return `directDependencies`. -/
def axiomClosureWith [Monad m] (env : Kernel.Environment) (dependencies : Name → m (Array Name))
    (roots : Array Name) (visible : Name → Bool := fun _ => true) :
    m (Array Name × Option Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut pending := roots
  let mut axioms : NameSet := {}
  let mut invisible := none
  while h : pending.size > 0 do
    let c := pending[pending.size - 1]
    pending := pending.pop
    if seen.contains c then continue
    seen := seen.insert c
    if invisible.isNone && !visible c then invisible := some c
    if env.find? c matches some (.axiomInfo _) then axioms := axioms.insert c
    for d in ← dependencies c do
      unless seen.contains d do pending := pending.push d
  return (axioms.toArray.qsort Name.lt, invisible)

/-- `axiomClosureWith`, computing each declaration's dependencies as it is reached. -/
def axiomClosureOf (env : Kernel.Environment) (roots : Array Name)
    (visible : Name → Bool := fun _ => true) : Array Name × Option Name :=
  Id.run (axiomClosureWith env (fun c => pure (directDependencies env c)) roots visible)

/-- `directDependencies`, remembered across the theorem audits of one request, which share most
of their closure through the framework. -/
def cachedDependencies (env : Kernel.Environment) (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (c : Name) : IO (Array Name) := do
  if let some known := (← cache.get)[c]? then return known
  let found := directDependencies env c
  cache.modify (·.insert c found)
  return found

/-- Axioms reachable from `root`, walking kernel declarations only. -/
def axiomClosure (env : Kernel.Environment) (root : Name) : Array Name :=
  (axiomClosureOf env #[root]).1

/-- `e` with every metadata node removed, so comparison sees only kernel structure. -/
partial def stripMData (e : Expr) : Expr := e.replace fun
  | .mdata _ b => some (stripMData b)
  | _ => none

/-- The contract predicates whose negation a refutation theorem may state. -/
def contracts : List Name :=
  [`CIL.Safety.MethodContract.Holds, `CIL.Safety.OutcomeContract.Holds,
    `CIL.Safety.OutcomeContract.HoldsCLR]

/-- The context for pretty-printing and source ranges; no elaboration runs in it.
With no open namespaces or aliases only full names resolve, so `pp.fullNames` prints the same text
without resolving every name suffix against the environment. -/
def coreContext : Core.Context :=
  { fileName := "<leancil-audit>", fileMap := default, maxHeartbeats := 200000 * 1000,
    maxRecDepth := 4096,
    options := ({} : Options).insert `pp.fieldNotation (.ofBool false)
      |>.insert `pp.fullNames (.ofBool true) }

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

/-- Audits one theorem's kind, owner scope, level parameters, type and axiom closure. -/
def theorem? (env : Environment) (req : Json)
    (ownerOf : Name → Option Name) (replayed : NameSet)
    (dependencies : Name → IO (Array Name)) : IO Json := do
  let thm := name (← IO.ofExcept (req.getObjValAs? String "name"))
  let kernel := env.toKernelEnv
  let result (fields : List (String × Json)) :=
    Json.mkObj ([("name", toJson thm.toString)] ++ fields)
  let some (.thmInfo info) := kernel.find? thm
    | return result [("error", toJson "Expected a theorem")]
  let allowed := (names req "allowedModules").foldl (·.insert ·) ({} : NameSet)
  if (req.getObjVal? "allowedModules").isOk then
    unless (ownerOf thm).any allowed.contains do
      return result [("error", toJson s!"Theorem is outside its request's import closure: {thm}")]
  let type := stripMData info.type
  let visible := fun constant => !(req.getObjVal? "allowedModules").isOk ||
    (ownerOf constant).all (fun owner => !replayed.contains owner || allowed.contains owner)
  let (found, invisible) ← axiomClosureWith kernel dependencies #[thm] visible
  if let some constant := invisible then
    return result [("error", toJson
      s!"Theorem dependency is outside its request's import closure: {constant}")]
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
def interfaces (env : Environment) (req : Json) (replayed : Option (List Name))
    (ownerOf : Name → Option Name) : Json :=
  let checked := match replayed with
    | some declarations =>
      CIL.Interface.validateReplayedInterfaceDeclarations env declarations ownerOf
    | none => CIL.Interface.validateInterfaceDeclarations env (names req "interfaces")
  match checked with
  | .ok _ => Json.mkObj []
  | .error error => Json.mkObj [("error", toJson error)]

/-- Reports the contract kind and canonical closure of one `closures` entry. -/
def closure? (env : Environment) (req : Json)
    (ownerOf : Name → Option Name) : IO Json := do
  let c := name (← IO.ofExcept (req.getObjValAs? String "name"))
  return Json.mkObj <| [("name", toJson c.toString)] ++
    match CIL.Interface.contractClosure env c ownerOf with
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
  let found := (axiomClosureOf kernel roots).1
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

/-- Writes one import header before the caller releases its backing region. -/
@[noinline] def writeImportHeader (path : String) (output : IO.FS.Handle) : IO CompactedRegion := do
  let (data, region) ← readModuleData path
  output.putStrLn (toJson (data.imports.map fun item => item.module.toString)).compress
  return region

/-- Writes compiled import headers without loading environment extensions. -/
unsafe def writeImports (input output : String) : IO Unit := do
  let paths : Array String ←
    IO.ofExcept <| (Json.parse (← IO.FS.readFile input)).bind fromJson?
  IO.FS.withFile output .write fun handle => do
    for path in paths do
      let region ← writeImportHeader path handle
      region.free

/-- Copies module parts excluding only persisted linter diagnostics. The caller owns the regions. -/
@[noinline] def fingerprintModule (name : String) (sources destinations : Array String) :
    IO (Array CompactedRegion) := do
  let parts ← readModuleDataParts (sources.map System.FilePath.mk)
  let filtered := parts.map fun (data, _) =>
    { data with entries := data.entries.filter (fun entry => entry.1 != `Lean.Linter.lintLogExt) }
  saveModuleDataParts name.toName (destinations.map System.FilePath.mk |>.zip filtered)
  return parts.map Prod.snd

/-- Writes portable module fingerprints and releases regions after their reconstructed data. -/
unsafe def writeFingerprints (input : String) : IO Unit := do
  let modules : Array (String × Array String × Array String) ←
    IO.ofExcept <| (Json.parse (← IO.FS.readFile input)).bind fromJson?
  for (name, sources, destinations) in modules do
    if sources.size != destinations.size then
      throw (IO.userError "Fingerprint source and destination counts differ")
    let regions ← fingerprintModule name sources destinations
    for region in regions.reverse do region.free

/-- Whether an audit needs target metadata absent from a freshly replayed kernel environment. -/
def needsTargetMetadata (env : Kernel.Environment) (req : Json) : Bool := Id.run do
  if (req.getObjVal? "namespaces").isOk then return true
  for entry in (req.getObjValAs? (Array Json) "theorems").toOption.getD #[] do
    if entry.getObjValAs? Bool "refutation" matches .ok true then
      let some thm := (entry.getObjValAs? String "name").toOption | return true
      if let some (.thmInfo info) := env.find? (name thm) then
        if let .app (.const `Not _) claim := stripMData info.type then
          if let .const contract _ := claim.getAppFn then
            if contracts.contains contract then return true
  return false

/-- Audits a supplied immutable environment and records the exact resolved module paths. -/
unsafe def writeAudit (req : Json) (output : String) (env : Environment)
    (extra : List (String × Json) := [])
    (ownerOf : Name → Option Name := fun name =>
      (env.getModuleIdxFor? name).bind (env.allImportedModuleNames[·.toNat]?))
    (closureOwnerOf : Name → Option Name := fun name =>
      some (CIL.Interface.definingModule env name))
    (replayedInterfaces : Option (List Name) := none) : IO Unit := do
  let modules := names req "modules"
  let replayed := (names req "replayTargets").foldl (·.insert ·) ({} : NameSet)
  let mut paths : List (String × Json) := []
  for m in modules do paths := paths ++ [(m.toString, toJson (← findOLean m).toString)]
  let cache ← IO.mkRef {}
  let theorems ← ((req.getObjValAs? (Array Json) "theorems").toOption.getD #[]).mapM
    (fun entry => theorem? env entry ownerOf replayed (cachedDependencies env.toKernelEnv cache))
  let constants ←
    ((req.getObjValAs? (Array Json) "constants").toOption.getD #[]).mapM (constant? env)
  let closures ← ((req.getObjValAs? (Array Json) "closures").toOption.getD #[]).mapM
    (fun entry => closure? env entry closureOwnerOf)
  let audited ← match req.getObjVal? "namespaces" with
    | .ok spec => pure [("namespaces", ← namespaces env modules spec)]
    | .error _ => pure []
  IO.FS.writeFile output (Json.mkObj ([("modules", Json.mkObj paths),
    ("theorems", toJson theorems), ("constants", toJson constants),
    ("interfaces", interfaces env req replayedInterfaces closureOwnerOf),
    ("closures", toJson closures)] ++ audited ++ extra)).compress

end LeanCILAudit

open Lean LeanCILAudit in
/-- Reads REQUEST, imports `modules` without running any extension, and writes RESULT. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--replay", input] =>
    let targets ← IO.ofExcept <| (Json.parse (← IO.FS.readFile input)).bind fromJson?
    CIL.Replay.replayModulesJointly targets
    return 0
  | ["--replay-separately", input] =>
    let targets ← IO.ofExcept <| (Json.parse (← IO.FS.readFile input)).bind fromJson?
    return ← CIL.Replay.replayModulesSeparately targets
  | ["--headers", input] => CIL.Interface.writeSourceHeaders input; return 0
  | ["--imports", input, output] => writeImports input output; return 0
  | ["--fingerprints", input] => writeFingerprints input; return 0
  | _ => pure ()
  let [request, output] := args | throw (IO.userError "Usage: leancil-audit REQUEST RESULT")
  let req ← IO.ofExcept (Json.parse (← IO.FS.readFile request))
  let sysroot ← findSysroot
  -- Toolchain modules first: LEAN_PATH may add modules but never replace core ones.
  searchPathRef.set ((← getBuiltinSearchPath sysroot) ++ (← addSearchPathFromEnv {}))
  let modules := names req "modules"
  if modules.isEmpty then throw (IO.userError "No modules to audit")
  if let .ok targets := req.getObjValAs? (List String) "replayTargets" then
    if targets.isEmpty then throw (IO.userError "No modules to replay")
    CIL.Replay.withReplayedModules targets fun kernel unique ownerOf owners => do
      let hasOwnerScopes := ((req.getObjValAs? (Array Json) "theorems").toOption.getD #[]).any
        (fun entry => (entry.getObjVal? "allowedModules").isOk)
      if hasOwnerScopes && !unique then
        throw (IO.userError "Scoped theorem audit requires unique replay declarations")
      let fused := unique && modules.all (fun m => targets.contains m.toString) &&
        (names req "interfaces").all (fun m => targets.contains m.toString) &&
        !needsTargetMetadata kernel req
      let env ← if fused then pure (Environment.ofKernelEnv kernel)
        else importModules (modules.map ({ module := · })) {} (loadExts := false)
      let closureOwnerOf := if fused then ownerOf
        else fun name => some (CIL.Interface.definingModule env name)
      let interfaceModules := names req "interfaces"
      let replayedInterfaces := if fused then some <|
        owners.fold (init := []) fun declarations name module =>
          if interfaceModules.contains module then name :: declarations else declarations
        else none
      try
        writeAudit req output env [("replayed", toJson targets), ("fused", toJson fused)]
          ownerOf closureOwnerOf replayedInterfaces
      finally unless fused do env.freeRegions
    return 0
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := false)
  writeAudit req output env
  return 0
