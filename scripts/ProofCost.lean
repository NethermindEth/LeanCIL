import Lean

/-!
Measuring frontend for `scripts/ProofCost.cs`.

`lean --run scripts/ProofCost.lean <module> <source> <report.json> [<output.olean>]` elaborates
one Lean source file command by command on a single thread and writes what each command cost:
heartbeats, the kernel's share of them for the theorems it declared, the allocated size of their
proof terms, source lines and elapsed time. With an olean path it also writes the compiled
module, so a later module can import it and its size on disk can be measured.

The file imports only `Lean`, so it measures any revision of the library, including one that
predates it. It checks nothing: a proof is accepted by the verification suites, not here.
-/

open Lean Elab

namespace ProofCost

/-- What one top-level command cost to elaborate and check. -/
structure CommandCost where
  /-- The declared name, or the command's keyword and first identifier. -/
  label : String
  /-- `theorem`, `definition`, `example` or `command`. -/
  kind : String
  /-- One-based line of the command's first token. -/
  line : Nat
  /-- Source lines the command spans. -/
  sourceLines : Nat
  /-- Heartbeats spent elaborating and kernel-checking the command. -/
  heartbeats : Nat
  /-- Heartbeats the kernel alone spends rechecking the theorems the command declared. -/
  kernelHeartbeats : Nat
  /-- Allocated expression objects in the proofs of the theorems the command declared. -/
  proofObjects : Nat
  /-- Constants the command added, auxiliary ones included. -/
  constants : Nat
  /-- Elapsed milliseconds elaborating the command; not reproducible. -/
  elapsedMs : Nat
  /-- Elapsed milliseconds of the kernel recheck; not reproducible. -/
  kernelMs : Nat

/-- The report field names are the measure names `scripts/ProofCost.cs` reads. -/
def CommandCost.toJson (cost : CommandCost) : Json :=
  Json.mkObj [
    ("label", cost.label), ("kind", cost.kind), ("line", cost.line),
    ("sourceLines", cost.sourceLines), ("heartbeats", cost.heartbeats),
    ("kernelHeartbeats", cost.kernelHeartbeats), ("proofObjects", cost.proofObjects),
    ("constants", cost.constants), ("elapsedMs", cost.elapsedMs), ("kernelMs", cost.kernelMs)]

/-- The first node of `kind` in `syntaxTree`, searching outermost first. -/
partial def findKind? (kind : SyntaxNodeKind) (syntaxTree : Syntax) : Option Syntax :=
  if syntaxTree.isOfKind kind then some syntaxTree
  else syntaxTree.getArgs.findSome? (findKind? kind)

/-- The first atom of `syntaxTree`, which for a command is its keyword. -/
partial def firstAtom? : Syntax → Option String
  | .atom _ value => some value
  | .node _ _ args => args.findSome? firstAtom?
  | _ => none

/-- The first identifier of `syntaxTree`. -/
partial def firstIdent? : Syntax → Option Name
  | .ident _ _ value _ => some value
  | .node _ _ args => args.findSome? firstIdent?
  | _ => none

/-- A name as the user wrote it: private prefixes and macro scopes removed. -/
def userName (name : Name) : Name :=
  (privateToUserName name).eraseMacroScopes

/--
The name a declaration command declares: the added constant its `declId` is a suffix of, or
the `declId` under `currentNamespace` when the command added no such constant.
-/
def declaredName (currentNamespace : Name) (declId : Syntax) (added : Array Name) : Name :=
  let written := declId[0].getId.eraseMacroScopes
  let candidates := added.filterMap fun name =>
    let shown := userName name
    if written.isSuffixOf shown && !name.isInternalDetail then some shown else none
  let shortest := candidates.foldl (init := none) fun (best : Option Name) candidate =>
    match best with
    | some chosen =>
      if candidate.toString.length < chosen.toString.length then some candidate else some chosen
    | none => some candidate
  shortest.getD (currentNamespace ++ written)

/-- Digits of the source hash kept in the label of a command that declares no name. -/
def sourceHashDigits : Nat := 8

/--
A label for a command that names nothing, from its `keyword` and its source text. An unnamed
command keeps its label when commands around it are added or removed, and loses it when edited.
-/
def unnamedLabel (keyword source : String) : String :=
  let digits := (Nat.toDigits 16 (hash source).toNat).reverse.take sourceHashDigits
  s!"{keyword}@{String.ofList digits}"

/--
The row label and kind of `command`, given its `source` text and the constants it `added`.
-/
def describe (currentNamespace : Name) (command : Syntax) (source : String) (added : Array Name)
    (addedTheorem : Bool) : String × String :=
  match findKind? ``Parser.Command.declId command with
  | some declId =>
    let isTheorem := addedTheorem || (findKind? ``Parser.Command.theorem command).isSome
    ((declaredName currentNamespace declId added).toString,
      if isTheorem then "theorem" else "definition")
  | none =>
    let keyword := (firstAtom? command).getD command.getKind.toString
    if (findKind? ``Parser.Command.example command).isSome then
      (unnamedLabel "example" source, "example")
    else
      let label := match firstIdent? command with
        | some name => s!"{keyword} {name.eraseMacroScopes}"
        | none => unnamedLabel keyword source
      (label, "command")

/-- The constants of the module being elaborated that `known` does not hold yet. -/
def addedConstants (env : Environment) (known : NameSet) : Array (Name × ConstantInfo) :=
  env.constants.map₂.foldl (init := #[]) fun added name info =>
    if known.contains name then added else added.push (name, info)

/-- The kernel's heartbeat limit value that disables the limit. -/
def noHeartbeatLimit : USize := 0

/-- Recursion depth allowed to the recheck; deeper than any proof the suites accept. -/
def recheckRecursionDepth : USize := 1000000

/--
Kernel heartbeats and milliseconds to recheck `theorems` against `env`, each under a fresh name.
A rejected recheck is an error: the elaborator's own check of the same term had passed.
-/
def recheck (env : Environment) (theorems : Array TheoremVal) : IO (Nat × Nat) := do
  let startBeats ← IO.getNumHeartbeats
  let startMs ← IO.monoMsNow
  for declaration in theorems do
    let copy : Declaration := .thmDecl
      { declaration with name := declaration.name ++ `proofCostRecheck }
    match env.toKernelEnv.addDeclCore noHeartbeatLimit recheckRecursionDepth copy none with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError s!"kernel rejected the recheck of {declaration.name}"
  return ((← IO.getNumHeartbeats) - startBeats, (← IO.monoMsNow) - startMs)

/--
Options that keep elaboration and kernel checking on the measuring thread, the only one whose
heartbeats are counted.
-/
def singleThreaded : Options :=
  ({} : Options).setBool `Elab.async false

/-- Elaborates `sourcePath` as `moduleName`; returns each command's cost and the result. -/
def measure (moduleName : Name) (sourcePath : String) :
    IO (Array CommandCost × Environment × Bool) := do
  let text ← IO.FS.readFile sourcePath
  let inputContext := Parser.mkInputContext text sourcePath
  let (header, parserState, headerMessages) ← Parser.parseHeader inputContext
  let (headerEnv, messages) ← processHeader header singleThreaded headerMessages inputContext
  let env := headerEnv.setMainModule moduleName
  let context : Frontend.Context := { inputCtx := inputContext }
  let commandState := Command.mkState env messages singleThreaded
  let mut state : Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
  let mut known : NameSet := {}
  let mut costs : Array CommandCost := #[]
  let mut finished := false
  while !finished do
    let start := state.cmdPos
    let currentNamespace := state.commandState.scopes.head!.currNamespace
    let startBeats ← IO.getNumHeartbeats
    let startMs ← IO.monoMsNow
    let (isLast, next) ← (Frontend.processCommand.run context).run state
    let heartbeats := (← IO.getNumHeartbeats) - startBeats
    let elapsedMs := (← IO.monoMsNow) - startMs
    state := next
    finished := isLast
    let some command := state.commands.back? | continue
    if command.isOfKind ``Parser.Command.eoi then continue
    let added := addedConstants state.commandState.env known
    known := added.foldl (fun names (name, _) => names.insert name) known
    let theorems := added.filterMap fun
      | (_, .thmInfo declaration) => some declaration
      | _ => none
    let (kernelHeartbeats, kernelMs) ← recheck state.commandState.env theorems
    let mut proofObjects := 0
    for declaration in theorems do
      proofObjects := proofObjects + (← declaration.value.numObjs)
    let position := command.getPos?.getD start
    let tail := command.getTailPos?.getD position
    let (label, kind) := describe currentNamespace command
      (String.Pos.Raw.extract text position tail) (added.map (·.1)) !theorems.isEmpty
    let firstLine := (inputContext.fileMap.toPosition position).line
    let lastLine := (inputContext.fileMap.toPosition tail).line
    costs := costs.push {
      label, kind, heartbeats, kernelHeartbeats, proofObjects, elapsedMs, kernelMs
      line := firstLine
      sourceLines := lastLine + 1 - firstLine
      constants := added.size }
  let log := state.commandState.messages
  for message in log.toList do
    if message.severity == .error then IO.eprintln (← message.toString)
  return (costs, state.commandState.env, log.hasErrors)

/-- Measures one module and writes its report; a module with an error has no report. -/
unsafe def run (arguments : List String) : IO UInt32 := do
  let (moduleName, sourcePath, reportPath, oleanPath?) ← match arguments with
    | [moduleName, sourcePath, reportPath] => pure (moduleName, sourcePath, reportPath, none)
    | [moduleName, sourcePath, reportPath, oleanPath] =>
      pure (moduleName, sourcePath, reportPath, some oleanPath)
    | _ =>
      IO.eprintln "Usage: ProofCost.lean <module> <source> <report.json> [<output.olean>]"
      return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let (costs, env, failed) ← measure moduleName.toName sourcePath
  if failed then
    IO.eprintln s!"{sourcePath}: elaboration reported an error; nothing was measured"
    return 1
  if let some oleanPath := oleanPath? then writeModule env oleanPath
  IO.FS.writeFile reportPath <| Json.compress <| Json.mkObj [
    ("module", moduleName), ("commands", Json.arr (costs.map (·.toJson)))]
  return 0

end ProofCost

/-- Entry point of `lean --run`. -/
unsafe def main (arguments : List String) : IO UInt32 :=
  ProofCost.run arguments
