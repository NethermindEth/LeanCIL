import CIL.MethodBinding
import CIL.Embedding.Basic
import Lean.Meta.Tactic.AuxLemma

/-!
`cil_embed` proves `MethodEmbeds program index expected`: the extracted method at
`index` contains every live instruction of `expected`, with code targets renamed
consistently. It aligns the two bodies outside the kernel, explains the first
violated condition if there is one, and otherwise hands the pc map to the kernel,
which checks every `Embeds` field by evaluation. The alignment is untrusted: a
wrong map only makes the kernel reject the proof.
-/

namespace CIL.MethodBinding

open Lean Meta Elab Tactic CIL.Embedding

/-- Code targets of an instruction, in the order `Op.relabel` maps them. -/
def opTargets : Op → List Nat
  | .nativeBinary op => opTargets op
  | .bgt t | .ble t | .bleu t | .branch t | .brzero t | .brnonzero t | .bltu t | .bgeu t
  | .bgtu t | .bge t | .blt t | .beq t | .bne t => [t]
  | .switch ts => ts
  | _ => []

/-- An instruction with its code targets erased. -/
def shape (op : Op) : Op := op.relabel (fun _ => 0)

private def opAt (code : Array Op) (pc : Nat) : Option Op := code[pc]?

/-- Maps each live expected pc to an actual pc: the next pc after a fallthrough, else a
    pc an already aligned branch targets, else the next actual instruction of the same shape. -/
def alignLive (expected actual : Array Op) : Array Nat := Id.run do
  let mut map : Array (Option Nat) := Array.replicate expected.size none
  let mut hints : Std.HashMap Nat Nat := {}
  let mut cursor := 0
  for p in [0:expected.size] do
    let op := expected.getD p .nop
    unless op.live do continue
    let previous := if p = 0 then none else opAt expected (p - 1)
    let forced := match previous with
      | some prior => if prior.live && prior.continues then (map[p - 1]!).map (· + 1) else none
      | none => none
    let hinted := (hints.get? p).filter fun k => (opAt actual k).any fun found => shape found == shape op
    let searched := Id.run do
      let mut k := cursor
      while k < actual.size do
        if shape (actual.getD k .nop) == shape op then return some k
        k := k + 1
      return none
    let chosen := if p = 0 then some 0 else forced <|> hinted <|> searched
    map := map.set! p chosen
    if let some k := chosen then
      cursor := k + 1
      if let some found := opAt actual k then
        for (t, t') in (opTargets op).zip (opTargets found) do
          unless hints.contains t do hints := hints.insert t t'
  -- Dead expected pcs only matter as targets or as the fallthrough of a live pc.
  let mut full : Array Nat := #[]
  for p in [0:expected.size] do
    let value := match map[p]! with
      | some k => k
      | none =>
        let previous := if p = 0 then none else opAt expected (p - 1)
        let follows := previous.any fun prior => prior.live && prior.continues
        if follows then full[p - 1]! + 1
        else (hints.get? p).getD (if p = 0 then 0 else full[p - 1]! + 1)
    full := full.push value
  return full

private def showOp (op : Option Op) : String := match op with
  | some op => reprStr op
  | none => "(past the end)"

/-- The first violated `Embeds` condition, explained by expected and actual pc. -/
def embedFailure (expected actual : Method) (map : List Nat) : Option String := Id.run do
  let fields := [ valueField "profile" expected.profile actual.profile,
    valueField "returnsValue" expected.returnsValue actual.returnsValue,
    listField "locals" expected.locals actual.locals,
    listField "localKinds" expected.localKinds actual.localKinds,
    listField "vectorLocals" expected.vectorLocals actual.vectorLocals,
    listField "vectorArgs" expected.vectorArgs actual.vectorArgs,
    listField "parameterHomes" expected.parameterHomes actual.parameterHomes,
    listField "static descriptors" (expected.staticSites.map Prod.snd) (actual.staticSites.map Prod.snd) ].filterMap id
  if let some field := fields.head? then
    return some s!"non-code field differs (left: expected, right: actual)\n{field}"
  let limit := actual.code.length
  let r := rename map limit
  let actualCode := actual.code.toArray
  if r 0 != 0 then return some s!"expected pc 0 must map to actual pc 0, not {r 0}"
  let imageOf : Std.HashMap Nat Nat := (sites limit 0 expected.code map).foldl
    (fun table site => table.insert site.image site.pc) {}
  let describe (k : Nat) : String := match imageOf.get? k with
    | some p => s!"actual pc {k} is expected pc {p}"
    | none => s!"actual pc {k} ({showOp (opAt actualCode k)}) is not the image of any live expected pc"
  for site in sites limit 0 expected.code map do
    let p := site.pc
    let op := site.op
    let q := site.image
    let found := opAt actualCode q
    let wanted := op.relabel r
    unless found == some wanted do
      let renamed := if wanted == op then "" else s!"\n  renamed:  {reprStr wanted}"
      let header := s!"expected pc {p} maps to actual pc {q}\n  expected: {reprStr op}{renamed}\n  actual:   {showOp found}"
      match found with
      | none => return some s!"{header}\n  no actual instruction of this shape follows the previous aligned instruction"
      | some present =>
        if shape present == shape op then
          let mismatch := ((opTargets op).zip (opTargets present)).find? fun (t, t') => r t != t'
          match mismatch with
          | some (t, t') =>
            return some s!"{header}\n  code target differs: expected target {t} maps to actual pc {r t}, but the actual instruction targets {t'}; {describe t'}"
          | none => return some s!"{header}\n  the code targets differ"
        else
          let entered := match p, expected.code[p - 1]? with
            | prior + 1, some previous => if previous.live && previous.continues then
                s!"\n  expected pc {prior} falls through to it, so it must be actual pc {r prior + 1}" else ""
            | _, _ => ""
          return some s!"{header}\n  the instructions differ{entered}"
    if staticAt actual q != staticAt expected p then
      return some s!"expected pc {p} (actual pc {q}) resolves a different static descriptor\n  expected: {reprStr (staticAt expected p)}\n  actual:   {reprStr (staticAt actual q)}"
    if op.continues && r (p + 1) != q + 1 then
      return some s!"fallthrough differs: expected pc {p} ({reprStr op}) continues at expected pc {p + 1}, which maps to actual pc {r (p + 1)}, but actual pc {q} continues at actual pc {q + 1}\n  {describe (q + 1)}"
  return none

private def methodType : Expr := mkConst ``CIL.Method

private unsafe def evaluateUnsafe (T : Type) (type value : Expr) : MetaM T := evalExpr T type value

@[implemented_by evaluateUnsafe]
private opaque evaluate (T : Type) (type value : Expr) : MetaM T

/-- Proves `MethodEmbeds program index expected` for closed terms; on failure names the
    first violated condition. The pc map is checked by the kernel, not trusted. -/
syntax (name := cilEmbed) "cil_embed" : tactic

@[tactic cilEmbed] def evalCilEmbed : Tactic := fun _ => do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let fail (message : MessageData) : TacticM Unit :=
    throwError m!"cil_embed: the expected body does not embed into the extracted method\n{message}"
  unless type.isAppOfArity ``CIL.MethodEmbeds 3 do
    throwError "cil_embed: the goal must be `MethodEmbeds program index expected`, not {type}"
  if type.hasFVar || type.hasMVar then
    throwError "cil_embed: program, index and expected body must be closed terms"
  let program := type.appFn!.appFn!.appArg!
  let index := type.appFn!.appArg!
  let expected := type.appArg!
  let indexValue ← evaluate Nat (mkConst ``Nat) index
  let programValue ← evaluate (List Method) (mkApp (mkConst ``List [Level.zero]) methodType) program
  let expectedValue ← evaluate Method methodType expected
  let some actualValue := programValue[indexValue]? |
    fail m!"method index {indexValue}: the program has {programValue.length} methods"
  let map := (alignLive expectedValue.code.toArray actualValue.code.toArray).toList
  if let some reason := embedFailure expectedValue actualValue map then
    fail m!"method index {indexValue}\n{reason}"
  let lookup ← mkAppM ``GetElem?.getElem? #[program, index]
  -- The kernel reduces this to the extracted method; `expected` is never selected.
  let actual ← mkAppM ``Option.getD #[lookup, expected]
  let mapExpr := toExpr map
  -- Each field is closed by `Eq.refl` of its left side; only the kernel compares the sides.
  let mut fieldsType ← instantiateForall (← inferType (mkConst ``CIL.Embeds.mk)) #[expected, actual, mapExpr]
  let mut fields : Array Expr := #[]
  while fieldsType.isForall do
    let some (_, lhs, _) := fieldsType.bindingDomain!.eq? |
      throwError "cil_embed: unexpected `Embeds` field {fieldsType.bindingDomain!}"
    let proof ← mkEqRefl lhs
    fields := fields.push proof
    fieldsType := fieldsType.bindingBody!.instantiate1 proof
  let embeds := mkAppN (mkConst ``CIL.Embeds.mk) (#[expected, actual, mapExpr] ++ fields)
  let found ← mkEqRefl lookup
  let some unfolded ← unfoldDefinition? type | throwError "cil_embed: could not unfold {type}"
  let .app (.app (.const ``Exists _) _) outer := unfolded |
    throwError "cil_embed: unexpected shape {unfolded}"
  let inner := outer.beta #[actual]
  let .app (.app (.const ``Exists _) _) innerMotive := inner |
    throwError "cil_embed: unexpected shape {inner}"
  let conjunction := innerMotive.beta #[mapExpr]
  let some (left, right) := conjunction.and? | throwError "cil_embed: unexpected shape {conjunction}"
  let both := mkApp4 (mkConst ``And.intro) left right found embeds
  let witness := mkApp4 (mkConst ``Exists.intro [1]) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat))
    innerMotive mapExpr both
  let value := mkApp4 (mkConst ``Exists.intro [1]) methodType outer actual witness
  let lemma ← try
      withOptions (Elab.async.set · false) do mkAuxLemma [] type value
    catch error =>
      throwError m!"cil_embed: the kernel rejected the computed embedding\n{error.toMessageData}"
  goal.assign (mkConst lemma)
  replaceMainGoal []

end CIL.MethodBinding
