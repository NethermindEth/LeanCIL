import Lean
import CIL.Extraction.DecodedMethod
import CIL.SymbolicExecution

/-!
# Methods defined by evaluating the decoder

`cil_decoded_method name := decoder` evaluates a closed `Option CIL.Method`, such as
`Method.ofRaw? profile environment original arguments`, defines `name` as the method it gives
and adds `name_decoded : decoder = some name`, which the kernel checks by evaluating the
decoder. The value is found by kernel reduction and written as constructors over numerals, so
the definition and the `@[cil_code]` field facts `name_locals`, `name_declared`, ... read as
literals to `cil_instruction_equations`, `cil_resolution_facts` and stepping, and no text an
extractor writes supplies any part of the method. A constant passed to the decoder, such as an
extraction's `profile` and `environment`, stays that constant where it lands in a field. The
evaluation is not trusted: the kernel checks `name_decoded` and every fact.
-/

namespace CIL.Extraction.DecodedDefinition

open Lean Meta Elab Command

/-- The weak head normal form of a closed term, as the kernel reduces it. -/
def kernelWhnf (term : Expr) : MetaM Expr := do
  ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) term)

/-- The natural number a closed `Nat` term reduces to. -/
partial def natValue (term : Expr) : MetaM Nat := do
  let value ← kernelWhnf term
  if let .lit (.natVal number) := value then return number
  if value.isConstOf ``Nat.zero then return 0
  if value.isAppOfArity ``Nat.succ 1 then return (← natValue value.appArg!) + 1
  throwError "cil_decoded_method: {term} does not reduce to a natural number"

/-- The integer a closed `Int` term reduces to. -/
def intValue (term : Expr) : MetaM Int := do
  let value ← kernelWhnf term
  match value.getAppFnArgs with
  | (``Int.ofNat, #[number]) => return Int.ofNat (← natValue number)
  | (``Int.negSucc, #[number]) => return Int.negSucc (← natValue number)
  | _ => throwError "cil_decoded_method: {term} does not reduce to an integer"

/-- The numeral `value` at `type`, with the instance elaborating the numeral there finds. -/
def numeral (type : Expr) (value : Int) : MetaM Expr := do
  if 0 ≤ value then mkNumeral type value.toNat
  else mkAppM ``Neg.neg #[← mkNumeral type (-value).toNat]

/-- The literal form of the closed term `term` of type `type`: a numeral for a natural
    number, integer, bit vector or `Fin`, a string literal or named string, and otherwise the
    constructor it reduces to applied to the literal forms of its fields. Parameters and proofs
    stay as they are, and so does every term `keep` holds. Each node is reduced once, from the
    term its parent reduced to, so the walk is linear in the size of the value. -/
partial def literal (keep : Expr → Bool) (type term : Expr) : MetaM Expr := do
  if keep term then return term
  let shape ← whnfD type
  match shape.getAppFnArgs with
  | (``Nat, #[]) => numeral type (← natValue term)
  | (``Int, #[]) => numeral type (← intValue term)
  | (``BitVec, #[width]) =>
    numeral type (← natValue (mkApp2 (mkConst ``BitVec.toNat) width term))
  | (``Fin, #[bound]) => numeral type (← natValue (mkApp2 (mkConst ``Fin.val) bound term))
  | (``String, #[]) =>
    -- A named string, such as `runtimeScope`, stays named: fact commands match it by name.
    if term.isConst || term.isStringLit then return term
    let .lit (.strVal text) ← kernelWhnf term
      | throwError "cil_decoded_method: {term} does not reduce to a string literal"
    return mkStrLit text
  | _ =>
    let value ← kernelWhnf term
    let .const head levels := value.getAppFn
      | throwError "cil_decoded_method: {term} does not reduce to a constructor"
    let some (.ctorInfo constructor) := (← getEnv).find? head
      | throwError "cil_decoded_method: {term} does not reduce to a constructor"
    let arguments := value.getAppArgs
    unless arguments.size == constructor.numParams + constructor.numFields do
      throwError "cil_decoded_method: {value} is not a full constructor application"
    let mut remaining := constructor.type.instantiateLevelParams constructor.levelParams levels
    let mut written := #[]
    for inRange : index in [0:arguments.size] do
      let .forallE _ domain body _ ← whnfD remaining
        | throwError "cil_decoded_method: {head} takes fewer arguments than given"
      let argument := arguments[index]
      let field ← if index < constructor.numParams || (← isProp domain) then pure argument
        else literal keep domain argument
      written := written.push field
      remaining := body.instantiate1 field
    return mkAppN value.getAppFn written

/-- The fields an extraction states as `@[cil_code]` facts; stepping, `cil_resolution_facts`
    and the contract tactics read them by name, as `{method}_{field}`. -/
def factFields : List Name :=
  [`profile, `locals, `localKinds, `returnsValue, `staticSites, `declared, `environment, `links,
    `opaqueVectorLocals, `parameterHomes]

/-- Adds the kernel-checked theorem `name : statement` proved by `Eq.refl`, documented by
    `doc`; the kernel accepts it only when both sides of `statement` reduce to one term. -/
def proveByReduction (name : Name) (doc : String) (statement : Expr) : MetaM Unit := do
  let some (type, left, _) := statement.eq?
    | throwError "cil_decoded_method: {statement} is not an equation"
  -- A window per declaration, so earlier kernel work does not exhaust a later one's.
  withCurrHeartbeats do
    addDecl <| .thmDecl {
      name, levelParams := [], type := statement,
      value := mkApp2 (mkConst ``Eq.refl [← getLevel type]) type left }
    addDocStringCore name doc

/-- `cil_decoded_method name := decoder` defines `name` as the method the closed
    `Option CIL.Method` `decoder` evaluates to, proves `name_decoded : decoder = some name` and
    the `@[cil_code]` facts `name_{field}` for each of `factFields`. Fails when the decoder
    gives `none` or does not reduce. -/
syntax (name := decodedMethod) "cil_decoded_method " ident " := " term : command

elab_rules : command
  | `(cil_decoded_method $nameSyntax:ident := $decoderSyntax) => liftTermElabM do
    let methodType := mkConst ``CIL.Method
    let optionType := mkApp (mkConst ``Option [.zero]) methodType
    let decoder ← Term.elabTermEnsuringType decoderSyntax optionType
    Term.synthesizeSyntheticMVarsNoPostponing
    let decoder ← instantiateMVars decoder
    if decoder.hasMVar || decoder.hasFVar then
      throwError "cil_decoded_method: the decoder must be a closed term{indentExpr decoder}"
    let some simpSet ← getSimpExtension? `cil_code
      | throwError "cil_decoded_method: the cil_code simp set is not registered"
    let name := (← getCurrNamespace) ++ nameSyntax.getId
    let passed := decoder.getAppArgs.filter (·.isConst)
    let decoded ← kernelWhnf decoder
    unless decoded.isAppOfArity ``Option.some 2 do
      throwError "cil_decoded_method: the decoder gives no method{indentExpr decoder}"
    let value ← literal passed.contains methodType decoded.appArg!
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := methodType, value,
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    addDeclarationRangesFromSyntax name (← getRef) nameSyntax
    addDocStringCore name s!"The method `{decoderSyntax}` decodes to."
    let method := mkConst name
    proveByReduction (name.appendAfter "_decoded") s!"`{name}` is the decoded method."
      (← mkEq decoder (mkApp2 (mkConst ``Option.some [.zero]) methodType method))
    let fields := getStructureFields (← getEnv) ``CIL.Method
    for field in factFields do
      let some position := fields.idxOf? field
        | throwError "cil_decoded_method: CIL.Method has no field {field}"
      let fact := name.appendAfter s!"_{field}"
      proveByReduction fact s!"The {field} of `{name}`."
        (← mkEq (mkApp (mkConst (``CIL.Method ++ field)) method) value.getAppArgs[position]!)
      addSimpTheorem simpSet fact (post := true) (inv := false) .global (eval_prio default)

end CIL.Extraction.DecodedDefinition
