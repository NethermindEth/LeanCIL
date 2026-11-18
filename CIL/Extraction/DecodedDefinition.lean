import Lean
import CIL.Extraction.DecodedMethod
import CIL.SymbolicExecution

/-!
# Methods defined by evaluating the decoder

`cil_decoded_method name := decoder` evaluates a closed `Option CIL.Method`, such as
`Method.ofClosed? profile environment links closed storage`, defines `name` as the method it gives
and adds `name_decoder_eq : decoder = some name`, which the kernel checks by evaluating the
decoder. Compiled code computes the value, which is written as constructors over numerals, so
the definition and the `@[cil_code]` field facts `name_locals`, `name_declared`, ... read as
literals to `cil_instruction_equations`, `cil_resolution_facts` and stepping, and no text an
extractor writes supplies any part of the method. A field whose type is that of a constant
passed to the decoder, such as an extraction's `profile`, `environment` and link table, is written
as that constant, and `cil_decoded_method name [field, ...] := decoder` writes each field operand
equal to a listed `FieldRef` constant as that constant, as an extraction's literal names it, so
the facts `cil_field_shape` states about the constant apply. A decoded constrained call keeps
the identity expressions from its raw layouts. The kernel checks `name_decoder_eq` and every fact.
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
    stay as they are, and a term `named` maps to a constant is written as that constant. Each
    node is reduced once, from the term its parent reduced to, so the walk is linear in the size
    of the value. -/
partial def literal (named : Expr → Option Expr) (type term : Expr) : MetaM Expr := do
  if let some constant := named term then return constant
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
        else literal named domain argument
      written := written.push field
      remaining := body.instantiate1 field
    return mkAppN value.getAppFn written

/-- Writes the runtime scope as its named constant, as an extraction writes it, so fact commands
    that match the scope by name read a decoded method as they read an extracted one. -/
local instance : ToExpr String where
  toExpr text :=
    if text == Extraction.runtimeScope then mkConst ``Extraction.runtimeScope else mkStrLit text
  toTypeExpr := mkConst ``String

deriving instance ToExpr for ComparisonGuard
deriving instance ToExpr for ZeroGuard
deriving instance ToExpr for EnumStorage
deriving instance ToExpr for ArrayElement
deriving instance ToExpr for ArraySpanRange
deriving instance ToExpr for SnapshotShape
deriving instance ToExpr for TransferKind
deriving instance ToExpr for ExceptionType
deriving instance ToExpr for NumericKind
deriving instance ToExpr for Extraction.TypeExpr
deriving instance ToExpr for MetadataName
deriving instance ToExpr for Extraction.FieldRef
deriving instance ToExpr for Extraction.MethodRef
deriving instance ToExpr for CallPrefixes
deriving instance ToExpr for ViewObservation
deriving instance ToExpr for MemoryOp
deriving instance ToExpr for Address
deriving instance ToExpr for ManagedSignature
deriving instance ToExpr for ArmAESIntrinsic
deriving instance ToExpr for AESIntrinsic
deriving instance ToExpr for X86BaseIntrinsic
deriving instance ToExpr for AVX512DQIntrinsic
deriving instance ToExpr for ArmBaseIntrinsic
deriving instance ToExpr for BMI2Intrinsic
deriving instance ToExpr for BMI1Intrinsic
deriving instance ToExpr for AVXIntrinsic
deriving instance ToExpr for AVX512Intrinsic
deriving instance ToExpr for AVX2Intrinsic
deriving instance ToExpr for Value
deriving instance ToExpr for SSEIntrinsic
deriving instance ToExpr for ManagedIdentity
deriving instance ToExpr for AdvSimdIntrinsic
deriving instance ToExpr for StaticInitializer
deriving instance ToExpr for VectorIntrinsic
deriving instance ToExpr for ScalarResultWidth
deriving instance ToExpr for IntegerMath
deriving instance ToExpr for ScalarIntrinsic
deriving instance ToExpr for ManagedTarget
deriving instance ToExpr for Receiver
deriving instance ToExpr for NarrowKind
deriving instance ToExpr for Intrinsic
deriving instance ToExpr for Feature
deriving instance ToExpr for ManagedOp
deriving instance ToExpr for SpanConstructor
deriving instance ToExpr for ConvTarget
deriving instance ToExpr for TokenOperand
deriving instance ToExpr for Instruction
deriving instance ToExpr for LocalKind
deriving instance ToExpr for StaticDescriptor
deriving instance ToExpr for DeclaredSignature
deriving instance ToExpr for Link

/-- The value of the closed term `decoder`, computed by compiled code. -/
unsafe def evaluateUnsafe (decoder : Expr) : MetaM (Option Method) :=
  evalExpr (Option Method) (mkApp (mkConst ``Option [.zero]) (mkConst ``Method)) decoder

/-- The value of the closed term `decoder`, computed by compiled code. -/
@[implemented_by evaluateUnsafe]
opaque evaluate (decoder : Expr) : MetaM (Option Method)

/-- The value of the closed field reference `field`, computed by compiled code. -/
unsafe def evaluateFieldUnsafe (field : Expr) : MetaM Extraction.FieldRef :=
  evalExpr Extraction.FieldRef (mkConst ``Extraction.FieldRef) field

/-- The value of the closed field reference `field`, computed by compiled code. -/
@[implemented_by evaluateFieldUnsafe]
opaque evaluateField (field : Expr) : MetaM Extraction.FieldRef

/-- Each named environment shares its raw aggregate identity expressions across decoded methods. -/
private initialize layoutIdentityCache : EnvExtension (NameMap (Std.HashMap Expr Expr)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- The raw layout expressions for identity strings used by a decoded constrained call.
    Reusing the expressions lets the kernel compare aggregate receivers by their source terms. -/
private def constrainedLayoutIdentities (decoder : Expr) (method : Method) :
    MetaM (Std.HashMap Expr Expr) := do
  let_expr CIL.Method.ofClosed? _ environment _ _ _ := decoder | return {}
  let .const name _ := environment | return {}
  unless method.code.any (fun
      | .call _ prefixes => prefixes.constrained.isSome
      | _ => false) do return {}
  if let some identities := (layoutIdentityCache.getState (← getEnv)).find? name then
    return identities
  let mut entries := mkApp (mkConst ``LayoutEnvironment.rawLayouts) environment
  let mut identities := {}
  for layout in method.environment.rawLayouts do
    let (``List.cons, #[_, entry, tail]) := (← kernelWhnf entries).getAppFnArgs | break
    let raw ← kernelWhnf entry
    unless raw.isAppOf ``RawLayout.mk do break
    let identity := raw.getArg! 0
    unless identity.isStringLit do
      identities := identities.insert (mkStrLit layout.identity) identity
    entries := tail
  modifyEnv (layoutIdentityCache.modifyState · (·.insert name identities))
  return identities

/-- The term `method` denotes, with each field whose type is that of a constant in `passed`
    written as that constant and every other field as its constructors. -/
def methodTerm (passed : Array Expr) (method : Method) : MetaM Expr := do
  let written : List (Name × Expr) := [(`code, toExpr method.code),
    (`locals, toExpr method.locals), (`localKinds, toExpr method.localKinds),
    (`staticSites, toExpr method.staticSites),
    (`opaqueVectorLocals, toExpr method.opaqueVectorLocals),
    (`parameterHomes, toExpr method.parameterHomes), (`declared, toExpr method.declared),
    (`links, toExpr method.links), (`returnsValue, toExpr method.returnsValue)]
  let mut fields := #[]
  for field in getStructureFields (← getEnv) ``CIL.Method do
    let fieldType := (← inferType (mkConst (``CIL.Method ++ field))).bindingBody!
    let mut constant := none
    for candidate in passed do
      if (← inferType candidate) == fieldType then constant := some candidate
    match constant, written.lookup field with
    | some candidate, _ => fields := fields.push candidate
    | none, some value => fields := fields.push value
    | none, none => throwError "cil_decoded_method: no term is written for the field {field}"
  return mkAppN (mkConst ``CIL.Method.mk) fields

/-- The term `written` that `literal` gives for the initial value `value` of a local, with a
    zero-filled aggregate written as `List.replicate size 0`: the form `LocalKind.initialValue`
    and an extraction give, which a caller's hypothesis about making the local names. -/
def initialLocal (value : Value) (written : Expr) : MetaM Expr := do
  let .aggregate bytes := value | return written
  unless bytes.all (· == 0) do return written
  let bytesType := (← inferType (mkConst ``Value.aggregate)).bindingDomain!
  let byteType := bytesType.appArg!
  let zeros := mkApp3 (mkConst ``List.replicate [.zero]) byteType
    (← mkNumeral (mkConst ``Nat) bytes.length) (← mkNumeral byteType 0)
  return mkApp (mkConst ``Value.aggregate) zeros

/-- The literal list `written` of the initial values `values`, each written by `initialLocal`. -/
def initialLocals : List Value → Expr → MetaM Expr
  | value :: values, written => do
    let some (type, head, tail) := written.app3? ``List.cons
      | throwError "cil_decoded_method: the locals {written} are not a literal list"
    return mkApp3 written.getAppFn type (← initialLocal value head) (← initialLocals values tail)
  | [], written => return written

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
  let declaration := Declaration.thmDecl {
    name, levelParams := [], type := statement,
    value := mkApp2 (mkConst ``Eq.refl [← getLevel type]) type left }
  -- Checked before the command goes on, so a refused fact stops it rather than being logged after
  -- the facts that follow it; a window per declaration keeps earlier work out of its budget.
  try withOptions (Elab.async.set · false) <| withCurrHeartbeats <| addDecl declaration
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    throwError "cil_decoded_method: the kernel does not reduce both sides of {name} to one term"
  addDocStringCore name doc

/-- The `FieldRef` constants a decoded method's field operands are written as. -/
syntax decodedFields := "[" ident,* "]"

/-- `cil_decoded_method name [field, ...] := decoder` defines `name` as the method the closed
    `Option CIL.Method` `decoder` evaluates to, with each field operand equal to a listed
    `FieldRef` constant written as that constant and each zero-initialized struct local as
    `List.replicate size 0`, proves `name_decoder_eq : decoder = some name` and the `@[cil_code]`
    facts `name_{field}` for each of `factFields`. Fails when the decoder gives `none` or does
    not reduce, or when a listed constant names no field operand. -/
syntax (name := decodedMethod)
  "cil_decoded_method " ident (decodedFields)? " := " term : command

elab_rules : command
  | `(cil_decoded_method $nameSyntax:ident $[$fieldsSyntax:decodedFields]? := $decoderSyntax) =>
    liftTermElabM do
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
    let fieldIdents : Array Ident ← match fieldsSyntax with
      | none => pure #[]
      | some listedSyntax =>
        match listedSyntax with
        | `(decodedFields| [$listed,*]) => pure listed.getElems
        | _ => throwError "cil_decoded_method: malformed field list {listedSyntax}"
    let mut fieldConstants : Std.HashMap Expr Expr := {}
    let mut fieldNames := #[]
    for fieldIdent in fieldIdents do
      let fieldName ← realizeGlobalConstNoOverloadWithInfo fieldIdent
      let constant := mkConst fieldName
      unless (← inferType constant) == mkConst ``Extraction.FieldRef do
        throwError "cil_decoded_method: {fieldName} is not a field reference"
      fieldConstants := fieldConstants.insert (toExpr (← evaluateField constant)) constant
      fieldNames := fieldNames.push fieldName
    let some method ← evaluate decoder
      | throwError "cil_decoded_method: the decoder gives no method{indentExpr decoder}"
    let identities ← constrainedLayoutIdentities decoder method
    let named (term : Expr) : Option Expr :=
      if passed.contains term then some term else fieldConstants.get? term <|> identities.get? term
    let written ← literal named methodType (← methodTerm passed method)
    let fields := getStructureFields (← getEnv) ``CIL.Method
    let some localsPosition := fields.idxOf? `locals
      | throwError "cil_decoded_method: CIL.Method has no field locals"
    let arguments := written.getAppArgs
    let value := mkAppN written.getAppFn <| arguments.set! localsPosition
      (← initialLocals method.locals arguments[localsPosition]!)
    let used := value.getUsedConstantsAsSet
    for fieldName in fieldNames do
      unless used.contains fieldName do
        throwError "cil_decoded_method: the decoded method has no field operand {fieldName}"
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := methodType, value,
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    -- Without it, unfolding the method in the module that defines it, as a batch does, fails.
    enableRealizationsForConst name
    addDeclarationRangesFromSyntax name (← getRef) nameSyntax
    addDocStringCore name s!"The method `{decoderSyntax}` decodes to."
    let method := mkConst name
    proveByReduction (name.appendAfter "_decoder_eq") s!"`{name}` is the decoded method."
      (← mkEq decoder (mkApp2 (mkConst ``Option.some [.zero]) methodType method))
    for field in factFields do
      let some position := fields.idxOf? field
        | throwError "cil_decoded_method: CIL.Method has no field {field}"
      let fact := name.appendAfter s!"_{field}"
      proveByReduction fact s!"The {field} of `{name}`."
        (← mkEq (mkApp (mkConst (``CIL.Method ++ field)) method) value.getAppArgs[position]!)
      addSimpTheorem simpSet fact (post := true) (inv := false) .global (eval_prio default)

end CIL.Extraction.DecodedDefinition
