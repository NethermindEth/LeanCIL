import CIL.Resolution
import CIL.InstructionEquations

/-!
# Return and argument metadata facts

Generated facts and value stepping share a proof-producing chooser for declared narrowing.
Primitive and non-candidate heads use storage lemmas, without evaluating code or layout tables.
`cil_resolution_facts` declares a method's return narrowing and, for each declared argument,
how the method reads it (`CIL.Method.argumentAccess`). The argument facts walk the parameter
types and the parameter homes once through named suffixes, as `CIL.CodeSuffix` does for code,
so a method's facts cost time linear in its arguments and homes.

`cil_field_shape` and `cil_value_shape` declare how every method of an extraction resolves one
distinct field or type operand, against the environment those methods share, so an operand used
at many sites of many methods costs one kernel evaluation. The `cil_code` simprocs
`reduceFieldShape` and `reduceValueShape` read a method's shape of such an operand from its fact.
-/

namespace CIL.Safety.ResolutionFacts

open Lean Meta Elab Command
open CIL.InstructionEquations
  (Body listElements declareSuffixes suffixBlock suffixFrom foundAt)

/-- A recognized runtime primitive, checked by its complete scope and type name. -/
def primitive? (type : Expr) : Option Name := do
  let (``CIL.Extraction.TypeExpr.atom, #[scope, name]) := type.getAppFnArgs | none
  let scopeMatches := scope.isConstOf ``CIL.Extraction.runtimeScope ||
    match scope with
    | .lit (.strVal value) => value == CIL.Extraction.runtimeScope
    | _ => false
  unless scopeMatches do none
  let .lit (.strVal name) := name | none
  let primitive ← #[(`sbyte, "System.SByte"), (`byte, "System.Byte"),
    (`boolean, "System.Boolean"), (`int16, "System.Int16"), (`uint16, "System.UInt16"),
    (`char, "System.Char"), (`int32, "System.Int32"), (`uint32, "System.UInt32"),
    (`int64, "System.Int64"), (`uint64, "System.UInt64"), (`single, "System.Single"),
    (`double, "System.Double"), (`intPtr, "System.IntPtr"), (`uintPtr, "System.UIntPtr")].find?
      (fun entry => entry.2 == name)
  return ``CIL.PrimitiveType ++ primitive.1

/-- A storage lemma for recognized heads, or one of five checked reflexivity results. -/
def declaredProof? (layouts type : Expr) : MetaM (Option Expr) := withDefault do
  let head ← withDefault <| whnf type
  if let some primitive := primitive? head then
    return some (← mkAppM ``CIL.Extraction.declaredNarrow_primitive
      #[layouts, mkConst primitive])
  if let (``CIL.Extraction.TypeExpr.enum, #[identity, underlying]) := head.getAppFnArgs then
    if let some primitive := primitive? (← withDefault <| whnf underlying) then
      return some (← mkAppM ``CIL.Extraction.declaredNarrow_enum
        #[layouts, identity, mkConst primitive])
  let mut terminal := head
  let mut identities := #[]
  repeat
    let (``CIL.Extraction.TypeExpr.enum, #[identity, underlying]) := terminal.getAppFnArgs
      | break
    identities := identities.push identity
    terminal ← withDefault <| whnf underlying
  let candidate := mkApp (mkConst ``CIL.Extraction.TypeExpr.narrowCandidate) terminal
  if (← withDefault <| whnf candidate).isConstOf ``Bool.false then
    let mut proof ← mkAppM ``CIL.Extraction.declaredNarrow_of_not_candidate
      #[layouts, terminal, ← mkEqRefl (mkConst ``Bool.false)]
    for identity in identities.reverse do
      proof ← mkAppM ``CIL.Extraction.declaredNarrow_enum_of_none
        #[layouts, identity, terminal, proof]
      terminal := mkApp2 (mkConst ``CIL.Extraction.TypeExpr.enum) identity terminal
    return some proof
  unless terminal.isAppOf ``CIL.Extraction.TypeExpr.atom do return none
  let narrowType := mkConst ``CIL.NarrowKind
  let choices := #[mkApp (mkConst ``Option.none [.zero]) narrowType] ++
    #[``CIL.NarrowKind.signed8, ``CIL.NarrowKind.unsigned8,
      ``CIL.NarrowKind.signed16, ``CIL.NarrowKind.unsigned16].map
        (fun kind => mkApp2 (mkConst ``Option.some [.zero]) narrowType (mkConst kind))
  let expression := mkApp2 (mkConst ``CIL.Extraction.declaredNarrow) layouts type
  for choice in choices do
    if ← withoutModifyingState <| isDefEq expression choice then
      return some (← mkEqRefl choice)
  return none

/-- Return narrowing from signature facts; unresolved metadata has no selected result. -/
def returnProof? (method returns declared : Expr) : MetaM (Option Expr) := withDefault do
  let some (_, _, value) := (← inferType returns).eq? | return none
  let value ← withDefault <| whnf value
  if value.isConstOf ``Bool.false then
    return some (← mkAppOptM ``CIL.Method.returnNarrow_of_void #[some method, some returns])
  unless value.isConstOf ``Bool.true do return none
  let some (_, _, signature) := (← inferType declared).eq? | return none
  let projection := mkConst ``CIL.DeclaredSignature.returnType
  let type ← withDefault <| whnf (mkApp projection signature)
  let declaredType ← mkCongrArg projection declared
  let layouts := mkApp (mkConst ``CIL.LayoutEnvironment.rawLayouts)
    (mkApp (mkConst ``CIL.Method.environment) method)
  let some resolved ← declaredProof? layouts type | return none
  return some (← mkAppOptM ``CIL.Method.returnNarrow_of_declared
    #[some method, some type, none, some returns, some declaredType, some resolved])

/-- `Nat × LocalKind`, the type of a parameter home. -/
def homeType : Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``CIL.LocalKind)

/-- The literal `some value` or `none` of type `Option Nat`. -/
def natOption : Option Nat → Expr
  | some value => mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Nat) (mkNatLit value)
  | none => mkApp (mkConst ``Option.none [.zero]) (mkConst ``Nat)

/-- `Eq.refl value` at the type `Option Nat`. -/
def natOptionRefl (value : Option Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [.one]) (mkApp (mkConst ``Option [.zero]) (mkConst ``Nat))
    (natOption value)

/-- The raw layouts a method's declared types refer to. -/
def layoutsOf (method : Expr) : Expr :=
  mkApp (mkConst ``CIL.LayoutEnvironment.rawLayouts)
    (mkApp (mkConst ``CIL.Method.environment) method)

/-- Each home's argument index, key and slot kind, when every key reduces to a literal. -/
def homeKeys? (homes : Array Expr) : MetaM (Option (Array (Nat × Expr × Expr))) := do
  let mut keys := #[]
  for home in homes do
    let (``Prod.mk, #[_, _, key, kind]) := (← whnf home).getAppFnArgs | return none
    let some value ← (Meta.evalNat key).run | return none
    keys := keys.push (value, key, kind)
  return some keys

/-- How `method` reads argument `index`, proved from premises the kernel decides by walking the
    homes, the local kinds and the parameters up to `index`; for a literal body in a proof. -/
def argumentProof? (method : Expr) (index : Nat) : MetaM (Option Expr) := withDefault do
  let argument := mkNatLit index
  let (homes, complete) ← listElements (mkApp (mkConst ``CIL.Method.parameterHomes) method)
  unless complete do return none
  let some keys ← homeKeys? homes | return none
  if let some position := keys.findIdx? (·.1 == index) then
    let (kinds, complete) ← listElements (mkApp (mkConst ``CIL.Method.localKinds) method)
    unless complete do return none
    let slot := mkNatLit (kinds.size + position)
    return some (mkAppN (mkConst ``CIL.Method.argumentAccess_home)
      #[method, argument, mkNatLit position, slot, natOptionRefl (some position),
        ← mkEqRefl slot])
  let declared := mkApp (mkConst ``CIL.Method.declared) method
  let type ← whnf (mkApp2 (mkConst ``CIL.DeclaredSignature.argumentType) declared argument)
  match type.getAppFnArgs with
  | (``Option.none, _) =>
    return some (mkAppN (mkConst ``CIL.Method.argumentAccess_undeclared)
      #[method, argument, natOptionRefl none, ← mkEqRefl type])
  | (``Option.some, #[_, parameter]) =>
    let some narrowed ← declaredProof? (layoutsOf method) parameter | return none
    let some (_, _, result) := (← inferType narrowed).eq? | return none
    return some (mkAppN (mkConst ``CIL.Method.argumentAccess_value)
      #[method, argument, parameter, ← whnf result, natOptionRefl none, ← mkEqRefl type,
        narrowed])
  | _ => return none

/-- The fact `cil_resolution_facts` declared for how the method constant `method` reads argument
    `index`, when its statement is about exactly that method and index. -/
def argumentFact? (method index : Expr) : MetaM (Option Expr) := do
  let .const name _ := method | return none
  let some literal ← (Meta.evalNat index).run | return none
  let fact := name.appendAfter s!"_argumentAccess{literal}"
  let some info := (← getEnv).find? fact | return none
  let some (_, lhs, _) := info.type.eq? | return none
  let_expr CIL.Method.argumentAccess factMethod factIndex := lhs | return none
  unless factMethod == method do return none
  unless (← (Meta.evalNat factIndex).run) == some literal do return none
  return some (mkConst fact)

/-- That a method with no homes and no declared receiver or parameters reads argument `index` as
    it is, from premises about the method alone, which the kernel checks once for every index. -/
def plainArgumentProof? (method index : Expr) : MetaM (Option Expr) := withDefault do
  let homes := mkApp (mkConst ``CIL.Method.parameterHomes) method
  unless (← whnf homes).isAppOf ``List.nil do return none
  let declared := mkApp (mkConst ``CIL.Method.declared) method
  let parameters := mkApp (mkConst ``CIL.DeclaredSignature.parameters) declared
  unless (← whnf parameters).isAppOf ``List.nil do return none
  let receiver := mkApp (mkConst ``CIL.DeclaredSignature.receiver) declared
  unless (← whnf receiver).isAppOf ``Option.none do return none
  return some (mkAppN (mkConst ``CIL.Method.argumentAccess_plain)
    #[method, index, ← mkEqRefl homes, ← mkEqRefl parameters, ← mkEqRefl receiver])

/-- How `method` reads argument `index`: its declared fact or the plain reading of a method
    without a signature, which cost the kernel nothing per index, or else a proof from premises
    that walk the signature up to `index`. -/
def argumentAccessProof? (method index : Expr) : MetaM (Option Expr) := do
  if let some fact ← argumentFact? method index then return some fact
  if let some plain ← plainArgumentProof? method index then return some plain
  let some literal ← (Meta.evalNat index).run | return none
  argumentProof? method literal

/-- What a method's argument facts read: its receiver, parameter types and homes. -/
structure Signature where
  /-- The receiver's value, for an instance method. -/
  receiver : Option Expr
  /-- The declared parameter types, `this` excluded. -/
  parameters : Array Expr
  /-- Each home's argument index, key and slot kind, ascending by index. -/
  homes : Array (Nat × Expr × Expr)
  /-- The number of local kinds, read only when the method has homes. -/
  localCount : Nat

/-- Reads the signature of the method `body` names. Fails on a part that does not reduce to a
    literal and on homes whose argument indices do not ascend. -/
def readSignature (body : Body) : MetaM Signature := withDefault do
  let method := body.constant ""
  let declared := mkApp (mkConst ``CIL.Method.declared) method
  let receiverValue ← whnf (mkApp (mkConst ``CIL.DeclaredSignature.receiver) declared)
  let receiver ← match receiverValue.getAppFnArgs with
    | (``Option.none, _) => pure none
    | (``Option.some, #[_, value]) => pure (some value)
    | _ => throwError "cil_resolution_facts: the receiver of {body.name} is unresolved"
  let (parameters, complete) ←
    listElements (mkApp (mkConst ``CIL.DeclaredSignature.parameters) declared)
  unless complete do
    throwError "cil_resolution_facts: the parameter types of {body.name} are unresolved"
  let (homes, complete) ← listElements (mkApp (mkConst ``CIL.Method.parameterHomes) method)
  let some keys ← homeKeys? homes
    | throwError "cil_resolution_facts: the parameter homes of {body.name} are unresolved"
  unless complete do
    throwError "cil_resolution_facts: the parameter homes of {body.name} are unresolved"
  for position in [1:keys.size] do
    unless keys[position - 1]!.1 < keys[position]!.1 do
      throwError "cil_resolution_facts: the parameter homes of {body.name} do not ascend"
  let mut localCount := 0
  unless keys.isEmpty do
    let (kinds, complete) ← listElements (mkApp (mkConst ``CIL.Method.localKinds) method)
    unless complete do
      throwError "cil_resolution_facts: the local kinds of {body.name} are unresolved"
    localCount := kinds.size
  return { receiver, parameters, homes := keys, localCount }

/-- `list.drop position = suffix`, from the named suffix that starts the position's block, with
    the suffix `suffixFrom` gives; the proof walks at most one block. -/
def placedAt (body : Body) (stem : String) (elementType list : Expr) (elements : Array Expr)
    (position : Nat) : Expr × Expr :=
  let offset := position % suffixBlock
  let start := position - offset
  let next := suffixFrom body stem elementType elements position
  (mkApp8 (mkConst ``CIL.CodeSuffix.advance) elementType list (body.constant s!"{stem}{start}")
    next (mkNatLit start) (mkNatLit offset) (body.constant s!"{stem}{start}_placed")
    (mkApp2 (mkConst ``Eq.refl [.one]) (mkApp (mkConst ``List [.zero]) elementType) next), next)

/-- Declares `body_argumentAccess{index}` for every argument of the method `body` names and adds
    each to `cil_code`. One pass walks the parameter types and the homes together; each fact
    applies a `CIL.Method.argumentAccess` lemma to premises that read at most one block of a
    named suffix, so the facts cost time linear in the arguments and homes. -/
def declareArgumentFacts (body : Body) (simpSet : SimpExtension) : TermElabM Unit := do
  let signature ← readSignature body
  let shift := if signature.receiver.isSome then 1 else 0
  let count := signature.parameters.size + shift
  if count = 0 then return
  let method := body.constant ""
  let declared := mkApp (mkConst ``CIL.Method.declared) method
  let typeExpr := mkConst ``CIL.Extraction.TypeExpr
  let localKind := mkConst ``CIL.LocalKind
  let parameterList := mkApp (mkConst ``CIL.DeclaredSignature.parameters) declared
  let homeList := mkApp (mkConst ``CIL.Method.parameterHomes) method
  let homes := signature.homes
  let homeElements := homes.map fun (_, key, kind) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) localKind key kind
  declareSuffixes body typeExpr "_parameterSuffix"
    (fun start => s!"The declared parameter types of `{body.name}` from parameter {start} on")
    parameterList signature.parameters
  let ascending := body.constant "_homesAscend"
  let localCount := body.constant "_localCount"
  let boolTrue ← mkEqRefl (mkConst ``Bool.true)
  unless homes.isEmpty do
    declareSuffixes body homeType "_homeSuffix"
      (fun start => s!"The parameter homes of `{body.name}` from position {start} on")
      homeList homeElements
    let ascends := mkApp3 (mkConst ``CIL.Extraction.keysAscend) localKind (mkNatLit 0) homeList
    body.prove "_homesAscend" s!"The parameter homes of `{body.name}` ascend by argument."
      (← mkEq ascends (mkConst ``Bool.true)) boolTrue
    let length := mkApp2 (mkConst ``List.length [.zero]) localKind
      (mkApp (mkConst ``CIL.Method.localKinds) method)
    body.prove "_localCount" s!"The number of declared locals of `{body.name}`."
      (← mkEq length (mkNatLit signature.localCount))
      (← mkEqRefl (mkNatLit signature.localCount))
  let placedHome := placedAt body "_homeSuffix" homeType homeList homeElements
  let mut passed := 0
  for index in [0:count] do
    let argument := mkNatLit index
    let homed := passed < homes.size && homes[passed]!.1 == index
    -- A window per fact, so a long signature's facts do not exhaust the command's.
    withCurrHeartbeats do
      let (access, proof) ← if homed then do
          let (_, key, kind) := homes[passed]!
          let (placed, next) := placedHome passed
          let found := mkAppN (mkConst ``CIL.Extraction.findIdx?_of_keysAscend)
            #[localKind, homeList, next.appArg!, mkNatLit 0, mkNatLit passed, key, kind,
              ascending, placed]
          let shifted := mkLambda `count .default (mkConst ``Nat)
            (mkNatAdd (mkBVar 0) (mkNatLit passed))
          let slot := mkNatLit (signature.localCount + passed)
          pure (mkApp (mkConst ``CIL.ArgumentAccess.home) slot,
            mkAppN (mkConst ``CIL.Method.argumentAccess_home)
              #[method, argument, mkNatLit passed, slot, found,
                ← mkCongrArg shifted localCount])
        else do
          let unhomed ← if homes.isEmpty then pure (natOptionRefl none)
            else if passed = 0 then do
              let raised := mkAppN (mkConst ``CIL.Extraction.keysAscend_raise)
                #[localKind, homeList, mkNatLit 0, mkNatLit (index + 1), ascending, boolTrue]
              pure <| mkAppN (mkConst ``CIL.Extraction.findIdx?_none_of_keysAscend)
                #[localKind, homeList, mkNatLit (index + 1), argument, raised,
                  mkApp (mkConst ``Nat.lt_add_one) argument]
            else do
              let (_, key, kind) := homes[passed - 1]!
              let (placed, next) := placedHome (passed - 1)
              let below ← mkDecideProof (← mkLt key argument)
              pure <| mkAppN (mkConst ``CIL.Extraction.findIdx?_none_after)
                #[localKind, homeList, next.appArg!, mkNatLit 0, mkNatLit (passed - 1), key,
                  argument, kind, ascending, placed, below, boolTrue]
          let thisReceiver := if index = 0 then signature.receiver else none
          if let some receiver := thisReceiver then
            let this := mkApp3 (mkConst ``CIL.DeclaredSignature.argumentType_this) declared
              receiver (← mkEqRefl (← mkAppM ``Option.some #[receiver]))
            let narrowNone := mkApp (mkConst ``Option.none [.zero]) (mkConst ``CIL.NarrowKind)
            pure (mkApp (mkConst ``CIL.ArgumentAccess.value) narrowNone,
              mkAppN (mkConst ``CIL.Method.argumentAccess_undeclared)
                #[method, argument, unhomed, this])
          else
            let parameter := index - shift
            let type := signature.parameters[parameter]!
            let found ← foundAt body "_parameterSuffix" typeExpr parameterList
              signature.parameters parameter
            let typed ← match signature.receiver with
              | none => do
                let static ←
                  mkEqRefl (mkApp (mkConst ``Option.none [.zero]) (mkConst ``CIL.Receiver))
                pure (mkAppN (mkConst ``CIL.DeclaredSignature.argumentType_static)
                  #[declared, mkNatLit parameter, type, static, found])
              | some receiver => do
                let instanceMethod ← mkEqRefl (← mkAppM ``Option.some #[receiver])
                pure (mkAppN (mkConst ``CIL.DeclaredSignature.argumentType_instance)
                  #[declared, mkNatLit parameter, receiver, type, instanceMethod, found])
            let some narrowed ← declaredProof? (layoutsOf method) type
              | throwError "cil_resolution_facts: the narrowing of argument {index} of \
                  {body.name} is unresolved"
            let some (_, _, result) := (← inferType narrowed).eq?
              | throwError "cil_resolution_facts: expected an argument narrowing equality"
            let result ← withDefault <| whnf result
            pure (mkApp (mkConst ``CIL.ArgumentAccess.value) result,
              mkAppN (mkConst ``CIL.Method.argumentAccess_value)
                #[method, argument, type, result, unhomed, typed, narrowed])
      body.prove s!"_argumentAccess{index}" s!"How `{body.name}` reads argument {index}."
        (← mkEq (mkApp2 (mkConst ``CIL.Method.argumentAccess) method argument) access) proof
      addSimpTheorem simpSet (body.name.appendAfter s!"_argumentAccess{index}") (post := false)
        (inv := false) .global (eval_prio default)
    if homed then passed := passed + 1

/-- Declares a method's kernel-checked return narrowing from its named signature facts, and
    how it reads each declared argument. -/
syntax "cil_resolution_facts " ident : command

elab_rules : command
  | `(cil_resolution_facts $methodSyntax:ident) => liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo methodSyntax
    let info ← getConstInfo name
    let some simpSet ← getSimpExtension? `cil_code
      | throwError "cil_resolution_facts: cil_code is not registered"
    forallTelescope info.type fun parameters result => do
      unless ← isDefEq result (mkConst ``CIL.Method) do
        throwError "cil_resolution_facts: {name} does not define a CIL.Method"
      let body : Body :=
        { name, levelParams := info.levelParams, parameters, syntaxRef := methodSyntax }
      let method := body.constant ""
      let some proof ← returnProof? method (body.constant "_returnsValue")
          (body.constant "_declared")
        | throwError "cil_resolution_facts: return narrowing of {name} is unresolved"
      let some (_, _, result) := (← inferType proof).eq?
        | throwError "cil_resolution_facts: expected a return narrowing equality"
      let result ← withDefault <| whnf result
      body.prove "_returnNarrow" s!"The return narrowing of `{name}`."
        (← mkEq (mkApp (mkConst ``CIL.Method.returnNarrow) method) result) proof
      addSimpTheorem simpSet (name.appendAfter "_returnNarrow") (post := false)
        (inv := false) .global (eval_prio default)
      declareArgumentFacts body simpSet

/-! ## Field and value shapes -/

/-- The constructor form of `value`: kernel reduction to a constructor, then the same for each
    of its fields after the type parameters. Fails on a term that is stuck before a constructor
    or a literal. -/
partial def kernelValue (value : Expr) : MetaM Expr := do
  let reduced ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) value)
  if reduced.isLit then return reduced
  let .const name levels := reduced.getAppFn
    | throwError "cil_shape_facts: {value} does not reduce to a constructor"
  let some (.ctorInfo info) := (← getEnv).find? name
    | throwError "cil_shape_facts: {value} does not reduce to a constructor"
  let arguments := reduced.getAppArgs
  let fields ← (arguments.extract info.numParams arguments.size).mapM kernelValue
  return mkAppN (mkConst name levels) (arguments.extract 0 info.numParams ++ fields)

/-- Declares `{operand}_shape`: every method whose environment is `environment` resolves the
    operand as the kernel computes, read through `methodResolver` and proved from the
    environment's `environmentResolver` by `sharedLemma`. -/
def declareShapeFact (environmentName operandName : Name) (methodResolver environmentResolver
    sharedLemma shapeType : Name) (describe : String) : TermElabM Unit := do
  let environment := mkConst environmentName
  let operand := mkConst operandName
  let shape ← kernelValue (mkApp2 (mkConst environmentResolver) environment operand)
  let resolved := mkApp2 (mkConst ``Eq.refl [.one]) (mkConst shapeType) shape
  let (statement, proof) ← withLocalDecl `body .implicit (mkConst ``CIL.Method) fun body => do
    let environmentOf := mkApp (mkConst ``CIL.Method.environment) body
    withLocalDeclD `shared (← mkEq environmentOf environment) fun shared => do
      let lhs := mkApp2 (mkConst methodResolver) body operand
      let proof := mkAppN (mkConst sharedLemma) #[body, environment, operand, shape, shared,
        resolved]
      return (← mkForallFVars #[body, shared] (← mkEq lhs shape),
        ← mkLambdaFVars #[body, shared] proof)
  let name := operandName.appendAfter "_shape"
  withCurrHeartbeats do
    addDecl (.thmDecl { name, levelParams := [], type := statement, value := proof })
  addDocStringCore name s!"How every method sharing `{environmentName}` resolves {describe}."

/-- `cil_field_shape environment field` declares `field_shape`: how every method whose
    environment is `environment` resolves the field operand `field` (`CIL.Method.fieldShape`). -/
syntax "cil_field_shape " ident ident : command

/-- `cil_value_shape environment type` declares `type_shape`: how every method whose
    environment is `environment` resolves the type operand `type` (`CIL.Method.valueShape`). -/
syntax "cil_value_shape " ident ident : command

elab_rules : command
  | `(cil_field_shape $environment:ident $field:ident) => liftTermElabM do
    declareShapeFact (← realizeGlobalConstNoOverloadWithInfo environment)
      (← realizeGlobalConstNoOverloadWithInfo field) ``CIL.Method.fieldShape
      ``CIL.LayoutEnvironment.fieldShape ``CIL.Method.fieldShape_of_environment ``CIL.FieldShape
      s!"the field operand `{field.getId}`"
  | `(cil_value_shape $environment:ident $type:ident) => liftTermElabM do
    declareShapeFact (← realizeGlobalConstNoOverloadWithInfo environment)
      (← realizeGlobalConstNoOverloadWithInfo type) ``CIL.Method.valueShape
      ``CIL.LayoutEnvironment.valueShape ``CIL.Method.valueShape_of_environment ``CIL.ValueShape
      s!"the type operand `{type.getId}`"

/-- The shape of `resolver body operand` from `operand_shape`, when `operand` is a constant with
    that fact and `body`'s environment unfolds to the fact's environment. The fact's premise is
    proved by reflexivity, which the kernel checks by unfolding `body` once. -/
def sharedShape? (resolver : Name) (expression : Expr) : MetaM (Option Simp.Step) := do
  let (name, #[body, operand]) := expression.getAppFnArgs | return none
  unless name == resolver do return none
  let .const operandName _ := operand | return none
  let fact := operandName.appendAfter "_shape"
  let some info := (← getEnv).find? fact | return none
  let .forallE _ _ (.forallE _ shared _ _) _ := info.type | return none
  let some (_, _, environment) := shared.eq? | return none
  if environment.hasLooseBVars then return none
  unless ← withDefault (isDefEq (mkApp (mkConst ``CIL.Method.environment) body) environment) do
    return none
  let proof := mkApp2 (mkConst fact) body (← mkEqRefl environment)
  let some (_, resolved, shape) := (← inferType proof).eq? | return none
  unless resolved == expression do return none
  return some (.done { expr := shape, proof? := some proof })

/-- A method's field shape, from the shared fact of a field operand that has one. -/
simproc ↓ [cil_code] reduceFieldShape (CIL.Method.fieldShape _ _) := fun expression => do
  return (← sharedShape? ``CIL.Method.fieldShape expression).getD .continue

/-- A method's value shape, from the shared fact of a type operand that has one. -/
simproc ↓ [cil_code] reduceValueShape (CIL.Method.valueShape _ _) := fun expression => do
  return (← sharedShape? ``CIL.Method.valueShape expression).getD .continue

end CIL.Safety.ResolutionFacts
