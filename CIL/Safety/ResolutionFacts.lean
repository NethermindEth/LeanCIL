import CIL.Resolution
import CIL.InstructionEquations
import CIL.Extraction.Generics

/-!
# Return, argument and array element metadata facts

Generated facts and value stepping share a proof-producing chooser for declared narrowing.
Primitive and non-candidate heads use storage lemmas, without evaluating code or layout tables.
`cil_resolution_facts` declares a method's return narrowing and, for each declared argument,
how the method reads it (`CIL.Method.argumentAccess`). The argument facts walk the parameter
types and the parameter homes once through named suffixes, as `CIL.CodeSuffix` does for code,
so a method's facts cost time linear in its arguments and homes.

For a method `m` with a raw method `mClosed`, the command also declares the shape of each
distinct array element type the raw code names (`CIL.Method.elementShape`). A struct element
reads its layout entries through named suffixes of the layout lists, shared by every method of
an environment constant, so the facts cost time linear in the layouts and the distinct types.
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

/-- `value` with every constructor field reduced: a natural number to a literal, and a string kept
    as written when it is a literal or a named constant and evaluated otherwise; `none` when a
    part reduces to no constructor or a string mentions a free variable. -/
partial def constructorForm? (value : Expr) : MetaM (Option Expr) := withDefault do
  let type ← whnf (← inferType value)
  if type.isConstOf ``String then
    let value := value.consumeMData
    if value.isConst || value matches .lit (.strVal _) then return some value
    if value.hasFVar || value.hasMVar then return none
    return some (mkStrLit (← unsafe evalExpr String type value))
  if type.isConstOf ``Nat then
    return (← (evalNat (← whnf value)).run).map mkNatLit
  let head ← whnf value
  let .const name _ := head.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  let arguments := head.getAppArgs
  let mut parts := arguments.extract 0 info.numParams
  for field in arguments.extract info.numParams arguments.size do
    let some reduced ← constructorForm? field | return none
    parts := parts.push reduced
  return some (mkAppN head.getAppFn parts)

/-- Reads of a method's layout tables at an index; `none` past the entries a read reaches. -/
structure LayoutReads where
  /-- The raw metadata at an index, with a proof of
      `body.environment.rawLayouts[index]? = some metadata`. -/
  declared : Nat → MetaM (Option (Expr × Expr))
  /-- The computed layout at an index, with a proof of
      `body.environment.layouts.toList[index]? = some layout`. -/
  computed : Nat → MetaM (Option (Expr × Expr))

/-- `body.elementShape (.aggregate identity index)` by the aggregate or the by-ref-like lemma,
    when the raw layouts hold the index under the same literal identity. -/
def aggregateProof? (method identity index : Expr) (reads : LayoutReads) :
    MetaM (Option Expr) := withDefault do
  let some position ← (evalNat index).run | return none
  let some (metadata, declared) ← reads.declared position | return none
  let .lit (.strVal actual) ← whnf (mkApp (mkConst ``CIL.Extraction.RawLayout.identity) metadata)
    | return none
  let .lit (.strVal expected) ← whnf identity | return none
  unless actual == expected do return none
  let identified ← mkEqRefl identity
  let byRefLike ← whnf (mkApp (mkConst ``CIL.Extraction.RawLayout.byRefLike) metadata)
  if byRefLike.isConstOf ``Bool.true then
    return some (mkAppN (mkConst ``CIL.Method.elementShape_byRefLike)
      #[method, identity, index, metadata, declared, identified, ← mkEqRefl byRefLike])
  unless byRefLike.isConstOf ``Bool.false do return none
  let some (layout, computed) ← reads.computed position | return none
  return some (mkAppN (mkConst ``CIL.Method.elementShape_aggregate)
    #[method, identity, index, metadata, layout, declared, identified, ← mkEqRefl byRefLike,
      computed])

/-- The shape of `method`'s array elements of type `type` in constructor form, with its proof: by
    the primitive, enum and class lemmas, which evaluate no type name, by the aggregate lemmas
    over `reads`, and otherwise by evaluation. -/
def elementProof? (method type : Expr) (reads : LayoutReads) :
    MetaM (Option (Expr × Expr)) := withDefault do
  let head ← whnf type
  let chosen ← match head.getAppFnArgs with
    | (``CIL.Extraction.TypeExpr.atom, _) =>
      pure ((primitive? head).map fun primitive =>
        mkApp2 (mkConst ``CIL.Method.elementShape_primitive) method (mkConst primitive))
    | (``CIL.Extraction.TypeExpr.enum, #[identity, underlying]) =>
      pure ((primitive? (← whnf underlying)).map fun primitive =>
        mkApp3 (mkConst ``CIL.Method.elementShape_enum) method identity (mkConst primitive))
    | (``CIL.Extraction.TypeExpr.object, #[scope, name]) =>
      pure (some (mkApp3 (mkConst ``CIL.Method.elementShape_object) method scope name))
    | (``CIL.Extraction.TypeExpr.aggregate, #[identity, index]) =>
      aggregateProof? method identity index reads
    | _ => pure none
  let shape := mkApp2 (mkConst ``CIL.Method.elementShape) method type
  let some proof := chosen | do
    let some value ← constructorForm? shape | return none
    return some (value, ← mkEqRefl value)
  let some (_, _, result) := (← inferType proof).eq? | return none
  let some value ← constructorForm? result | return none
  return some (value, proof)

/-- `LayoutReads` that walk a literal body's layout lists, with premises the kernel decides by
    walking them to the index; for a literal body in a proof. -/
def literalReads (method : Expr) : LayoutReads :=
  let environment := mkApp (mkConst ``CIL.Method.environment) method
  let read (list : Expr) (position : Nat) : MetaM (Option (Expr × Expr)) := do
    let (elements, _) ← listElements list
    let some element := elements[position]? | return none
    return some (element, ← mkEqRefl (← mkAppM ``Option.some #[element]))
  { declared := read (mkApp (mkConst ``CIL.LayoutEnvironment.rawLayouts) environment)
    computed := read (mkApp2 (mkConst ``Array.toList [.zero])
      (mkConst ``CIL.Extraction.ComputedLayout)
      (mkApp (mkConst ``CIL.LayoutEnvironment.layouts) environment)) }

/-- The opcodes whose type operand is an array element type: `newarr`, `ldelema`, `ldelem` and
    `stelem`. -/
def elementOpcodes : List Nat := [141, 143, 163, 164]

/-- The distinct element types the raw method `body{Closed}` names as the type operand of an
    `elementOpcodes` instruction, in order of first appearance; none without that raw method. -/
def elementTypes (body : Body) : MetaM (Array Expr) := withDefault do
  let closed := body.name.appendAfter "Closed"
  let some info := (← getEnv).find? closed | return #[]
  unless info.type.isConstOf ``CIL.Extraction.RawMethod do return #[]
  let code := mkApp (mkConst ``CIL.Extraction.RawMethod.code)
    (mkConst closed (info.levelParams.map fun _ => .zero))
  let (instructions, complete) ← listElements code
  unless complete do throwError "cil_resolution_facts: the raw code of {closed} is unresolved"
  let mut seen : Std.HashSet Expr := {}
  let mut types := #[]
  for instruction in instructions do
    let (``CIL.Extraction.RawInstruction.mk, #[_, opcode, operand]) :=
        (← whnf instruction).getAppFnArgs
      | throwError "cil_resolution_facts: an instruction of {closed} is unresolved"
    let some opcode ← (evalNat (← whnf opcode)).run
      | throwError "cil_resolution_facts: an opcode of {closed} is unresolved"
    unless elementOpcodes.contains opcode do continue
    let (``CIL.Extraction.RawOperand.type, #[type]) := (← whnf operand).getAppFnArgs | continue
    let type ← instantiateMVars type
    unless seen.contains type do
      seen := seen.insert type
      types := types.push type
  return types

/-- `LayoutReads` through named suffixes of the layout lists of `body`'s environment. An
    environment constant of this module names the suffixes once for all its methods; any other
    environment names them for `body`. Each read walks at most one block. -/
def suffixReads (body : Body) : TermElabM LayoutReads := withDefault do
  let method := body.constant ""
  let projected := mkApp (mkConst ``CIL.Method.environment) method
  let named ← whnfR (mkApp (mkConst ``CIL.Method.environment) (← whnf method))
  let current ← getEnv
  let shared := match named with
    | .const name [] => (current.getModuleIdxFor? name).isNone
    | _ => false
  let (owner, environment) := if shared then
      ({ body with name := named.constName!, levelParams := [], parameters := #[] }, named)
    else (body, projected)
  let rawType := mkConst ``CIL.Extraction.RawLayout
  let computedType := mkConst ``CIL.Extraction.ComputedLayout
  let rawList := mkApp (mkConst ``CIL.LayoutEnvironment.rawLayouts) environment
  let computedList := mkApp2 (mkConst ``Array.toList [.zero]) computedType
    (mkApp (mkConst ``CIL.LayoutEnvironment.layouts) environment)
  let (raw, rawComplete) ← listElements rawList
  let (computed, computedComplete) ← listElements computedList
  unless rawComplete && computedComplete do
    throwError "cil_resolution_facts: the layouts of {body.name} are unresolved"
  unless (← getEnv).contains (owner.name.appendAfter "_rawLayoutSuffix0") do
    declareSuffixes owner rawType "_rawLayoutSuffix"
      (fun start => s!"The raw layouts of `{owner.name}` from entry {start} on") rawList raw
    declareSuffixes owner computedType "_layoutSuffix"
      (fun start => s!"The computed layouts of `{owner.name}` from entry {start} on")
      computedList computed
  let read (stem : String) (elementType list : Expr) (elements : Array Expr) (position : Nat) :
      MetaM (Option (Expr × Expr)) := do
    let some element := elements[position]? | return none
    return some (element, ← foundAt owner stem elementType list elements position)
  return { declared := read "_rawLayoutSuffix" rawType rawList raw
           computed := read "_layoutSuffix" computedType computedList computed }

/-- Declares `body_elementShape{k}` for the `k`-th distinct element type the raw method
    `body{Closed}` names and adds each to `cil_code`. A struct element reads its layouts through
    named suffixes, so the facts cost time linear in the layouts and the distinct types. -/
def declareElementFacts (body : Body) (simpSet : SimpExtension) : TermElabM Unit := do
  let types ← elementTypes body
  if types.isEmpty then return
  let method := body.constant ""
  let aggregate ← types.anyM fun type => do
    return (← whnf type).isAppOf ``CIL.Extraction.TypeExpr.aggregate
  let reads ← if aggregate then suffixReads body else pure (literalReads method)
  for h : position in [0:types.size] do
    let type := types[position]
    -- A window per fact, so the facts of many element types do not exhaust the command's.
    withCurrHeartbeats do
      let some (shape, proof) ← elementProof? method type reads
        | throwError "cil_resolution_facts: the shape of element type {position} of \
            {body.name} is unresolved"
      body.prove s!"_elementShape{position}"
        s!"The shape of `{body.name}`'s array elements of type {position}."
        (← mkEq (mkApp2 (mkConst ``CIL.Method.elementShape) method type) shape) proof
      addSimpTheorem simpSet (body.name.appendAfter s!"_elementShape{position}") (post := false)
        (inv := false) .global (eval_prio default)

/-- Declares a method's kernel-checked return narrowing from its named signature facts, how it
    reads each declared argument and the shape of each array element type its raw method names. -/
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
      declareElementFacts body simpSet

end CIL.Safety.ResolutionFacts
