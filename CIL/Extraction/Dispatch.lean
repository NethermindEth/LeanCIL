import CIL.Extraction.Assemblies
import CIL.Extraction.Folds
import CIL.Extraction.FlowIndex
import Std.Data.TreeSet.Lemmas
import Std.Data.TreeMap.Lemmas

/-!
Constrained-call dispatch metadata and indexed resolution, equivalent to raw-list search.
-/

namespace CIL.Extraction

/-- A declared method and its explicit interface-slot overrides, before dispatch resolution. -/
structure DispatchMethod where
  token : Nat
  name : String
  hasThis : Bool
  isPublic : Bool
  isAbstract : Bool
  isVirtual : Bool
  hasBody : Bool
  genericArity : Nat
  explicitThis : Bool
  callingConvention : Nat
  attributes : Nat
  implementation : Nat
  returnType : TypeExpr
  parameters : List TypeExpr
  overrides : List (Nat × TypeExpr)
  owner : TypeExpr := .void
  ownerArguments : List TypeExpr := []
  deriving DecidableEq, Repr

/-- Direct interfaces and declared methods of one metadata type; no inherited dispatch table. -/
structure DispatchType where
  identity : TypeExpr
  valueType : Bool
  interfaceType : Bool
  interfaces : List TypeExpr
  methods : List DispatchMethod
  /-- The pinned assembly whose metadata supplied this entry. -/
  assembly : AssemblyPin := {}
  /-- A class's base class, or `.void` when it derives from `System.Object` or is no class. -/
  base : TypeExpr := .void
  /-- The class is abstract, so it has no instances of its own. -/
  abstractType : Bool := false
  deriving DecidableEq, Repr

/-- The entry names a valid pin that scopes its type. Dispatch reads only such entries, so every
    type it consults comes from the selected assembly or a pinned reference, never elsewhere. -/
def DispatchType.pinned (entry : DispatchType) : Bool :=
  pinIdentityValid entry.assembly.identity &&
    match managedOwner entry.identity with
    | some (owner, _) => ownedBy entry.assembly.identity owner
    | none => false

/-- Ambiguous metadata never selects an arbitrary first candidate. -/
private def unique : List α → Option α
  | [value] => some value
  | _ => none

/-- The method type arguments of a call: the prefix of `typeArguments` before the owner's. -/
def siteMethodArguments (site : CallSite) : List TypeExpr :=
  site.typeArguments.take (site.typeArguments.length - site.ownerArgumentCount)

/-- The ECMA-335 calling-convention bit of a generic method signature. -/
private def genericCallingConvention : Nat := 16

/-- The signature, including whether a receiver is passed, must agree before a method can
    implement the declared slot. A generic method's own parameters are closed at the site's
    method type arguments, whose count must equal its arity. -/
private def signatureMatches (method : DispatchMethod) (site : CallSite) : Bool :=
  let arguments := siteMethodArguments site
  method.hasThis == site.hasThis && !method.explicitThis &&
    method.callingConvention == (if arguments.isEmpty then 0 else genericCallingConvention) &&
    method.genericArity == arguments.length &&
    substituteType arguments method.returnType == some site.returnType &&
    (method.returnType != .void) == site.returnsValue &&
    method.parameters.mapM (substituteType arguments) == some site.parameterTypes &&
    method.parameters.length == site.parameterCount

/-- The generic type definition of a closed owner, which carries its assembly scope. -/
def ownerBase : TypeExpr → TypeExpr
  | .apply owner _ => ownerBase owner
  | type => type

/-- Generic dispatch metadata must name precisely the closed receiver specialization. -/
def dispatchOwnerMatches (receiver : TypeExpr) (target : DispatchMethod) : Bool :=
  if target.ownerArguments.isEmpty then target.owner == .void else
  match receiver with
  | .aggregate identity _ => genericOwnerIdentity target.owner target.ownerArguments == some identity
  | _ => false

/-- A closed struct slot uses its receiver's layout identity; interface identities stay structural. -/
private def declaringIdentity (receiver : TypeExpr) (site : CallSite) : TypeExpr :=
  match receiver with
  | .aggregate identity _ =>
    if !site.typeArguments.isEmpty &&
        genericOwnerIdentity (ownerBase site.declaringType) site.typeArguments == some identity
      then receiver else site.declaringType
  | _ => site.declaringType

/-- Owner arguments are the site's closed owner arguments; method arguments precede them, must
    be closed, and are admitted only for static slots. -/
private def slotArgumentsValid (site : CallSite) : Bool :=
  match managedOwner site.declaringType with
  | some (_, arguments) => arguments.length == site.ownerArgumentCount &&
      site.ownerArgumentCount ≤ site.typeArguments.length &&
      site.typeArguments.drop (site.typeArguments.length - site.ownerArgumentCount) ==
        arguments &&
      (!site.hasThis || (siteMethodArguments site).isEmpty) &&
      (siteMethodArguments site).all fun argument => substituteType [] argument == some argument
  | none => false

/-- Where a constrained call lands: a method declared on the receiver, or the most specific
    interface-level body of a static virtual slot that the receiver does not implement, declared
    by the closed interface `owner`: the slot's own default or another interface's `MethodImpl`. -/
inductive ConstrainedTarget where
  | implementation (method : DispatchMethod)
  | interfaceBody (owner : TypeExpr) (method : DispatchMethod)
  deriving DecidableEq, Repr

/-- The selected declaration, before instantiation at the site's method type arguments. -/
def ConstrainedTarget.method : ConstrainedTarget → DispatchMethod
  | .implementation method | .interfaceBody _ method => method

/-- The closed type declaring the target: the receiver or its generic owner application for an
    implementation, and the closed declaring interface for an interface-level body. -/
def ConstrainedTarget.declaringType (receiver : TypeExpr) : ConstrainedTarget → TypeExpr
  | .implementation method => if method.ownerArguments.isEmpty then receiver else
      method.ownerArguments.foldl TypeExpr.apply method.owner
  | .interfaceBody owner _ => owner

/-- `derived` is `base` or inherits it through a chain of at most `fuel` catalog interface
    lists. A missing entry ends its chain, so this never claims an inheritance it cannot see. -/
def derivesFrom (find : TypeExpr → Option DispatchType) : Nat → TypeExpr → TypeExpr → Bool
  | 0, derived, base => derived == base
  | fuel + 1, derived, base => derived == base ||
      (find derived).any fun entry => entry.interfaces.any (derivesFrom find fuel · base)

/-- The one candidate whose declaring interface inherits every other candidate's. Two bodies on
    one interface, or on unrelated interfaces, leave no unique winner, as the runtime rejects. -/
def mostSpecific (derives : TypeExpr → TypeExpr → Bool)
    (candidates : List (TypeExpr × DispatchMethod)) : Option (TypeExpr × DispatchMethod) :=
  unique (candidates.filter fun candidate =>
    candidates.all fun other => derives candidate.1 other.1)

/-- `unique` selects exactly the sole element of a singleton. -/
private theorem unique_eq_some {values : List α} {value : α} :
    unique values = some value ↔ values = [value] := by
  match values with
  | [] => simp [unique]
  | [single] => simp [unique]
  | _ :: _ :: _ => simp [unique]

#print axioms unique_eq_some

/-- The selected candidate is a candidate, inherits every candidate's interface, and is the only
    candidate that does. -/
theorem mostSpecific_spec {derives : TypeExpr → TypeExpr → Bool}
    {candidates : List (TypeExpr × DispatchMethod)} {winner : TypeExpr × DispatchMethod}
    (selected : mostSpecific derives candidates = some winner) :
    winner ∈ candidates ∧ (∀ other ∈ candidates, derives winner.1 other.1 = true) ∧
      ∀ candidate ∈ candidates, (∀ other ∈ candidates, derives candidate.1 other.1 = true) →
        candidate = winner := by
  have single := unique_eq_some.mp selected
  have member : winner ∈ candidates.filter fun candidate =>
      candidates.all fun other => derives candidate.1 other.1 := by
    rw [single]; exact List.mem_singleton_self winner
  simp only [List.mem_filter, List.all_eq_true] at member
  refine ⟨member.1, member.2, fun candidate present dominates => ?_⟩
  have kept : candidate ∈ candidates.filter fun candidate =>
      candidates.all fun other => derives candidate.1 other.1 := by
    simp only [List.mem_filter, List.all_eq_true]
    exact ⟨present, dominates⟩
  rw [single] at kept
  exact List.mem_singleton.mp kept

#print axioms mostSpecific_spec

/-- The most specific interface-level body of a static slot: the slot itself or an interface
    `MethodImpl` of it on an interface the receiver lists. Every listed interface must be a
    pinned catalog interface whose bases the receiver also lists, so no body is unseen. -/
private def interfaceTarget (find : TypeExpr → Option DispatchType) (concrete : DispatchType)
    (slot : DispatchMethod) (token : Nat) (site : CallSite) : Option ConstrainedTarget := do
  let entries ← concrete.interfaces.mapM find
  if !(entries.all fun entry => entry.interfaceType && entry.pinned &&
      entry.interfaces.all concrete.interfaces.contains) then none else pure ()
  let candidates := (site.declaringType, slot) :: entries.flatMap fun entry =>
    (entry.methods.filter fun method => method.overrides.contains (token, site.declaringType)).map
      ((entry.identity, ·))
  let (owner, method) ← mostSpecific (derivesFrom find concrete.interfaces.length) candidates
  pure (.interfaceBody owner method)

/-- Recorded overrides take precedence. Otherwise an abstract slot needs exactly one public
    same-signature method, and beside a default body such a method is ambiguous. With neither, a
    static slot runs its most specific interface-level body. -/
private def selectTarget (site : CallSite) (slot : DispatchMethod)
    (explicit implicit : List DispatchMethod) (interfaceLevel : Option ConstrainedTarget) :
    Option ConstrainedTarget :=
  if !explicit.isEmpty then ConstrainedTarget.implementation <$> unique explicit
  else if !implicit.isEmpty then
    if slot.isAbstract then ConstrainedTarget.implementation <$> unique implicit else none
  else if site.hasThis then none
  else interfaceLevel

/-- Generic owner metadata must name the receiver for an implementation, and the declaring
    closed interface, with its arity, for an interface-level body. -/
private def targetOwnerMatches (receiver : TypeExpr) : ConstrainedTarget → Bool
  | .implementation method => dispatchOwnerMatches receiver method
  | .interfaceBody owner method =>
      (managedOwner owner).any (·.2.length == method.ownerArguments.length) &&
      if method.ownerArguments.isEmpty then method.owner == .void else
        method.ownerArguments.foldl TypeExpr.apply method.owner == owner

/-- A selected target must have a body and match the site and its declaring owner. A
    re-abstracted or missing body fails here, after selection, so no less specific body runs. -/
private def checkedTarget (receiver : TypeExpr) (site : CallSite) (target : ConstrainedTarget) :
    Option ConstrainedTarget :=
  if target.method.isAbstract || !target.method.hasBody ||
      target.method.name ∈ [".ctor", ".cctor"] || !signatureMatches target.method site ||
      !targetOwnerMatches receiver target then none
  else some target

/-- Resolve a concrete value-type method or a directly implemented interface slot. A static
    slot resolves only through an interface, to a static implementation on the receiver or to
    the most specific interface-level body. Explicit overrides take precedence; missing,
    ambiguous, unpinned and boxing cases fail. This list-based specification states the
    equivalence of indexed production resolution. -/
def resolveConstrained (types : List DispatchType) (receiver : TypeExpr) (site : CallSite) :
    Option ConstrainedTarget := do
  let .aggregate .. := receiver | none
  if !slotArgumentsValid site then
    none else pure ()
  let .managed token := site.target | none
  let concrete ← unique (types.filter fun type => type.identity == receiver)
  if !concrete.valueType || concrete.interfaceType || !concrete.pinned then none else pure ()
  let declaring ← unique (types.filter fun type => type.identity == declaringIdentity receiver site)
  if !declaring.pinned then none else pure ()
  let slot ← unique (declaring.methods.filter fun method => method.token == token)
  if slot.name != site.name || !signatureMatches slot site then none else pure ()
  let target ← if receiver == declaring.identity then
      (if site.hasThis then some (.implementation slot) else none) else do
    if !declaring.interfaceType || !slot.isVirtual ||
        !concrete.interfaces.contains declaring.identity then none else pure ()
    selectTarget site slot
      (concrete.methods.filter fun method => method.overrides.contains (token, site.declaringType))
      (concrete.methods.filter fun method =>
        method.isPublic && method.name == slot.name && signatureMatches method site)
      (interfaceTarget
        (fun identity => unique (types.filter fun type => type.identity == identity))
        concrete slot token site)
  checkedTarget receiver site target

/-- The `NewSlot` flag of a method's attributes: the method introduces a slot rather than
    overriding the nearest inherited one (ECMA-335 II.10.3.1). -/
def newSlotAttribute : Nat := 0x100

/-- Whether a catalog method introduces a new virtual slot. -/
def DispatchMethod.isNewSlot (method : DispatchMethod) : Bool :=
  method.attributes &&& newSlotAttribute != 0

/-- The catalog classes from `current` up to and including `root`, following `base`, in at most
    `fuel` entries; `none` when a class is missing or the chain ends without reaching `root`. -/
def classChain (find : TypeExpr → Option DispatchType) : Nat → TypeExpr → TypeExpr →
    Option (List DispatchType)
  | 0, _, _ => none
  | fuel + 1, current, root => do
    let entry ← find current
    if current == root then pure [entry] else
    match entry.base with
    | .void => none
    | base => (entry :: ·) <$> classChain find fuel base root

/-- The body `callvirt` of the class slot `site` names runs on an instance of exactly `runtime`,
    with the class declaring it: the nearest class from `runtime` up to the slot's class with a
    virtual method of the slot's name and signature (ECMA-335 II.10.3.2). The slot must
    introduce itself (`NewSlot`) in a non-generic class; every class on the chain is a pinned
    class of the slot's assembly, and none has a `MethodImpl` naming a class of the chain. A
    nearer match that starts its own slot (hiding), is abstract or is ambiguous fails rather
    than select a less specific body. -/
def resolveVirtualWith (find : TypeExpr → Option DispatchType) (fuel : Nat) (runtime : TypeExpr)
    (site : CallSite) : Option (TypeExpr × DispatchMethod) := do
  let .managed token := site.target | none
  if !site.hasThis || !site.typeArguments.isEmpty then none else pure ()
  let declaring ← find site.declaringType
  let slot ← unique (declaring.methods.filter fun method => method.token == token)
  if !slot.isVirtual || !slot.isNewSlot || slot.name != site.name ||
      !signatureMatches slot site then none else pure ()
  let chain ← classChain find fuel runtime site.declaringType
  let classes := chain.map (·.identity)
  if !(chain.all fun entry => entry.pinned && !entry.valueType && !entry.interfaceType &&
      entry.assembly == declaring.assembly &&
      entry.methods.all fun method =>
        method.overrides.all fun (_, owner) => !classes.contains owner)
    then none else pure ()
  let selected ← chain.findSome? fun entry =>
    if entry.identity == site.declaringType then some (entry.identity, some slot) else
    match entry.methods.filter fun method =>
        method.isVirtual && method.name == slot.name && signatureMatches method site with
    | [] => none
    | [method] => some (entry.identity, if method.isNewSlot then none else some method)
    | _ => some (entry.identity, none)
  let (owner, some method) := selected | none
  if method.isAbstract || !method.hasBody then none else pure (owner, method)

/-- Exactly one catalog entry with this identity, as dispatch reads it. -/
def findDispatchType (types : List DispatchType) (identity : TypeExpr) : Option DispatchType :=
  unique (types.filter fun type => type.identity == identity)

/-- Every class a virtual call's table lists is bound to the body `resolveVirtualWith` selects:
    an extracted, non-generic instance method of the selecting class with the site's signature.
    Each class appears once, and no concrete catalog class whose chain reaches the slot's class
    is left out. -/
def virtualTableValid (types : List DispatchType) (find : TypeExpr → Option DispatchType)
    (methods : Nat → Option SpecializedMethod) (site : CallSite)
    (targets : List (TypeExpr × Nat)) (count : Nat) : Bool :=
  let fuel := types.length
  !targets.isEmpty && decide (targets.map Prod.fst).Nodup &&
  count == site.parameterCount + 1 &&
  (targets.all fun (runtime, index) =>
    match resolveVirtualWith find fuel runtime site, methods index with
    | some (owner, method), some callee =>
      callee.arguments.isEmpty && callee.closed.token == method.token &&
      managedOwner owner == some (callee.closed.owner, []) &&
      callee.closed.objectReceiver && callee.closed.hasThis && !callee.closed.code.isEmpty &&
      callee.closed.attributes == method.attributes &&
      callee.closed.returnType == site.returnType &&
      callee.closed.parameters == site.parameterTypes
    | _, _ => false) &&
  types.all fun entry => entry.abstractType ||
    (classChain find fuel entry.identity site.declaringType).isNone ||
    targets.any (·.1 == entry.identity)

/-- A class `castclass` and `isinst` may test against: a pinned, non-generic catalog class other
    than `System.Object`. An instance's runtime lineage lists exactly its own and its admitted
    base classes, so it decides such a test, but not one against an interface or the root. -/
def castTargetValid (find : TypeExpr → Option DispatchType) (target : TypeExpr) : Bool :=
  match target with
  | .object _ name => name != "System.Object" && (find target).any fun entry =>
    entry.pinned && !entry.valueType && !entry.interfaceType
  | _ => false


/-- Ordered candidate buckets retain every matching metadata entry. -/
private def groupIndex {α κ : Type} [Ord κ] (key : α → κ) :
    List α → Std.TreeMap κ (List α)
  | [] => ∅
  | value :: rest =>
    let index := groupIndex key rest
    index.insert (key value) (value :: index.getD (key value) [])
/-- Each bucket is exactly the corresponding ordered filter of the input. -/
private theorem groupIndex_get {α κ : Type} [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ]
    [BEq κ] [LawfulBEq κ] (key : α → κ) (values : List α) (query : κ) :
    (groupIndex key values).getD query [] = values.filter (fun value => key value == query) := by
  induction values with
  | nil => simp [groupIndex]
  | cons value rest ih =>
    simp only [groupIndex, Std.TreeMap.getD_insert, Std.compare_eq_iff_eq]
    by_cases same : key value = query
    · simp [same, ih]
    · simp [same, ih]

#print axioms groupIndex_get

/-- Add one candidate at each advertised key, without duplicating repeated keys. -/
private def insertKeys (base : Std.TreeMap Nat (List α)) (value : α) :
    List Nat → Std.TreeMap Nat (List α)
  | [] => base
  | key :: rest => (insertKeys base value rest).insert key (value :: base.getD key [])
/-- Repeated keys add the candidate only once to a bucket. -/
private theorem insertKeys_get (base : Std.TreeMap Nat (List α)) (value : α)
    (keys : List Nat) (query : Nat) :
    (insertKeys base value keys).getD query [] =
      if keys.contains query then value :: base.getD query [] else base.getD query [] := by
  induction keys with
  | nil => simp [insertKeys]
  | cons key keys ih =>
    simp only [insertKeys, Std.TreeMap.getD_insert, Nat.compare_eq_eq, List.contains_cons]
    by_cases same : key = query
    · subst key; simp
    · simp [same, Ne.symm same, ih]

#print axioms insertKeys_get

/-- Candidate buckets for metadata entries that advertise several keys. -/
private def multiGroup (keys : α → List Nat) : List α → Std.TreeMap Nat (List α)
  | [] => ∅
  | value :: rest => insertKeys (multiGroup keys rest) value (keys value)
/-- Multi-key buckets preserve list-membership filtering and candidate order. -/
private theorem multiGroup_get (keys : α → List Nat) (values : List α) (query : Nat) :
    (multiGroup keys values).getD query [] =
      values.filter (fun value => (keys value).contains query) := by
  induction values with
  | nil => simp [multiGroup]
  | cons value values ih =>
    simp only [multiGroup, insertKeys_get, ih, List.filter_cons]

#print axioms multiGroup_get

/-- Linked UTF-8 bytes avoid indexed string decoding while comparing dispatch keys. -/
private def keyBytes (text : String) : List UInt8 := text.toByteArray.data.toList

/-- Constructor-delimited type buckets retain scopes and aggregate positions. Exact identity
    checks below remain mandatory even if two encodings were to share a bucket. -/
private def typeKeyInto : TypeExpr → List (List UInt8) → List (List UInt8)
  | .void, rest => keyBytes "void" :: rest
  | .atom scope name, rest => keyBytes "atom" :: keyBytes scope :: keyBytes name :: rest
  | .aggregate identity index, rest =>
    keyBytes "aggregate" :: keyBytes identity :: keyBytes (toString index) :: rest
  | .enum identity underlying, rest =>
    keyBytes "enum" :: keyBytes identity :: typeKeyInto underlying rest
  | .parameter index, rest => keyBytes "parameter" :: keyBytes (toString index) :: rest
  | .byref element, rest => keyBytes "byref" :: typeKeyInto element rest
  | .pointer element, rest => keyBytes "pointer" :: typeKeyInto element rest
  | .array element, rest => keyBytes "array" :: typeKeyInto element rest
  | .functionPointer result parameters convention hasThis explicitThis, rest =>
    keyBytes "functionPointer" :: keyBytes (toString convention) ::
      keyBytes (toString hasThis) :: keyBytes (toString explicitThis) ::
      typeKeyInto result (typeKeyInto parameters rest)
  | .signatureParameter head tail, rest =>
    keyBytes "signatureParameter" :: typeKeyInto head (typeKeyInto tail rest)
  | .constructor scope name, rest =>
    keyBytes "constructor" :: keyBytes scope :: keyBytes name :: rest
  | .apply constructor argument, rest =>
    keyBytes "apply" :: typeKeyInto constructor (typeKeyInto argument rest)
  | .object scope name, rest =>
    keyBytes "object" :: keyBytes scope :: keyBytes name :: rest

/-- Raw metadata and its order-preserving method candidate indexes. -/
structure DispatchTypeIndex where
  raw : DispatchType
  tokens : Std.TreeMap Nat (List DispatchMethod)
  names : Std.TreeMap String (List DispatchMethod)
  overrides : Std.TreeMap Nat (List DispatchMethod)

/-- Build candidate lists without discarding duplicate tokens, names or implementations. -/
def DispatchTypeIndex.ofType (type : DispatchType) : DispatchTypeIndex :=
  ⟨type, groupIndex (·.token) type.methods, groupIndex (·.name) type.methods,
    multiGroup (fun method => method.overrides.map Prod.fst) type.methods⟩

/-- Dispatch type buckets; exact identity filtering preserves duplicate ambiguity. -/
def DispatchIndex := Std.TreeMap (List (List UInt8)) (List DispatchTypeIndex)

/-- Construct all type and method indexes once for a metadata catalog. -/
def DispatchIndex.ofTypes (types : List DispatchType) : DispatchIndex :=
  groupIndex (fun entry => typeKeyInto entry.raw.identity []) (types.map DispatchTypeIndex.ofType)

/-- Select exactly one type with the requested full identity, including aggregate position. -/
def DispatchIndex.findType (index : DispatchIndex) (identity : TypeExpr) :
    Option DispatchTypeIndex :=
  unique ((index.getD (typeKeyInto identity []) []).filter fun entry =>
    entry.raw.identity == identity)

/-- Mapping candidates preserves the exactly-one requirement. -/
private theorem unique_map (f : α → β) (values : List α) :
    unique (values.map f) = (unique values).map f := by
  cases values with
  | nil => rfl
  | cons value rest => cases rest <;> rfl

#print axioms unique_map

/-- The bucket index selects exactly the unique type selected by the raw-list rule. -/
theorem DispatchIndex.findType_ofTypes (types : List DispatchType) (identity : TypeExpr) :
    (DispatchIndex.ofTypes types).findType identity =
      (unique (types.filter (fun type => type.identity == identity))).map
        DispatchTypeIndex.ofType := by
  simp only [DispatchIndex.findType, DispatchIndex.ofTypes, groupIndex_get, List.filter_filter,
    List.filter_map, Function.comp_def, DispatchTypeIndex.ofType]
  have predicates : (fun type : DispatchType =>
      (type.identity == identity && typeKeyInto type.identity [] == typeKeyInto identity [])) =
      (fun type => type.identity == identity) := by
    funext type
    by_cases same : type.identity = identity <;> simp [same]
  rw [predicates, unique_map]

#print axioms DispatchIndex.findType_ofTypes

/-- The indexed lookup finds exactly the entry `findDispatchType` does. -/
theorem DispatchIndex.findType_raw (types : List DispatchType) :
    (fun identity => ((DispatchIndex.ofTypes types).findType identity).map (·.raw)) =
      findDispatchType types := by
  funext identity
  rw [DispatchIndex.findType_ofTypes, Option.map_map]
  unfold findDispatchType
  cases unique (types.filter fun type => type.identity == identity) <;> rfl

#print axioms DispatchIndex.findType_raw

/-- Resolve a constrained call against indexed candidates, retaining all original filters. -/
def DispatchIndex.resolve (index : DispatchIndex) (receiver : TypeExpr) (site : CallSite) :
    Option ConstrainedTarget := do
  let .aggregate .. := receiver | none
  if !slotArgumentsValid site then
    none else pure ()
  let .managed token := site.target | none
  let concrete ← index.findType receiver
  if !concrete.raw.valueType || concrete.raw.interfaceType || !concrete.raw.pinned then none
    else pure ()
  let declaring ← index.findType (declaringIdentity receiver site)
  if !declaring.raw.pinned then none else pure ()
  let slot ← unique (declaring.tokens.getD token [])
  if slot.name != site.name || !signatureMatches slot site then none else pure ()
  let target ← if receiver == declaring.raw.identity then
      (if site.hasThis then some (.implementation slot) else none) else do
    if !declaring.raw.interfaceType || !slot.isVirtual ||
        !concrete.raw.interfaces.contains declaring.raw.identity then none else pure ()
    selectTarget site slot
      ((concrete.overrides.getD token []).filter fun method =>
        method.overrides.contains (token, site.declaringType))
      ((concrete.names.getD slot.name []).filter fun method =>
        method.isPublic && signatureMatches method site)
      (interfaceTarget (fun identity => (index.findType identity).map (·.raw)) concrete.raw
        slot token site)
  checkedTarget receiver site target

/-- Indexed dispatch preserves ambiguity, explicit overrides, signatures and all failures. -/
theorem DispatchIndex.resolve_ofTypes (types : List DispatchType) (receiver : TypeExpr)
    (site : CallSite) :
    (DispatchIndex.ofTypes types).resolve receiver site =
      resolveConstrained types receiver site := by
  have overrideFilter (token : Nat) (method : DispatchMethod) :
      (method.overrides.contains (token, site.declaringType) &&
        (method.overrides.map Prod.fst).contains token) =
          method.overrides.contains (token, site.declaringType) := by
    by_cases present : (token, site.declaringType) ∈ method.overrides
    · have mapped : token ∈ method.overrides.map Prod.fst := List.mem_map.mpr
        ⟨(token, site.declaringType), present, rfl⟩
      simp [present, mapped]
    · simp [present]
  simp only [DispatchIndex.resolve, resolveConstrained, DispatchIndex.findType_ofTypes,
    Option.map_map, Option.map_id',
    Bind.bind, Option.bind_map, Function.comp_def, DispatchTypeIndex.ofType,
    groupIndex_get, multiGroup_get,
    List.filter_filter, overrideFilter]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

#print axioms DispatchIndex.resolve_ofTypes

end CIL.Extraction
