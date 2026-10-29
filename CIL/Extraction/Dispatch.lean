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
  overrides : List Nat
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
  deriving DecidableEq, Repr

/-- Ambiguous metadata never selects an arbitrary first candidate. -/
private def unique : List α → Option α
  | [value] => some value
  | _ => none

/-- The signature must agree before a method can implement the declared slot. -/
private def signatureMatches (method : DispatchMethod) (site : CallSite) : Bool :=
  method.hasThis && !method.explicitThis && method.callingConvention == 0 &&
    method.genericArity == 0 && method.returnType == site.returnType &&
    (method.returnType != .void) == site.returnsValue &&
    method.parameters == site.parameterTypes && method.parameters.length == site.parameterCount

/-- Restrict both sides of dispatch to one assembly identity. -/
private def sameScope (left right : TypeExpr) : Bool :=
  match namedType left, namedType right with
  | some (scope, _), some (other, _) => scope == other
  | _, _ => false

/-- Generic dispatch metadata must name precisely the closed receiver specialization. -/
def dispatchOwnerMatches (receiver : TypeExpr) (target : DispatchMethod) : Bool :=
  if target.ownerArguments.isEmpty then target.owner == .void else
  match receiver with
  | .aggregate identity _ => genericOwnerIdentity target.owner target.ownerArguments == some identity
  | _ => false

/-- Resolve a concrete value-type method or a directly implemented interface slot.
    Explicit overrides take precedence; missing, ambiguous and boxing cases fail.
    This list-based specification states the equivalence of indexed production resolution. -/
def resolveConstrained (types : List DispatchType) (receiver : TypeExpr) (site : CallSite) :
    Option DispatchMethod := do
  let .aggregate .. := receiver | none
  if !site.hasThis || !site.typeArguments.isEmpty then
    none else pure ()
  let .managed token := site.target | none
  let concrete ← unique (types.filter fun type => type.identity == receiver)
  if !concrete.valueType || concrete.interfaceType then none else pure ()
  let declaring ← unique (types.filter fun type => type.identity == site.declaringType)
  let slot ← unique (declaring.methods.filter fun method => method.token == token)
  if slot.name != site.name || !signatureMatches slot site then none else pure ()
  let target ← if receiver == declaring.identity then some slot else do
    if !declaring.interfaceType || !slot.isAbstract || !slot.isVirtual ||
        !concrete.interfaces.contains declaring.identity then none else pure ()
    let explicit := concrete.methods.filter fun method => method.overrides.contains token
    unique (if explicit.isEmpty then concrete.methods.filter fun method =>
      method.isPublic && method.name == slot.name && signatureMatches method site else explicit)
  if target.isAbstract || !target.hasBody || target.name ∈ [".ctor", ".cctor"] ||
      !signatureMatches target site || !dispatchOwnerMatches receiver target ||
      !sameScope (if target.ownerArguments.isEmpty then receiver else target.owner)
        site.declaringType then none else some target


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

/-- Raw metadata and its order-preserving method candidate indexes. -/
structure DispatchTypeIndex where
  raw : DispatchType
  tokens : Std.TreeMap Nat (List DispatchMethod)
  names : Std.TreeMap String (List DispatchMethod)
  overrides : Std.TreeMap Nat (List DispatchMethod)

/-- Build candidate lists without discarding duplicate tokens, names or implementations. -/
def DispatchTypeIndex.ofType (type : DispatchType) : DispatchTypeIndex :=
  ⟨type, groupIndex (·.token) type.methods, groupIndex (·.name) type.methods,
    multiGroup (·.overrides) type.methods⟩

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

/-- Resolve a constrained call against indexed candidates, retaining all original filters. -/
def DispatchIndex.resolve (index : DispatchIndex) (receiver : TypeExpr) (site : CallSite) :
    Option DispatchMethod := do
  let .aggregate .. := receiver | none
  if !site.hasThis || !site.typeArguments.isEmpty then
    none else pure ()
  let .managed token := site.target | none
  let concrete ← index.findType receiver
  if !concrete.raw.valueType || concrete.raw.interfaceType then none else pure ()
  let declaring ← index.findType site.declaringType
  let slot ← unique (declaring.tokens.getD token [])
  if slot.name != site.name || !signatureMatches slot site then none else pure ()
  let target ← if receiver == declaring.raw.identity then some slot else do
    if !declaring.raw.interfaceType || !slot.isAbstract || !slot.isVirtual ||
        !concrete.raw.interfaces.contains declaring.raw.identity then none else pure ()
    let explicit := concrete.overrides.getD token []
    unique (if explicit.isEmpty then (concrete.names.getD slot.name []).filter fun method =>
      method.isPublic && signatureMatches method site else explicit)
  if target.isAbstract || !target.hasBody || target.name ∈ [".ctor", ".cctor"] ||
      !signatureMatches target site || !dispatchOwnerMatches receiver target ||
      !sameScope (if target.ownerArguments.isEmpty then receiver else target.owner)
        site.declaringType then none else some target

/-- Indexed dispatch preserves ambiguity, explicit overrides, signatures and all failures. -/
theorem DispatchIndex.resolve_ofTypes (types : List DispatchType) (receiver : TypeExpr)
    (site : CallSite) :
    (DispatchIndex.ofTypes types).resolve receiver site =
      resolveConstrained types receiver site := by
  simp only [DispatchIndex.resolve, resolveConstrained, DispatchIndex.findType_ofTypes,
    Bind.bind, Option.bind_map, Function.comp_def, DispatchTypeIndex.ofType,
    groupIndex_get, multiGroup_get,
    List.filter_filter]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

#print axioms DispatchIndex.resolve_ofTypes

end CIL.Extraction
