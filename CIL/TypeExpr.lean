import Std
import CIL.Identity

/-!
# Metadata type expressions

A scope-qualified form of ECMA-335 signature types, used by extraction and by typed import
slots to compare signatures as values. Open member declarations preserve custom modifiers.
See `docs/SOUNDNESS-SPEC.md` for the admitted placements.
Ordered type keys and candidate buckets let dispatch and layout tables find entries by type.
-/

namespace CIL.Extraction

/-- The assembly scope of the .NET 11 reference assembly that defines the primitive types. -/
def runtimeScope : String :=
  { toByteArray := ⟨#[
      83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
      86, 101, 114, 115, 105, 111, 110, 61, 49, 49, 46, 48, 46, 48, 46, 48,
      44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
      108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
      110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
      51, 97]⟩,
    isValidUTF8 :=
      ("System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
      ).isValidUTF8 }

/-- The byte-backed scope retains the exact original assembly identity. -/
theorem runtimeScope_eq :
    runtimeScope =
      "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" := by
  rfl
#print axioms runtimeScope_eq

/-- The .NET 11 reference assembly that holds the `TypeDef` rows of the primitive types and of the
    modelled exceptions; `runtimeScope` is its display name. -/
def runtimeAssembly : AssemblyName :=
  { name := name!"System.Runtime", version := ⟨11, 0, 0, 0⟩, culture := name!"",
    publicKeyToken := some 0xb03f5f7f11d50a3a }

/-- Scoped metadata types shared by extraction and typed import slots. -/
inductive TypeExpr where
  | void
  | atom (scope name : String)
  | aggregate (identity : String) (index : Nat)
  | enum (identity : String) (underlying : TypeExpr)
  | parameter (index : Nat)
  | byref (element : TypeExpr)
  | pointer (element : TypeExpr)
  /-- A zero-based, single-dimensional CLI array signature. -/
  | array (element : TypeExpr)
  /-- A function pointer retains its exact calling convention and receiver flags. -/
  | functionPointer (result parameters : TypeExpr) (convention : Nat)
      (hasThis explicitThis : Bool)
  /-- One parameter in a function-pointer signature; the parameter chain ends in `.void`. -/
  | signatureParameter (head tail : TypeExpr)
  /-- The generic definition of a value type, by its exact scope and name; an `apply` chain over
      it is a value type instance. -/
  | constructor (scope name : String)
  /-- The generic definition of a class, interface or delegate, by its exact scope and name; an
      `apply` chain over it is a reference type instance. -/
  | objectConstructor (scope name : String)
  | apply (constructor argument : TypeExpr)
  /-- A class on the checked heap, by its exact scope and name: a class of a pinned assembly or
      `System.String`, or, as the type a class instance field holds, any class or interface,
      whose references the field never reads through. -/
  | object (scope name : String)
  /-- A custom modifier of an open member type, with the modifier's assembly and full name. -/
  | modified (required : Bool) (scope name : String) (element : TypeExpr)
  /-- An owner variable (!n) in an open declaration. A method variable (!!n) uses `parameter`. -/
  | ownerParameter (index : Nat)
  deriving DecidableEq, Repr

/-- Structural substitution includes nested type constructors, not just signature strings. -/
def substituteType (arguments : List TypeExpr) : TypeExpr → Option TypeExpr
  | .parameter index => arguments[index]?
  | .ownerParameter _ => none
  | .byref element => TypeExpr.byref <$> substituteType arguments element
  | .pointer element => TypeExpr.pointer <$> substituteType arguments element
  | .array element => TypeExpr.array <$> substituteType arguments element
  | .functionPointer result parameters convention hasThis explicitThis => do
    return .functionPointer (← substituteType arguments result)
      (← substituteType arguments parameters) convention hasThis explicitThis
  | .signatureParameter head tail => do
    return .signatureParameter (← substituteType arguments head) (← substituteType arguments tail)
  | .enum identity underlying => TypeExpr.enum identity <$> substituteType arguments underlying
  | .modified required scope name element =>
    .modified required scope name <$> substituteType arguments element
  | .apply constructor argument => do
    return .apply (← substituteType arguments constructor) (← substituteType arguments argument)
  | type => some type

/-- Whether the type is an `apply` chain over the generic definition of a class, interface or
    delegate, so that a value of it is an object reference. -/
def TypeExpr.objectApplication : TypeExpr → Bool
  | .apply (.objectConstructor _ _) _ => true
  | .apply head _ => head.objectApplication
  | _ => false

/-- Ordered candidate buckets retain every matching metadata entry. -/
def groupIndex {α κ : Type} [Ord κ] (key : α → κ) :
    List α → Std.TreeMap κ (List α)
  | [] => ∅
  | value :: rest =>
    let index := groupIndex key rest
    index.insert (key value) (value :: index.getD (key value) [])

/-- Each bucket is exactly the corresponding ordered filter of the input. -/
theorem groupIndex_get {α κ : Type} [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ]
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

/-- Linked UTF-8 bytes avoid indexed string decoding while comparing type keys. -/
def keyBytes (text : String) : List UInt8 := text.toByteArray.data.toList

/-- `runtimeScope` is the display name of `runtimeAssembly`, compared in bytes because display
    text does not reduce in the kernel; a version or token changed in only one of them fails it. -/
theorem runtimeScope_spells_runtimeAssembly :
    runtimeAssembly.culture = name!"" ∧
      (runtimeAssembly.name.bytes?.getD []).map Nat.toUInt8 ++
          keyBytes (", Version=" ++ runtimeAssembly.version.display ++
            ", Culture=neutral, PublicKeyToken=" ++
            publicKeyTokenText runtimeAssembly.publicKeyToken) =
        keyBytes runtimeScope := by
  decide +kernel

#print axioms runtimeScope_spells_runtimeAssembly

/-- Constructor-delimited type buckets retain scopes and aggregate positions. Lookups through
    these keys still compare full identities, in case two encodings were to share a bucket. -/
def typeKeyInto : TypeExpr → List (List UInt8) → List (List UInt8)
  | .modified required scope name element, rest =>
    keyBytes (if required then "modreq" else "modopt") :: keyBytes scope :: keyBytes name ::
      typeKeyInto element rest
  | .void, rest => keyBytes "void" :: rest
  | .atom scope name, rest => keyBytes "atom" :: keyBytes scope :: keyBytes name :: rest
  | .aggregate identity index, rest =>
    keyBytes "aggregate" :: keyBytes identity :: keyBytes (toString index) :: rest
  | .enum identity underlying, rest =>
    keyBytes "enum" :: keyBytes identity :: typeKeyInto underlying rest
  | .parameter index, rest => keyBytes "parameter" :: keyBytes (toString index) :: rest
  | .ownerParameter index, rest => keyBytes "ownerParameter" :: keyBytes (toString index) :: rest
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
  | .objectConstructor scope name, rest =>
    keyBytes "objectConstructor" :: keyBytes scope :: keyBytes name :: rest
  | .apply constructor argument, rest =>
    keyBytes "apply" :: typeKeyInto constructor (typeKeyInto argument rest)
  | .object scope name, rest =>
    keyBytes "object" :: keyBytes scope :: keyBytes name :: rest

end CIL.Extraction
