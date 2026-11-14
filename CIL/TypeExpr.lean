import Std

/-!
# Metadata type expressions

A scope-qualified form of ECMA-335 signature types, used by extraction and by typed import
slots to compare signatures as values. Custom modifiers, whose placement the ECMA-335 augments
widen, are not represented; see `docs/SOUNDNESS-SPEC.md` for the admitted placements.
Ordered type keys and candidate buckets let dispatch and layout tables find entries by type.
-/

namespace CIL.Extraction

/-- The assembly scope of the .NET 10 reference assembly that defines the primitive types. -/
def runtimeScope : String :=
  { toByteArray := ⟨#[
      83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
      86, 101, 114, 115, 105, 111, 110, 61, 49, 48, 46, 48, 46, 48, 46, 48,
      44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
      108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
      110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
      51, 97]⟩,
    isValidUTF8 :=
      ("System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
      ).isValidUTF8 }

/-- The byte-backed scope retains the exact original assembly identity. -/
theorem runtimeScope_eq :
    runtimeScope =
      "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" := by rfl
#print axioms runtimeScope_eq

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
  | constructor (scope name : String)
  | apply (constructor argument : TypeExpr)
  /-- A class on the checked heap, by its exact scope and name: an admitted class, or, as the
      type a class field holds, a class outside the model whose references are never read
      through. -/
  | object (scope name : String)
  deriving DecidableEq, Repr

/-- Structural substitution includes nested type constructors, not just signature strings. -/
def substituteType (arguments : List TypeExpr) : TypeExpr → Option TypeExpr
  | .parameter index => arguments[index]?
  | .byref element => TypeExpr.byref <$> substituteType arguments element
  | .pointer element => TypeExpr.pointer <$> substituteType arguments element
  | .array element => TypeExpr.array <$> substituteType arguments element
  | .functionPointer result parameters convention hasThis explicitThis => do
    return .functionPointer (← substituteType arguments result)
      (← substituteType arguments parameters) convention hasThis explicitThis
  | .signatureParameter head tail => do
    return .signatureParameter (← substituteType arguments head) (← substituteType arguments tail)
  | .enum identity underlying => TypeExpr.enum identity <$> substituteType arguments underlying
  | .apply constructor argument => do
    return .apply (← substituteType arguments constructor) (← substituteType arguments argument)
  | type => some type

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

/-- Constructor-delimited type buckets retain scopes and aggregate positions. Lookups through
    these keys still compare full identities, in case two encodings were to share a bucket. -/
def typeKeyInto : TypeExpr → List (List UInt8) → List (List UInt8)
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

end CIL.Extraction
