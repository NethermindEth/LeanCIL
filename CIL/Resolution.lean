import CIL.Extraction.TypeStorage
import CIL.Extraction.LinkIndex
import CIL.Identity

/-!
# Narrowing from declared types

`declaredNarrow` is the small-integer narrowing a value of a declared metadata type takes:
the storage of a primitive or of an enum's underlying type. `CIL.Method.returnNarrow` applies it
to a method's declared return type. The lemmas here state the narrowing of every primitive, of
every enum over a primitive and of every other type head, so a generated fact names a method's
narrowing by lemma application and no generated proof evaluates a type name.

`CIL.Method.argumentAccess` says how a method reads each argument: from the frame slot of its
parameter home, which follows the declared locals, or as the incoming value narrowed as its
declared type requires. Under `ParameterHomesValid` the home slot is the one the argument check
expects. The key lemmas over ascending homes let a generated fact name an argument's home
position without searching the homes before it.
-/

namespace CIL

/-- The type expression the extractor writes for a primitive: its full name in the runtime
    scope. -/
def PrimitiveType.typeExpr (type : PrimitiveType) : Extraction.TypeExpr :=
  .atom Extraction.runtimeScope type.display

/-- The narrowing a value of the primitive takes; `none` for every type wider than 16 bits. -/
def PrimitiveType.narrow : PrimitiveType → Option NarrowKind
  | .sbyte => some .signed8
  | .byte | .boolean => some .unsigned8
  | .int16 => some .signed16
  | .uint16 | .char => some .unsigned16
  | .int32 | .uint32 | .int64 | .uint64 | .single | .double | .intPtr | .uintPtr => none

/-- Whether `typeStorage` admits the primitive as an enum's underlying type. -/
def PrimitiveType.enumUnderlying : PrimitiveType → Bool
  | .sbyte | .byte | .int16 | .uint16 | .int32 | .uint32 | .int64 | .uint64 => true
  | .boolean | .char | .single | .double | .intPtr | .uintPtr => false

namespace Extraction

/-- Whether `declaredNarrow` can be `some` for the type's head: an atom or an enum. -/
def TypeExpr.narrowCandidate : TypeExpr → Bool
  | .atom .. | .enum .. => true
  | _ => false

/-- The narrowing a value of declared type `type` takes: the small-integer storage of a primitive
    or of an enum's underlying type, and `none` for every other type. Any other head is `none`
    without decoding its storage, so evaluating it never compares a struct identity. -/
def declaredNarrow (layouts : List RawLayout) (type : TypeExpr) : Option NarrowKind :=
  if type.narrowCandidate then (typeStorage layouts type).bind StorageType.narrow else none

/-- A primitive narrows as its own kind, whatever the layout table. -/
theorem declaredNarrow_primitive (layouts : List RawLayout) (type : PrimitiveType) :
    declaredNarrow layouts type.typeExpr = type.narrow := by
  cases type <;> rfl

#print axioms declaredNarrow_primitive

/-- An enum narrows as its underlying primitive when `typeStorage` admits that primitive as an
    enum's underlying type, and not at all otherwise. -/
theorem declaredNarrow_enum (layouts : List RawLayout) (identity : String)
    (type : PrimitiveType) :
    declaredNarrow layouts (.enum identity type.typeExpr) =
      if type.enumUnderlying then type.narrow else none := by
  cases type <;> rfl

#print axioms declaredNarrow_enum

/-- The narrowing of a storage that is never a small-integer field is `none`. -/
theorem storage_narrow_of_wide {storage : Option StorageType}
    (wide : ∀ field, storage = some (.field field) → ∃ index, field = .aggregate index) :
    storage.bind StorageType.narrow = none := by
  cases storage with
  | none => rfl
  | some storage =>
    cases storage with
    | field field =>
      obtain ⟨index, rfl⟩ := wide field rfl
      rfl
    | _ => rfl

#print axioms storage_narrow_of_wide

/-- Span metadata is never stored as a field. -/
theorem spanStorage_ne_field (type : TypeExpr) (width : Nat) (field : FieldType) :
    spanStorage type width ≠ some (.field field) := by
  unfold spanStorage
  split
  · intro stored
    revert stored
    split
    · simp
    · simp [Option.bind_eq_bind, Option.bind_eq_some_iff]
  · simp

#print axioms spanStorage_ne_field

/-- Every head other than an atom or an enum decodes to a struct field, a reference, a
    vector, a span, an array, a callable or an object, none of which narrows. -/
theorem typeStorage_narrow_of_not_candidate (layouts : List RawLayout) (type : TypeExpr)
    (shape : type.narrowCandidate = false) :
    (typeStorage layouts type).bind StorageType.narrow = none := by
  apply storage_narrow_of_wide
  intro field stored
  cases type with
  | atom => simp [TypeExpr.narrowCandidate] at shape
  | enum => simp [TypeExpr.narrowCandidate] at shape
  | aggregate identity index =>
    simp only [typeStorage] at stored
    revert stored
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
    rintro ⟨metadata, -, chosen⟩
    split at chosen
    · simp only [pure, Option.some.injEq, StorageType.field.injEq] at chosen
      exact ⟨index, chosen.symm⟩
    · cases chosen
  | array element =>
    cases element <;> simp only [typeStorage] at stored <;> revert stored <;> (repeat' split) <;>
      simp_all [Option.map_eq_map, Option.bind_eq_bind, Option.bind_eq_some_iff]
  | pointer element =>
    cases element <;> simp only [typeStorage] at stored <;> revert stored <;> (repeat' split) <;>
      simp_all [Option.bind_eq_bind, Option.bind_eq_some_iff]
    -- A pointer to an enum: the storage of the pointer itself is a reference.
    intro storage _ _ _ result
    cases storage <;> simp at result
  | apply constructor argument =>
    cases constructor <;> simp only [typeStorage] at stored <;> revert stored <;>
      (repeat' split) <;> simp_all [Option.bind_eq_bind, Option.bind_eq_some_iff]
    -- A span: its storage is the one `spanStorage` gives.
    rintro rfl
    exact absurd ‹spanStorage _ _ = _› (spanStorage_ne_field _ _ _)
  | _ => simp [typeStorage] at stored

#print axioms typeStorage_narrow_of_not_candidate

/-- `declaredNarrow` is the narrowing of the type's decoded storage, for every type. -/
theorem declaredNarrow_eq_storage (layouts : List RawLayout) (type : TypeExpr) :
    declaredNarrow layouts type = (typeStorage layouts type).bind StorageType.narrow := by
  unfold declaredNarrow
  split
  · rfl
  · next other =>
    exact (typeStorage_narrow_of_not_candidate layouts type (by simpa using other)).symm

#print axioms declaredNarrow_eq_storage

/-- A type whose storage is never a small-integer field does not narrow. -/
theorem declaredNarrow_of_storage {layouts : List RawLayout} {type : TypeExpr}
    (wide : ∀ field, typeStorage layouts type = some (.field field) →
      ∃ index, field = .aggregate index) :
    declaredNarrow layouts type = none := by
  rw [declaredNarrow_eq_storage]
  exact storage_narrow_of_wide wide

#print axioms declaredNarrow_of_storage

/-- Only an atom or an enum narrows; any other head is `none` without decoding its storage. -/
theorem declaredNarrow_of_not_candidate (layouts : List RawLayout) (type : TypeExpr)
    (shape : type.narrowCandidate = false) : declaredNarrow layouts type = none := by
  simp [declaredNarrow, shape]

#print axioms declaredNarrow_of_not_candidate

/-- An enum cannot introduce narrowing when its underlying storage does not narrow. -/
theorem declaredNarrow_enum_of_none (layouts : List RawLayout) (identity : String)
    (type : TypeExpr) (narrow : declaredNarrow layouts type = none) :
    declaredNarrow layouts (.enum identity type) = none := by
  rw [declaredNarrow_eq_storage] at narrow ⊢
  simp only [typeStorage]
  cases stored : typeStorage layouts type with
  | none => simp
  | some storage =>
    rw [stored] at narrow
    cases storage <;> try simp
    case field kind =>
      cases kind <;> simp_all [StorageType.narrow]

#print axioms declaredNarrow_enum_of_none

end Extraction

/-- The narrowing `ret` applies: the declared return type's small-integer storage, and `none`
    for a method that returns nothing. -/
def Method.returnNarrow (body : Method) : Option NarrowKind :=
  if body.returnsValue then
    Extraction.declaredNarrow body.environment.rawLayouts body.declared.returnType
  else none

/-- A method that returns nothing does not narrow. -/
theorem Method.returnNarrow_of_void {body : Method} (returns : body.returnsValue = false) :
    body.returnNarrow = none := by
  simp [Method.returnNarrow, returns]

#print axioms Method.returnNarrow_of_void

/-- A method that returns a value narrows as its declared return type. -/
theorem Method.returnNarrow_of_declared {body : Method} {type : Extraction.TypeExpr}
    {result : Option NarrowKind} (returns : body.returnsValue = true)
    (declared : body.declared.returnType = type)
    (resolved : Extraction.declaredNarrow body.environment.rawLayouts type = result) :
    body.returnNarrow = result := by
  simp [Method.returnNarrow, returns, declared, resolved]

#print axioms Method.returnNarrow_of_declared

/-- A narrowed method returns a value. -/
theorem Method.returnsValue_of_returnNarrow {body : Method} {kind : NarrowKind}
    (narrowed : body.returnNarrow = some kind) : body.returnsValue = true := by
  unfold Method.returnNarrow at narrowed
  split at narrowed <;> simp_all

#print axioms Method.returnsValue_of_returnNarrow

/-! ## Argument access -/

namespace Extraction

/-- Below an ascending table, every entry has a larger key than `key`, so none has `key`. -/
theorem findIdx?_none_of_keysAscend {α : Type} {entries : List (Nat × α)} {lower key : Nat}
    (ascending : keysAscend lower entries = true) (below : key < lower) :
    entries.findIdx? (fun entry => entry.1 == key) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro entry member
  have := keysAscend_bound entries lower ascending entry member
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

#print axioms findIdx?_none_of_keysAscend

/-- The entry at `position` of an ascending table is the first with its key. -/
theorem findIdx?_of_keysAscend {α : Type} {entries rest : List (Nat × α)}
    {lower position key : Nat} {value : α} (ascending : keysAscend lower entries = true)
    (placed : entries.drop position = (key, value) :: rest) :
    entries.findIdx? (fun entry => entry.1 == key) = some position := by
  induction entries generalizing lower position with
  | nil => simp at placed
  | cons head tail ih =>
    obtain ⟨first, other⟩ := head
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    cases position with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq, Prod.mk.injEq] at placed
      obtain ⟨⟨rfl, -⟩, -⟩ := placed
      -- `simp` closes this through Nat's LawfulBEq instance, which depends on Classical.choice.
      rw [List.findIdx?_cons, show ∀ same : Nat, (same == same) = true from Nat.beq_refl]
      rfl
    | succ position =>
      simp only [List.drop_succ_cons] at placed
      have later := keysAscend_bound tail (first + 1) ascending.2 (key, value)
        (List.mem_of_mem_drop (placed ▸ List.mem_cons_self))
      rw [List.findIdx?_cons, ih ascending.2 placed]
      simp only [beq_iff_eq]
      split
      · omega
      · rfl

#print axioms findIdx?_of_keysAscend

/-- No entry of an ascending table has a key strictly between the key at `position` and the
    next one. -/
theorem findIdx?_none_after {α : Type} {entries rest : List (Nat × α)}
    {lower position previous key : Nat} {value : α}
    (ascending : keysAscend lower entries = true)
    (placed : entries.drop position = (previous, value) :: rest) (below : previous < key)
    (above : (rest.head?.all fun entry => decide (key < entry.1)) = true) :
    entries.findIdx? (fun entry => entry.1 == key) = none := by
  induction entries generalizing lower position with
  | nil => simp at placed
  | cons head tail ih =>
    obtain ⟨first, other⟩ := head
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    cases position with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq, Prod.mk.injEq] at placed
      obtain ⟨⟨rfl, -⟩, rfl⟩ := placed
      have beyond := keysAscend_raise (higher := key + 1) ascending.2 (by
        cases tail with
        | nil => rfl
        | cons next _ =>
          simp only [List.head?_cons, Option.all_some, decide_eq_true_eq] at above ⊢
          omega)
      rw [List.findIdx?_cons, findIdx?_none_of_keysAscend beyond (Nat.lt_succ_self key)]
      simp only [beq_iff_eq]
      split
      · omega
      · rfl
    | succ position =>
      simp only [List.drop_succ_cons] at placed
      have later := keysAscend_bound tail (first + 1) ascending.2 (previous, value)
        (List.mem_of_mem_drop (placed ▸ List.mem_cons_self))
      rw [List.findIdx?_cons, ih ascending.2 placed]
      simp only [beq_iff_eq]
      split
      · omega
      · rfl

#print axioms findIdx?_none_after

end Extraction

/-- How a method reads argument `index`: the incoming value narrowed as its declared type
    requires, or the frame slot of the argument's parameter home. -/
inductive ArgumentAccess where
  | value (narrow : Option NarrowKind)
  | home (slot : Nat)
  deriving DecidableEq, Repr

/-- Homes follow the declared local kinds in `parameterHomes` order; an argument without a home
    is read from the incoming arguments, narrowed by its declared type (none for `this`). -/
def Method.argumentAccess (body : Method) (index : Nat) : ArgumentAccess :=
  match body.parameterHomes.findIdx? (fun home => home.1 == index) with
  | some position => .home (body.localKinds.length + position)
  | none => .value ((body.declared.argumentType index).bind
      (Extraction.declaredNarrow body.environment.rawLayouts))

/-- An argument without a home is read narrowed as its declared type requires. -/
theorem Method.argumentAccess_value {body : Method} {index : Nat} {type : Extraction.TypeExpr}
    {narrow : Option NarrowKind}
    (unhomed : body.parameterHomes.findIdx? (fun home => home.1 == index) = none)
    (declared : body.declared.argumentType index = some type)
    (narrowed : Extraction.declaredNarrow body.environment.rawLayouts type = narrow) :
    body.argumentAccess index = .value narrow := by
  simp [Method.argumentAccess, unhomed, declared, narrowed]

#print axioms Method.argumentAccess_value

/-- An argument without a home or a declared type, such as `this`, is read as it is. -/
theorem Method.argumentAccess_undeclared {body : Method} {index : Nat}
    (unhomed : body.parameterHomes.findIdx? (fun home => home.1 == index) = none)
    (declared : body.declared.argumentType index = none) :
    body.argumentAccess index = .value none := by
  simp [Method.argumentAccess, unhomed, declared]

#print axioms Method.argumentAccess_undeclared

/-- A method with no parameter homes and no declared receiver or parameters reads every argument
    as it is; one proof serves every index. -/
theorem Method.argumentAccess_plain {body : Method} (index : Nat)
    (homes : body.parameterHomes = []) (parameters : body.declared.parameters = [])
    (receiver : body.declared.receiver = none) : body.argumentAccess index = .value none := by
  simp [Method.argumentAccess, homes, DeclaredSignature.argumentType, parameters, receiver]

#print axioms Method.argumentAccess_plain

/-- A homed argument is read from its home's slot, after the declared locals. -/
theorem Method.argumentAccess_home {body : Method} {index position slot : Nat}
    (homed : body.parameterHomes.findIdx? (fun home => home.1 == index) = some position)
    (placed : body.localKinds.length + position = slot) :
    body.argumentAccess index = .home slot := by
  simp [Method.argumentAccess, homed, placed]

#print axioms Method.argumentAccess_home

/-- Two methods with the same homes, local count, signature and layouts read every argument
    alike. -/
theorem Method.argumentAccess_congr {expected actual : Method}
    (homes : actual.parameterHomes = expected.parameterHomes)
    (localCount : actual.localKinds.length = expected.localKinds.length)
    (declared : actual.declared = expected.declared)
    (environment : actual.environment = expected.environment) :
    actual.argumentAccess = expected.argumentAccess := by
  funext index
  simp only [Method.argumentAccess, homes, localCount, declared, environment]

#print axioms Method.argumentAccess_congr

/-- Parameter `index` of a static method is argument `index`. -/
theorem DeclaredSignature.argumentType_static {signature : DeclaredSignature} {index : Nat}
    {type : Extraction.TypeExpr} (static : signature.receiver = none)
    (found : signature.parameters[index]? = some type) :
    signature.argumentType index = some type := by
  simp [DeclaredSignature.argumentType, static, found]

#print axioms DeclaredSignature.argumentType_static

/-- Parameter `index` of an instance method is argument `index + 1`. -/
theorem DeclaredSignature.argumentType_instance {signature : DeclaredSignature} {index : Nat}
    {receiver : Receiver} {type : Extraction.TypeExpr}
    (instanceMethod : signature.receiver = some receiver)
    (found : signature.parameters[index]? = some type) :
    signature.argumentType (index + 1) = some type := by
  simp [DeclaredSignature.argumentType, instanceMethod, found]

#print axioms DeclaredSignature.argumentType_instance

/-- Argument 0 of an instance method, `this`, has no declared parameter type. -/
theorem DeclaredSignature.argumentType_this {signature : DeclaredSignature} {receiver : Receiver}
    (instanceMethod : signature.receiver = some receiver) : signature.argumentType 0 = none := by
  simp [DeclaredSignature.argumentType, instanceMethod]

#print axioms DeclaredSignature.argumentType_this

namespace Extraction

/-- A list an option-valued function maps entirely has as many results as inputs. -/
private theorem length_of_mapM {α β : Type} {inputs : List α} {outputs : List β}
    {make : α → Option β} (made : inputs.mapM make = some outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp_all
  | cons input rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at made
    obtain ⟨_, -, others, remaining, rfl⟩ := made
    simp [ih remaining]

#print axioms length_of_mapM

/-- Searching the expected homes for an argument searches the required home indices. -/
theorem homeKeys_findIdx? {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {homes : List (Nat × LocalKind)} {index : Nat}
    (expected : expectedHomes layouts raw reachable = some homes) :
    homes.findIdx? (fun home => home.1 == index) =
      (requiredHomeIndices raw reachable).findIdx? (· == index) := by
  unfold expectedHomes at expected
  generalize requiredHomeIndices raw reachable = indices at expected ⊢
  induction indices generalizing homes with
  | nil => simp_all
  | cons key rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_some_iff, bind, pure, Option.some.injEq]
      at expected
    obtain ⟨entry, made, others, remaining, rfl⟩ := expected
    obtain ⟨_, -, _, -, rfl⟩ := made
    simp [List.findIdx?_cons, ih remaining]

#print axioms homeKeys_findIdx?

/-- Under `ParameterHomesValid`, a homed argument is read from the slot the argument check
    expects of it: the raw locals' count plus its position among the required homes. -/
theorem argumentAccess_of_homed {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {method : Method} {index : Nat}
    (valid : ParameterHomesValid layouts raw reachable method)
    (homed : index ∈ requiredHomeIndices raw reachable) :
    method.argumentAccess index =
      .home (raw.locals.length + (requiredHomeIndices raw reachable).idxOf index) := by
  obtain ⟨-, -, kinds, -, homes, -⟩ := valid
  apply Method.argumentAccess_home (position := (requiredHomeIndices raw reachable).idxOf index)
  · rw [homeKeys_findIdx? homes]
    cases found : (requiredHomeIndices raw reachable).findIdx? (· == index) with
    | none =>
      rw [List.findIdx?_eq_none_iff] at found
      simp at found
      exact absurd rfl (found index homed)
    | some position =>
      show some position = some (List.findIdx (· == index) (requiredHomeIndices raw reachable))
      rw [List.findIdx_eq_getD_findIdx?, found]
      rfl
  · rw [length_of_mapM kinds]

#print axioms argumentAccess_of_homed

end Extraction

end CIL
