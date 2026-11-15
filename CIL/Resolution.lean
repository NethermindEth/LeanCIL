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

`CIL.Method.elementShape` says how an array of a declared element type holds its elements: inline
values of a primitive, an enum, a vector or a struct of the size its checked layout gives, class
references, or method-table entries of one managed signature; a by-ref-like struct has no shape.
The primitive, enum and class lemmas state a shape without evaluating a type name, and the struct
lemmas take the layout entries as premises, so a generated fact reads them through named suffixes.

`CIL.LayoutEnvironment.fieldShape` says how `ldfld`, `stfld` and `ldflda` of a field operand
reach memory: a value-type field through its checked layout entry, a class instance field through
its model slot. `CIL.LayoutEnvironment.valueShape` says the same of a type operand of `ldobj`,
`stobj`, `initobj`, `cpobj` and `sizeof`. Both read only the layouts every method of an
extraction shares, so one fact per distinct operand serves every method.
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

/-! ## Array element shapes -/

/-- How an array of one element type holds its elements: reference-free values of an exact
    element identity and width, class references, or method-table entries of one managed
    signature. Every other element type is `unsupported`, with the reason. -/
inductive ElementShape where
  /-- Inline values: a primitive, an enum over its underlying integer type, an integer vector or
      a struct of the size its checked layout gives. -/
  | value (element : ArrayElement)
  /-- References to instances of the class `element`. -/
  | reference (element : Extraction.TypeExpr)
  /-- Method-table entries: managed method pointers of `signature`. -/
  | method (signature : ManagedSignature)
  /-- An element type no array of the model holds. -/
  | unsupported (reason : String)
  deriving DecidableEq, Repr

namespace ElementShape

/-- Why a struct element without an entry in the checked layouts has no shape. -/
def outsideLayouts : String := "Array element outside the checked layouts"

/-- Why a by-ref-like struct element has no shape: no heap array holds one. -/
def byRefLikeElement : String := "By-ref-like array element"

/-- Why any other element type without array storage has no shape. -/
def unsupportedType : String := "Array element type"

end ElementShape

/-- The shape of an array element of declared type `type`: a class reference for a class, the
    size the checked layout gives for a struct that the raw layouts hold under its identity and
    that is not by-ref-like, the managed signature of a function pointer whose struct parameters
    the raw layouts bind, and the storage `arrayElementType` gives for every other type. -/
def LayoutEnvironment.elementShape (environment : LayoutEnvironment)
    (type : Extraction.TypeExpr) : ElementShape :=
  match type with
  | .object .. => .reference type
  | .aggregate identity index =>
    match environment.rawLayouts[index]? with
    | none => .unsupported ElementShape.outsideLayouts
    | some metadata =>
      if metadata.identity ≠ identity then .unsupported ElementShape.outsideLayouts
      else if metadata.byRefLike then .unsupported ElementShape.byRefLikeElement
      else match environment.layouts[index]? with
        | some layout => .value (.aggregate identity layout.layout.size)
        | none => .unsupported ElementShape.outsideLayouts
  | _ => match Extraction.managedSignature type with
    | some signature =>
      if Extraction.callableLayoutsValid environment.rawLayouts type then .method signature
      else .unsupported ElementShape.outsideLayouts
    | none => match Extraction.arrayElementType type with
      | some element => .value element
      | none => .unsupported ElementShape.unsupportedType

/-- The shape of an array element of declared type `type` in the method's layouts. -/
def Method.elementShape (body : Method) (type : Extraction.TypeExpr) : ElementShape :=
  body.environment.elementShape type

/-- The shape of an array of the primitive: its own storage, and none for floating point. -/
def PrimitiveType.elementShape : PrimitiveType → ElementShape
  | .sbyte => .value .signed8 | .byte => .value .unsigned8 | .boolean => .value .boolean
  | .int16 => .value .signed16 | .uint16 => .value .unsigned16 | .char => .value .character
  | .int32 => .value .signed32 | .uint32 => .value .unsigned32
  | .int64 => .value .signed64 | .uint64 => .value .unsigned64
  | .intPtr => .value .nativeInt | .uintPtr => .value .nativeUInt
  | .single | .double => .unsupported ElementShape.unsupportedType

/-- The storage of an enum over the primitive; `none` where `typeStorage` admits no enum. -/
def PrimitiveType.enumStorage : PrimitiveType → Option EnumStorage
  | .sbyte => some .signed8 | .byte => some .unsigned8
  | .int16 => some .signed16 | .uint16 => some .unsigned16
  | .int32 => some .signed32 | .uint32 => some .unsigned32
  | .int64 => some .signed64 | .uint64 => some .unsigned64
  | .boolean | .char | .single | .double | .intPtr | .uintPtr => none

/-- The shape of an array of the enum `identity` over the primitive. -/
def PrimitiveType.enumElementShape (identity : String) (type : PrimitiveType) : ElementShape :=
  match type.enumStorage with
  | some storage => .value (.enumeration identity storage)
  | none => .unsupported ElementShape.unsupportedType

/-- An array of a primitive holds the primitive's storage, whatever the layouts. -/
theorem Method.elementShape_primitive (body : Method) (type : PrimitiveType) :
    body.elementShape type.typeExpr = type.elementShape := by
  cases type <;> rfl

#print axioms Method.elementShape_primitive

/-- An array of an enum over a primitive holds the enum's storage where `typeStorage` admits
    the primitive as an enum's underlying type, whatever the layouts. -/
theorem Method.elementShape_enum (body : Method) (identity : String) (type : PrimitiveType) :
    body.elementShape (.enum identity type.typeExpr) = type.enumElementShape identity := by
  cases type <;> rfl

#print axioms Method.elementShape_enum

/-- An array of a class holds references to its instances. -/
theorem Method.elementShape_object (body : Method) (scope name : String) :
    body.elementShape (.object scope name) = .reference (.object scope name) := rfl

#print axioms Method.elementShape_object

/-- An array of a struct the raw layouts hold under its identity, and that is not by-ref-like,
    holds values of the size its checked layout gives. -/
theorem Method.elementShape_aggregate {body : Method} {identity : String} {index : Nat}
    {metadata : Extraction.RawLayout} {layout : Extraction.ComputedLayout}
    (declared : body.environment.rawLayouts[index]? = some metadata)
    (identified : metadata.identity = identity) (inline : metadata.byRefLike = false)
    (computed : body.environment.layouts.toList[index]? = some layout) :
    body.elementShape (.aggregate identity index) =
      .value (.aggregate identity layout.layout.size) := by
  rw [Array.getElem?_toList] at computed
  simp [Method.elementShape, LayoutEnvironment.elementShape, declared, identified, inline,
    computed]

#print axioms Method.elementShape_aggregate

/-- An array of a by-ref-like struct has no shape: no heap array holds one. -/
theorem Method.elementShape_byRefLike {body : Method} {identity : String} {index : Nat}
    {metadata : Extraction.RawLayout}
    (declared : body.environment.rawLayouts[index]? = some metadata)
    (identified : metadata.identity = identity) (byRefLike : metadata.byRefLike = true) :
    body.elementShape (.aggregate identity index) =
      .unsupported ElementShape.byRefLikeElement := by
  simp [Method.elementShape, LayoutEnvironment.elementShape, declared, identified, byRefLike]

#print axioms Method.elementShape_byRefLike

/-! ## Field and value shapes -/

namespace Extraction

/-- The width and sign extension of a class instance field of `type`: integer, Boolean, Char
    and enum fields only, each fitting one `objectFieldSlot`. -/
def objectFieldShape (type : TypeExpr) : Option (Nat × Bool) :=
  match typeStorage [] type with
  | some (.field kind) => (primitiveFieldWidth kind).map fun width => (width, signedField kind)
  | _ => none

/-- A class instance field whose slot holds an object reference: one typed as an admitted class
    or as an array of one, which is itself an object on the heap. -/
def referenceFieldType : TypeExpr → Bool
  | .object _ _ | .array (.object _ _) => true
  | _ => false

/-- The element of a class instance field typed as an array of a value type, as the evaluation
    stack records it: a struct element by its identity alone. -/
def valueArrayFieldElement (type : TypeExpr) : Option ArrayElement :=
  match type with
  | .array element => arrayElementType element
  | _ => none

end Extraction

/-- What the model keeps in a class instance field's 8-byte slot. -/
inductive ClassSlot where
  /-- An integer, Boolean, Char or enum of `width` bytes, sign-extended when `signed`. -/
  | word (width : Nat) (signed : Bool)
  /-- An object reference: a class or an array of a class. -/
  | reference
  /-- A reference to an array of the value type `element`. -/
  | array (element : ArrayElement)
  deriving DecidableEq, Repr

/-- How `ldfld`, `stfld` and `ldflda` of one field operand reach memory. -/
inductive FieldShape where
  /-- A primitive or vector field of a value type: `width` bytes at byte `offset` of the
      owner, sign-extended on load when `signed`. -/
  | value (offset width : Nat) (signed : Bool)
  /-- A nested struct field of a value type: `size` bytes at byte `offset` of the owner. -/
  | aggregate (offset size : Nat)
  /-- A class instance field at model offset `offset`; its address is never formed. -/
  | classSlot (offset : Nat) (slot : ClassSlot)
  /-- A field outside the checked layouts and class slots; an access faults with `reason`. -/
  | unsupported (reason : String)
  deriving DecidableEq, Repr

/-- The shape of a value-type field with checked layout entry `layout`, sign-extended on load
    when `signed`. -/
def FieldShape.ofLayout (layout : FieldLayout) (signed : Bool) : FieldShape :=
  if layout.aggregate then .aggregate layout.offset layout.width
  else .value layout.offset layout.width signed

/-- The slot of a class instance field typed `type`, apart from the size of a struct array
    element, which only the environment's layouts know. -/
def classSlotOf (type : Extraction.TypeExpr) : Option ClassSlot :=
  match Extraction.objectFieldShape type with
  | some (width, signed) => some (.word width signed)
  | none =>
    if Extraction.referenceFieldType type then some .reference
    else (Extraction.valueArrayFieldElement type).map .array

/-- The slot of a class instance field typed `type`. A struct array element is an admitted
    struct that is not byref-like, sized by its checked layout. -/
def LayoutEnvironment.classSlot (environment : LayoutEnvironment) (type : Extraction.TypeExpr) :
    Option ClassSlot :=
  match type with
  | .array (.aggregate identity index) => do
    let .aggregateArray .. ← Extraction.typeStorage environment.rawLayouts type | none
    let layout ← environment.layouts[index]?
    return .array (.aggregate identity layout.layout.size)
  | _ => classSlotOf type

/-- The checked layout entry of field `index` of the struct at layout `parent`, with whether a
    load sign-extends it; `none` unless the field is declared with the storage `held` decodes to.
-/
def LayoutEnvironment.structField? (environment : LayoutEnvironment) (parent index : Nat)
    (held : Extraction.TypeExpr) : Option (FieldLayout × Bool) := do
  let metadata ← environment.rawLayouts[parent]?
  let declared ← metadata.fields[index]?
  if Extraction.typeStorage environment.rawLayouts held !=
      some (Extraction.declaredFieldStorage declared.type) then none else pure ()
  let layout ← environment.layouts[parent]?
  let computed ← layout.layout.fields[index]?
  return (computed, Extraction.signedField declared.type)

/-- How an access to `field` reaches memory. A class owner's field is the slot at the model
    offset of its index; a value-type owner's field is its checked layout entry when the operand
    holds the field's declared type; a field of any other owner is unsupported. -/
def LayoutEnvironment.fieldShape (environment : LayoutEnvironment)
    (field : Extraction.FieldRef) : FieldShape :=
  match field.owner with
  | .object _ _ => match environment.classSlot field.type with
    | some slot => .classSlot (objectFieldOffset field.index) slot
    | none => .unsupported "Class instance field type"
  | owner => match Extraction.typeStorage environment.rawLayouts owner with
    | some (.field (.aggregate parent)) =>
      match environment.structField? parent field.index field.type with
      | some (computed, signed) => FieldShape.ofLayout computed signed
      | none => .unsupported "Field outside the checked layouts"
    | _ => .unsupported "Field owner is not a value type"

/-- How `ldobj`, `stobj`, `initobj`, `cpobj` and `sizeof` of one type operand reach memory. -/
inductive ValueShape where
  /-- A primitive integer, Boolean, Char or enum of `width` bytes, sign-extended on load when
      `signed`. -/
  | primitive (width : Nat) (signed : Bool)
  /-- A struct of `size` bytes. -/
  | aggregate (size : Nat)
  /-- A vector of `width` bytes. -/
  | vector (width : Nat)
  /-- A span, whose address on the stack is already the view it names. -/
  | span
  /-- A type outside the checked layouts and primitives; an access faults with `reason`. -/
  | unsupported (reason : String)
  deriving DecidableEq, Repr

/-- How a value of `type` reaches memory: as a span, a vector of its width, a struct sized by its
    checked layout or a primitive of its width. -/
def LayoutEnvironment.valueShape (environment : LayoutEnvironment)
    (type : Extraction.TypeExpr) : ValueShape :=
  if Extraction.spanLocal type then .span else
  match Extraction.integerVectorWidth type with
  | some width => .vector width
  | none => match Extraction.typeStorage environment.rawLayouts type with
    | some (.field (.aggregate index)) => match environment.layouts[index]? with
      | some layout => .aggregate layout.layout.size
      | none => .unsupported "Value type outside the checked layouts"
    | some (.field kind) => match Extraction.primitiveFieldWidth kind with
      | some width => .primitive width (Extraction.signedField kind)
      | none => .unsupported "Value type without a width"
    | some .vector128 => .vector 16
    | some .vector256 => .vector 32
    | some .vector512 => .vector 64
    | _ => .unsupported "Not a value type"

/-- The bytes a value of the shape occupies; `none` for a span and an unsupported type. -/
def ValueShape.size? : ValueShape → Option Nat
  | .primitive width _ | .vector width => some width
  | .aggregate size => some size
  | _ => none

/-- How an access to `field` in `body` reaches memory, from the program-wide layouts. -/
def Method.fieldShape (body : Method) (field : Extraction.FieldRef) : FieldShape :=
  body.environment.fieldShape field

/-- How a value of `type` in `body` reaches memory, from the program-wide layouts. -/
def Method.valueShape (body : Method) (type : Extraction.TypeExpr) : ValueShape :=
  body.environment.valueShape type

/-- A class slot sits at the model offset of the field's index, and only a class owner has one,
    so a view naming a field by owner and offset agrees with the step that resolves it. -/
theorem LayoutEnvironment.fieldShape_class_offset {environment : LayoutEnvironment}
    {field : Extraction.FieldRef} {offset : Nat} {slot : ClassSlot}
    (shape : environment.fieldShape field = .classSlot offset slot) :
    offset = objectFieldOffset field.index ∧ ∃ scope name, field.owner = .object scope name := by
  unfold LayoutEnvironment.fieldShape at shape
  split at shape
  · next scope name owned =>
    split at shape
    · simp only [FieldShape.classSlot.injEq] at shape
      exact ⟨shape.1.symm, scope, name, owned⟩
    · cases shape
  · split at shape
    · split at shape
      · unfold FieldShape.ofLayout at shape
        split at shape <;> cases shape
      · cases shape
    · cases shape

#print axioms LayoutEnvironment.fieldShape_class_offset

/-- A field of a class owner whose type has a slot resolves to that slot at the model offset of
    its index. -/
theorem LayoutEnvironment.fieldShape_class {environment : LayoutEnvironment}
    {field : Extraction.FieldRef} {scope name : String} {slot : ClassSlot}
    (owner : field.owner = .object scope name)
    (typed : environment.classSlot field.type = some slot) :
    environment.fieldShape field = .classSlot (objectFieldOffset field.index) slot := by
  simp [LayoutEnvironment.fieldShape, owner, typed]

#print axioms LayoutEnvironment.fieldShape_class

/-- A field of a struct owner resolves to its checked layout entry. -/
theorem LayoutEnvironment.fieldShape_struct {environment : LayoutEnvironment}
    {field : Extraction.FieldRef} {parent : Nat} {computed : FieldLayout} {signed : Bool}
    (owner : Extraction.typeStorage environment.rawLayouts field.owner =
      some (.field (.aggregate parent)))
    (found : environment.structField? parent field.index field.type = some (computed, signed)) :
    environment.fieldShape field = FieldShape.ofLayout computed signed := by
  unfold LayoutEnvironment.fieldShape
  split
  · next scope name owned => simp [owned, Extraction.typeStorage] at owner
  · simp [owner, found]

#print axioms LayoutEnvironment.fieldShape_struct

/-- A method resolves a field as the environment it shares does. -/
theorem Method.fieldShape_of_environment {body : Method} {environment : LayoutEnvironment}
    {field : Extraction.FieldRef} {shape : FieldShape} (shared : body.environment = environment)
    (resolved : environment.fieldShape field = shape) : body.fieldShape field = shape := by
  rw [Method.fieldShape, shared, resolved]

#print axioms Method.fieldShape_of_environment

/-- A method resolves a value type as the environment it shares does. -/
theorem Method.valueShape_of_environment {body : Method} {environment : LayoutEnvironment}
    {type : Extraction.TypeExpr} {shape : ValueShape} (shared : body.environment = environment)
    (resolved : environment.valueShape type = shape) : body.valueShape type = shape := by
  rw [Method.valueShape, shared, resolved]

#print axioms Method.valueShape_of_environment

/-! ### Shapes from one layout entry

Each lemma reads the layouts only through the entries it names, so a fact built from them never
has the kernel walk the layout lists to an index; the entries come from named suffixes. -/

/-- A struct type decodes to the field storage of its index when the layout there carries its
    identity. -/
theorem Extraction.typeStorage_aggregate {layouts : List Extraction.RawLayout}
    {metadata : Extraction.RawLayout} {identity : String} {index : Nat}
    (found : layouts[index]? = some metadata) (named : metadata.identity = identity) :
    Extraction.typeStorage layouts (.aggregate identity index) =
      some (.field (.aggregate index)) := by
  simp only [Extraction.typeStorage]
  rw [found]
  dsimp only [bind, Option.bind]
  simp only [named, ite_true, eq_self, pure]

#print axioms Extraction.typeStorage_aggregate

/-- An array of a struct decodes to an array of that struct's layout when the layout at its
    index carries its identity and is not byref-like. -/
theorem Extraction.typeStorage_aggregateArray {layouts : List Extraction.RawLayout}
    {metadata : Extraction.RawLayout} {identity : String} {index : Nat}
    (found : layouts[index]? = some metadata)
    (admitted : (metadata.identity == identity && !metadata.byRefLike) = true) :
    Extraction.typeStorage layouts (.array (.aggregate identity index)) =
      some (.aggregateArray identity index) := by
  simp only [Extraction.typeStorage]
  rw [found]
  dsimp only [bind, Option.bind]
  simp only [admitted, ite_true]

#print axioms Extraction.typeStorage_aggregateArray

/-- Field `index` of the struct at `parent` is its checked entry when its declared storage is
    the storage of `held`. -/
theorem LayoutEnvironment.structField?_eq {environment : LayoutEnvironment}
    {parent index : Nat} {held : Extraction.TypeExpr} {metadata : Extraction.RawLayout}
    {declared : Extraction.RawField} {layout : Extraction.ComputedLayout} {computed : FieldLayout}
    (raw : environment.rawLayouts[parent]? = some metadata)
    (field : metadata.fields[index]? = some declared)
    (storage : Extraction.typeStorage environment.rawLayouts held =
      some (Extraction.declaredFieldStorage declared.type))
    (checked : environment.layouts.toList[parent]? = some layout)
    (entry : layout.layout.fields[index]? = some computed) :
    environment.structField? parent index held =
      some (computed, Extraction.signedField declared.type) := by
  rw [Array.getElem?_toList] at checked
  unfold LayoutEnvironment.structField?
  rw [raw]
  dsimp only [bind, Option.bind]
  rw [field]
  dsimp only [bind, Option.bind]
  rw [storage, bne_self_eq_false]
  dsimp only [bind, Option.bind, Bool.false_eq_true, ↓reduceIte, pure]
  rw [checked]
  dsimp only [bind, Option.bind]
  rw [entry]
  rfl

#print axioms LayoutEnvironment.structField?_eq

/-- A class field holding an array of an admitted struct has that struct's checked size. -/
theorem LayoutEnvironment.classSlot_aggregateArray {environment : LayoutEnvironment}
    {identity : String} {index : Nat} {layout : Extraction.ComputedLayout}
    (storage : Extraction.typeStorage environment.rawLayouts (.array (.aggregate identity index)) =
      some (.aggregateArray identity index))
    (checked : environment.layouts.toList[index]? = some layout) :
    environment.classSlot (.array (.aggregate identity index)) =
      some (.array (.aggregate identity layout.layout.size)) := by
  rw [Array.getElem?_toList] at checked
  unfold LayoutEnvironment.classSlot
  rw [storage]
  dsimp only [bind, Option.bind]
  rw [checked]
  rfl

#print axioms LayoutEnvironment.classSlot_aggregateArray

/-- A struct type that is neither a span nor a vector has its checked size. -/
theorem LayoutEnvironment.valueShape_aggregate {environment : LayoutEnvironment}
    {type : Extraction.TypeExpr} {index : Nat} {layout : Extraction.ComputedLayout}
    (notSpan : Extraction.spanLocal type = false)
    (notVector : Extraction.integerVectorWidth type = none)
    (storage : Extraction.typeStorage environment.rawLayouts type =
      some (.field (.aggregate index)))
    (checked : environment.layouts.toList[index]? = some layout) :
    environment.valueShape type = .aggregate layout.layout.size := by
  rw [Array.getElem?_toList] at checked
  simp [LayoutEnvironment.valueShape, notSpan, notVector, storage, checked]

#print axioms LayoutEnvironment.valueShape_aggregate

end CIL
