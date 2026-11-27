import CIL.Safety.Execution

/-!
# Static readonly values

A `static readonly` integer, enum or struct field set once by its static constructor loads
as a constant. The extractor records the literal, call or construction with constant arguments
that produced the value. `StaticValuesValid` checks literal storage or reruns the initializer in the
interpreter from empty memory and requires exactly the emitted bytes. An opaque value has no
initializer and zero placeholder bytes: loads read it from the caller's memory, so a proof holds
for every value it may take. See the static-value section of `docs/SOUNDNESS.md` for what stays
trusted.
-/

namespace CIL.Extraction

/-- Initializers run from this memory: no allocations, views or loaded fields. -/
def initializerMemory : Safety.Memory where
  allocations := fun _ => none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 0

/-- Initializers are generous bounded runs; exhausting this fuel fails the certificate. -/
def initializerFuel : Nat := 65536

/-- Constructor-fixed sites removed, so no initializer can read a value it justifies. -/
def withoutStaticValues (program : Program) : Program :=
  program.map fun body =>
    { body with staticSites := body.staticSites.filter (·.2.initializer.isNone) }

/-- A stored integer truncates to its field width; aggregate initializers preserve every byte. -/
def staticStoredBytes (descriptor : StaticDescriptor) (value : Value) : Option (List (BitVec 8)) :=
  match descriptor.scalar, value with
  | none, .aggregate bytes => some bytes
  | some _, .i32 word =>
    if descriptor.bytes.length ∈ [1, 2, 4] then
      some (Safety.numberBytes word.toNat descriptor.bytes.length) else none
  | some _, .i64 word =>
    if descriptor.bytes.length == 8 then some (Safety.numberBytes word.toNat 8) else none
  | _, _ => none

/-- Scalar storage has the width and extension of its field. An aggregate has no scalar flag. -/
def staticStorageMatches (type : TypeExpr) (descriptor : StaticDescriptor) : Bool :=
  match objectFieldShape type with
  | some (width, signed) => descriptor.bytes.length == width && descriptor.scalar == some signed
  | none => !(type matches .enum ..) && descriptor.scalar.isNone

/-- Run constructors through the ordinary checked aggregate-construction operation. -/
def constructorYields (program : Program) (descriptor : StaticDescriptor)
    (init : StaticInitializer) : Bool := Id.run do
  let some body := program[init.method]? | return false
  if descriptor.scalar.isSome || body.returnsValue then return false
  if size : descriptor.bytes.length < 2^64 then
    let wrapper : Method := {
      profile := body.profile
      code := (List.range init.arguments.length).map (fun index => .ldarg index) ++
        [.newobj (.arity init.arguments.length), .ret]
      locals := []
      links := [(init.arguments.length, .aggregate init.method ⟨descriptor.bytes.length, size⟩)]
      returnsValue := true }
    match Safety.invoke (program ++ [wrapper]) initializerFuel program.length
        (init.arguments.map .scalar) initializerMemory with
    | .ok (_, [.scalar value]) => return staticStoredBytes descriptor value == some descriptor.bytes
    | _ => return false
  else return false

/-- Initializers reproduce exactly the descriptor's bytes; RVA descriptors have none. An opaque
    scalar has no initializer and only zero bytes, so no value can be pinned through it. -/
private def initializerYieldsIn (stripped : Thunk Program) (descriptor : StaticDescriptor) : Bool :=
  if descriptor.opaqueValue then
    descriptor.initializer.isNone && descriptor.scalar.isSome && descriptor.bytes.all (· == 0)
  else match descriptor.initializer with
  | none => true
  | some init =>
    match init.literal with
    | some value => !init.construct && init.method == 0 && init.arguments.isEmpty &&
        descriptor.scalar.isSome &&
        staticStoredBytes descriptor value == some descriptor.bytes
    | none => if init.construct then constructorYields stripped.get descriptor init
      else match Safety.invoke stripped.get initializerFuel init.method
        (init.arguments.map .scalar) initializerMemory with
      | .ok (_, [.scalar value]) => staticStoredBytes descriptor value == some descriptor.bytes
      | _ => false

/-- Whether a single descriptor is valid with all constructor-fixed sites removed from execution. -/
def initializerYields (program : Program) (descriptor : StaticDescriptor) : Bool :=
  initializerYieldsIn (Thunk.mk fun _ => withoutStaticValues program) descriptor

/-- All sites of a static identity agree on the full descriptor, and its initializer reproduces
    its bytes. Initializers share a program without constructor-fixed sites. -/
def StaticValuesValid (program : Program) : Prop :=
  let stripped := Thunk.mk fun _ => withoutStaticValues program
  let checked := program.foldlM (init := (∅ : Std.TreeMap Nat StaticDescriptor)) fun seen body =>
    body.staticSites.foldlM (init := seen) fun seen (_, descriptor) => do
      match seen.get? descriptor.identity with
      | some previous =>
        guard (previous = descriptor)
        return seen
      | none =>
        guard (initializerYieldsIn stripped descriptor)
        return seen.insert descriptor.identity descriptor
  (checked : Option (Std.TreeMap Nat StaticDescriptor)).isSome = true

instance (program : Program) : Decidable (StaticValuesValid program) :=
  inferInstanceAs (Decidable (_ = _))

end CIL.Extraction
