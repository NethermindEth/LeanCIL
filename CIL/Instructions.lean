import CIL.Types
import CIL.IntegerArithmetic
import CIL.Features
import CIL.SIMD.Availability
import CIL.VectorMemory
import CIL.MethodPointers
import CIL.CallSite
import CIL.Extraction.Layout

/-!
# Instructions and methods

`Instruction` is the instruction set the extractor emits; `Method` is one extracted method body
and `Program` the list a call index refers into.
-/

namespace CIL

/-- Small integer storage types; all extend to the 32-bit evaluation-stack type. -/
inductive NarrowKind where
  | signed8 | unsigned8 | signed16 | unsigned16
  deriving DecidableEq, Repr

/-- Storage size in bytes. -/
def NarrowKind.width : NarrowKind → Nat
  | .signed8 | .unsigned8 => 1
  | .signed16 | .unsigned16 => 2

@[simp] theorem NarrowKind.width_lt (kind : NarrowKind) : kind.width < 2^64 := by
  cases kind <;> decide

/-- Truncates to the storage width, then sign- or zero-extends back to 32 bits. -/
def NarrowKind.extend (kind : NarrowKind) (bits : W32) : W32 :=
  match kind with
  | .signed8 => (bits.setWidth 8).signExtend 32
  | .unsigned8 => (bits.setWidth 8).zeroExtend 32
  | .signed16 => (bits.setWidth 16).signExtend 32
  | .unsigned16 => (bits.setWidth 16).zeroExtend 32

/-- A boolean result already fits every narrow kind, so a narrowed comparison return is unchanged. -/
theorem NarrowKind.extend_ite_one_zero (kind : NarrowKind) (p : Prop) [Decidable p] :
    kind.extend (if p then 1 else 0) = if p then 1 else 0 := by
  cases kind <;> split <;> rfl

/-- The `1#32`/`0#32` literals comparisons produce are not syntactically `1`/`0`, so simp needs this form too. -/
theorem NarrowKind.extend_ite_ofNat_one_zero (kind : NarrowKind) (p : Prop) [Decidable p] :
    kind.extend (if p then 1#32 else 0#32) = if p then 1#32 else 0#32 := by
  cases kind <;> split <;> rfl

/-- A decided comparison returns the literal `1#32`, which every narrow kind keeps. -/
@[simp] theorem NarrowKind.extend_one (kind : NarrowKind) : kind.extend 1#32 = 1#32 := by
  cases kind <;> rfl

/-- A decided comparison returns the literal `0#32`, which every narrow kind keeps. -/
@[simp] theorem NarrowKind.extend_zero (kind : NarrowKind) : kind.extend 0#32 = 0#32 := by
  cases kind <;> rfl

#print axioms NarrowKind.extend_ite_one_zero
#print axioms NarrowKind.extend_ite_ofNat_one_zero
#print axioms NarrowKind.extend_one
#print axioms NarrowKind.extend_zero

/-- Applies an optional narrowing to an `i32`; narrowing anything else is stuck. -/
def narrowValue (kind : Option NarrowKind) (value : Value) : Option Value :=
  match kind, value with
  | none, value => some value
  | some kind, .i32 bits => some (.i32 (kind.extend bits))
  | _, _ => none

/-- Physical local storage, retained even when InitLocals is false. Reference
    slots retain managed-reference values rather than numerical addresses. -/
inductive LocalKind where
  | narrow (kind : NarrowKind)
  | aggregate (size : Fin (2^64))
  /-- A span root stores provenance rather than serializing a managed pointer into bytes. -/
  | span (width : Nat) (writable : Bool)
  /-- A typed array root keeps its shape and reference without encoding object headers. -/
  | array (element : ArrayElement)
  /-- Callable roots retain exact signatures and never expose a numeric byte home. -/
  | methodPointer (signature : ManagedSignature)
  | methodTable (signature : ManagedSignature)
  /-- An object reference root holds a heap identity, never bytes. -/
  | object
  | byte | word32 | word64 | vector128 | vector256 | vector512 | reference
  deriving DecidableEq, Repr

/-- Constructors that initialize a typed span local without exposing its storage address. -/
inductive SpanConstructor where
  | empty (width : Nat) (writable : Bool)
  | array (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  | reference (width : Nat) (writable : Bool)
  | singleReference (width : Nat) (writable : Bool)
  deriving DecidableEq, Repr

/-- The checked memory operation underlying a span constructor. -/
def SpanConstructor.operation : SpanConstructor → MemoryOp
  | .empty width writable => .spanEmpty width writable
  | .array element writable range => .arraySpan element writable range
  | .reference width writable => .spanFromReference width writable
  | .singleReference width writable => .spanSingleReference width writable

/-- One instruction. Branch targets and call indices are positions in the method's code
    and in the `Program`. Constructors that `CIL.step` does not execute are handled by the
    checked interpreter in `CIL.Safety`. -/
inductive Instruction where
  /-- Widen the int32 operand of a metadata-validated mixed native operation. -/
  | nativeBinary (operation : Instruction)
  | divide (signed remainder : Bool)
  | checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool)
  | checkedConvert (width : Nat) (signed unsignedInput : Bool)
  /-- Dynamic frame storage; the flag is checked against the raw method's localsinit bit. -/
  | stackAlloc (initLocals : Bool)
  /-- Fresh zero-initialized primitive heap storage, assuming runtime allocation availability. -/
  | newArray (element : ArrayElement)
  /-- `newarr` of class `element`: a fresh array of null references on the heap budget. -/
  | newReferenceArray (element : Extraction.TypeExpr)
  | nop | neg | cgt
  -- Signed and unsigned compare-and-branch; more follow `switch` below.
  | bgt (target : Nat)
  | ble (target : Nat)
  | ble_un (target : Nat)
  -- Value-type aggregates and fields, by byte offset and width.
  | loadAggregate (size : Nat)
  | copyObject (size : Nat)
  | storeAggregate (size : Nat)
  | initAggregate (size : Nat)
  | loadScalar (width : Nat) (signed : Bool := false)
  | storeScalar (width : Nat)
  | fieldAt (offset width : Nat) (signed : Bool := false)
  | fieldAddress (offset : Nat)
  | setFieldAt (offset width : Nat)
  | aggregateFieldAt (offset size : Nat)
  | setAggregateFieldAt (offset size : Nat)
  -- Arguments and locals.
  | arg (index : Nat) (narrow : Option NarrowKind := none)
  | local (index : Nat) (narrow : Option NarrowKind := none)
  | localAddr (index : Nat)
  | setLocal (index : Nat) (narrow : Option NarrowKind := none)
  | initializeSpanLocal (index : Nat) (constructor : SpanConstructor)
  /-- Transfer to a managed method after retiring the current activation. -/
  | tailCall (callee argc : Nat)
  /-- Authenticated managed pointers, immutable tables and exact-signature indirect calls. -/
  | managed (operation : ManagedOp)
  -- Constants, conversions, arithmetic, 64-bit memory access and stack shuffling.
  | ldc_i4 (value : W32)
  | ldc_i8 (value : W64)
  | conv_i1 | conv_i2 | conv_u2
  | conv_i8 | conv_i4 | conv_u1 | conv_u4 | conv_u8 | conv_u | not | add | sub | mul | and | or
  | xor | shl | shr | shr_un | clt | clt_un | cgt_un | ceq | load64 | store64 | dup | pop
  -- Control flow.
  | br (target : Nat)
  | switch (targets : List Nat)
  | brfalse (target : Nat)
  | brtrue (target : Nat)
  | blt_un (target : Nat)
  | bge_un (target : Nat)
  | bgt_un (target : Nat)
  | bge (target : Nat)
  | blt (target : Nat)
  | beq (target : Nat)
  | bne_un (target : Nat)
  -- Calls and constructors; `argc` values are popped as arguments.
  | call (method : Nat) (argc : Nat)
  /-- `callvirt` of a non-virtual instance method of a class: a null receiver, the first of the
      `argc` arguments, throws `System.NullReferenceException` before the call. -/
  | callInstance (method : Nat) (argc : Nat)
  /-- `callvirt` of a virtual method of a class: the receiver, the first of the `argc` arguments,
      enters the body `targets` lists for its exact runtime class. A null receiver throws
      `System.NullReferenceException`; a class `targets` omits is a model fault, not a call. -/
  | callVirtual (targets : List (Extraction.TypeExpr × Nat)) (argc : Nat)
  | newAggregate (constructor : Nat) (argc : Nat) (size : Fin (2^64))
  /-- A fresh zeroed instance of class `owner` with `size` bytes of fields, passed to
      `constructor` as its receiver ahead of `argc` arguments and pushed once it returns. -/
  | newObject (constructor : Nat) (argc : Nat) (owner : Extraction.TypeExpr)
      (bases : List Extraction.TypeExpr) (size : Nat)
  /-- `castclass` (`throwing`) or `isinst` of class `type`: an object whose runtime class or one
      of its bases is `type` stays on the stack, as does null; any other object becomes null,
      or throws `System.InvalidCastException` for `castclass`. -/
  | objectTest (type : Extraction.TypeExpr) (throwing : Bool)
  | skipInit
  /-- Pushes `1` when the method's feature profile has the feature, else `0`. -/
  | feature (id : Feature)
  | intrinsic (operation : Intrinsic) (argc : Nat)
  | memory (operation : MemoryOp)
  | ret (narrow : Option NarrowKind := none)
  /-- Raises an exception of the named type; there are no handlers. -/
  | throw (exception : String)
  | unsupported (description : String)
  deriving Repr

/-- The name of the instruction type, for tactics that recognise its constructors. -/
def instructionTypeName : Lean.Name := ``CIL.Instruction

/-- A literal, call or construction whose value a static constructor stores in a readonly field. -/
structure StaticInitializer where
  method : Nat
  arguments : List Value
  /-- A direct integer literal store; no method is called when this is present. -/
  literal : Option Value := none
  /-- Construct a zero-initialized aggregate with this instance constructor. -/
  construct : Bool := false
  deriving DecidableEq, Repr

/-- A static field the method reads: its bytes as extracted, and where they came from. -/
structure StaticDescriptor where
  identity : Nat
  fieldName : String
  bytes : List (BitVec 8)
  /-- `some` for a value fixed by its static constructor, `none` for RVA data. -/
  initializer : Option StaticInitializer := none
  /-- Integer fields use their byte width and this signed-load flag; aggregates use `none`. -/
  scalar : Option Bool := none
  assemblyIdentity : String := ""
  /-- Guaranteed alignment of the field's storage: the declared packing of RVA data, which the
      extractor checked divides the field's RVA. `1` promises nothing beyond byte alignment. -/
  alignment : Nat := 1
  /-- A constructor-fixed value extraction cannot compute. Loads read the caller's static binding
      and fault without one; `bytes` gives only the width and its contents are never read. -/
  opaqueValue : Bool := false
  deriving DecidableEq, Repr

/-- How `this` reaches an instance method: an object reference for a class method, a managed
    reference to the instance for a value-type method. -/
inductive Receiver where
  | object
  | reference
  deriving DecidableEq, Repr

/-- A method's declared signature after its type arguments are closed. Aggregate types refer
    to `LayoutEnvironment.rawLayouts`. -/
structure DeclaredSignature where
  /-- `some` exactly for an instance method. -/
  receiver : Option Receiver := none
  /-- Declared parameter types in order, `this` excluded. -/
  parameters : List Extraction.TypeExpr := []
  returnType : Extraction.TypeExpr := .void
  deriving DecidableEq, Repr

/-- The declared type of argument `index`, counting `this` as argument 0; `none` for `this`. -/
def DeclaredSignature.argumentType (signature : DeclaredSignature) (index : Nat) :
    Option Extraction.TypeExpr :=
  match signature.receiver, index with
  | none, _ => signature.parameters[index]?
  | some _, 0 => none
  | some _, index + 1 => signature.parameters[index]?

/-- Program-wide struct layouts the semantics may read, shared by every method of one
    extraction. -/
structure LayoutEnvironment where
  /-- Raw struct metadata, the input that `LayoutsValid` recomputes layouts from. -/
  rawLayouts : List Extraction.RawLayout := []
  /-- The checked layout table, indexed like `rawLayouts`. -/
  layouts : Array Extraction.ComputedLayout := #[]
  deriving DecidableEq, Repr

/-- Where the call-family instruction at one pc goes. Every entry is checked against the call
    site's metadata; method indices are positions in the `Program`. -/
inductive Link where
  /-- One body: a program method or import slot for `call`, a non-virtual `callvirt`, or the
      implementation a `constrained.` call resolves to. -/
  | direct (method : Nat)
  /-- A virtual `callvirt` of a class slot: the body each exact runtime class enters. -/
  | virtual (targets : List (Extraction.TypeExpr × Nat))
  /-- `newobj` of a value type: its constructor and the instance size from the layout table. -/
  | aggregate (constructor : Nat) (size : Fin (2^64))
  /-- `newobj` of a class: its constructor, admitted bases nearest first, and field bytes. -/
  | object (constructor : Nat) (bases : List Extraction.TypeExpr) (size : Nat)
  /-- `calli`: the bodies a method pointer of the site's signature may name. -/
  | indirect (catalog : List ManagedTarget)
  deriving DecidableEq, Repr

/-- Every method index a link may enter. -/
def Link.callees : Link → List Nat
  | .direct method | .aggregate method _ | .object method _ _ => [method]
  | .virtual targets => targets.map Prod.snd
  | .indirect catalog => catalog.map ManagedTarget.method

/-- The link that an instruction's own program index implies; `none` for instructions that
    enter no method. -/
def Instruction.link? (op : Instruction) : Option Link := by
  -- Built by cases: a catch-all `match` on this type elaborates to a sparse recursor that
  -- depends on `propext`, and every method literal's default link table would inherit it.
  cases op
  case call method _ => exact some (.direct method)
  case callInstance method _ => exact some (.direct method)
  case tailCall method _ => exact some (.direct method)
  case callVirtual targets _ => exact some (.virtual targets)
  case newAggregate method _ size => exact some (.aggregate method size)
  case newObject method _ _ bases size => exact some (.object method bases size)
  case managed operation =>
    cases operation
    case call _ catalog _ => exact some (.indirect catalog)
    all_goals exact none
  all_goals exact none

/-- The link table a code list implies: each linking instruction's pc with its link. The pcs come
    from `List.range`, which the kernel reduces to literals. Numbered by `zipIdx`, each pc would be
    a chain of `+ 1` terms shaped like the pcs `Embeds` reads at, and the kernel would pay a
    chain's length at every read, so an embedding would cost the square of its calls. -/
def linksOfCode (code : List Instruction) : List (Nat × Link) :=
  (code.zip (List.range code.length)).filterMap fun entry =>
    entry.1.link?.map fun link => (entry.2, link)

/-- An extracted method body with the frame layout the interpreter needs. -/
structure Method where
  /-- The hardware features the method was compiled against. -/
  profile : FeatureProfile := FeatureProfile.scalar
  code : List Instruction
  /-- Initial values of the scalar locals. -/
  locals : List Value
  localKinds : List LocalKind := []
  staticSites : List (Nat × StaticDescriptor) := []
  opaqueVectorLocals : List Nat := []
  parameterHomes : List (Nat × LocalKind) := []
  /-- Declared argument and return types; see `DeclaredSignature`. -/
  declared : DeclaredSignature := {}
  /-- Program-wide layouts, the same value for every method of an extraction. -/
  environment : LayoutEnvironment := {}
  /-- Call-family pc to link; the first entry for a pc wins. -/
  links : List (Nat × Link) := linksOfCode code
  returnsValue : Bool
  deriving Repr

/-- The link the first entry of `links` for `query` gives, `none` without one. -/
def linkLookup (links : List (Nat × Link)) (query : Nat) : Option Link :=
  (links.find? fun entry => entry.1 == query).map Prod.snd

/-- The link of the call-family instruction at `pc`, if the table has one; the first entry wins.
    An extracted method states each call site's link as a generated fact, so a proof need not
    evaluate this scan; for any other body the scan runs over its table, which for a body without
    a written `links` is the one its code implies. -/
def Method.linkAt (body : Method) (pc : Nat) : Option Link :=
  linkLookup body.links pc

/-- `method` with new code and the link table that code implies. Static sites are keyed by pc like
    the links, so they are reset to none; a body that reads statics supplies its own after the
    call. The declared signature, the environment and the other fields are kept. A plain
    `{ method with code := ... }` keeps the old table and sites, whose pcs are those of the old
    code. -/
def Method.withCode (method : Method) (code : List Instruction) : Method :=
  { method with code := code, links := linksOfCode code, staticSites := [] }

/-- The implied table, with the code numbered by `zipIdx`. -/
theorem linksOfCode_eq_zipIdx (code : List Instruction) :
    linksOfCode code =
      code.zipIdx.filterMap fun entry => entry.1.link?.map fun link => (entry.2, link) := by
  simp only [linksOfCode, List.zipIdx_eq_zip_range', List.range_eq_range']

#print axioms linksOfCode_eq_zipIdx

/-- Reading the table implied by code that starts at pc `start` gives the code's own link at each
    pc from `start` on, and none before it. -/
theorem linksOfCode_find (code : List Instruction) (start pc : Nat) :
    (((code.zipIdx start).filterMap fun entry =>
        entry.1.link?.map fun link => (entry.2, link)).find? fun entry => entry.1 == pc).map
          Prod.snd = if start ≤ pc then (code[pc - start]?).bind Instruction.link? else none := by
  induction code generalizing start with
  | nil => simp
  | cons op rest ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons]
    by_cases same : start = pc
    · subst same
      cases link : op.link? with
      | none =>
        have none_after : (((rest.zipIdx (start + 1)).filterMap fun entry =>
            entry.1.link?.map fun link => (entry.2, link)).find? fun entry => entry.1 == start) =
              none := by
          have := ih (start + 1)
          simp only [show ¬ (start + 1 ≤ start) by omega, ite_false] at this
          exact Option.map_eq_none_iff.mp this
        simp [link, none_after]
      | some found =>
        have first : (((start, found) :: ((rest.zipIdx (start + 1)).filterMap fun entry =>
            entry.1.link?.map fun link => (entry.2, link))).find? fun entry => entry.1 == start) =
              some (start, found) := List.find?_cons_of_pos (Nat.beq_refl start)
        simp [link, first]
    · have different : ¬ (start == pc) = true := by
        simp only [beq_iff_eq]
        exact same
      cases link : op.link? with
      | none =>
        simp only [Option.map_none]
        rw [ih (start + 1)]
        by_cases later : start + 1 ≤ pc
        · have : pc - start = (pc - (start + 1)) + 1 := by omega
          simp [later, show start ≤ pc by omega, this]
        · simp [later, show ¬ start ≤ pc by omega]
      | some found =>
        have skip : (((start, found) :: ((rest.zipIdx (start + 1)).filterMap fun entry =>
            entry.1.link?.map fun link => (entry.2, link))).find? fun entry => entry.1 == pc) =
              ((rest.zipIdx (start + 1)).filterMap fun entry =>
                entry.1.link?.map fun link => (entry.2, link)).find? fun entry => entry.1 == pc :=
          List.find?_cons_of_neg different
        simp only [Option.map_some]
        rw [skip, ih (start + 1)]
        by_cases later : start + 1 ≤ pc
        · have : pc - start = (pc - (start + 1)) + 1 := by omega
          simp [later, show start ≤ pc by omega, this]
        · simp [later, show ¬ start ≤ pc by omega]

#print axioms linksOfCode_find

/-- A body whose table is the one its code implies has a link exactly at its linking
    instructions. -/
theorem Method.linkAt_of_implied {body : Method} (implied : body.links = linksOfCode body.code)
    (pc : Nat) : body.linkAt pc = (body.code[pc]?).bind Instruction.link? := by
  simp only [Method.linkAt, linkLookup, implied, linksOfCode_eq_zipIdx]
  rw [linksOfCode_find body.code 0 pc]
  simp

#print axioms Method.linkAt_of_implied

/-- `withCode` gives the body the links its new code implies. -/
theorem Method.withCode_linkAt (method : Method) (code : List Instruction) (pc : Nat) :
    (method.withCode code).linkAt pc = (code[pc]?).bind Instruction.link? :=
  Method.linkAt_of_implied rfl pc

#print axioms Method.withCode_linkAt

/-- A body whose table is the one its code implies reads the link of its instruction at `pc` in one
    step once an instruction equation names that instruction; no table is evaluated. -/
theorem Method.linkAt_of_instruction {body : Method}
    (implied : body.links = linksOfCode body.code) {pc : Nat} {op : Instruction}
    (found : body.code[pc]? = some op) : body.linkAt pc = op.link? := by
  rw [Method.linkAt_of_implied implied pc, found]
  rfl

#print axioms Method.linkAt_of_instruction

/-- A body's table has no entry at a pc the table lists no key for. -/
theorem Method.linkAt_of_unlisted {body : Method} {pc : Nat}
    (unlisted : ∀ entry ∈ body.links, entry.1 ≠ pc) : body.linkAt pc = none := by
  have none_found : (body.links.find? fun entry => entry.1 == pc) = none := by
    rw [List.find?_eq_none]
    intro entry member
    simpa using unlisted entry member
  simp [Method.linkAt, linkLookup, none_found]

#print axioms Method.linkAt_of_unlisted

/-- The methods a call refers to, by index. -/
abbrev Program := List Method

end CIL
