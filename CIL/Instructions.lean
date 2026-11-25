import CIL.Types
import CIL.ExceptionType
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

/-- The admitted integer suffixes of `ldind.*`, `stind.*`, `ldelem.*` and `stelem.*`. -/
inductive NumericKind where
  | i1 | u1 | i2 | u2 | i4 | u4 | i8 | i
  deriving DecidableEq, Repr

/-- Bytes the access moves; native int is eight bytes on every admitted profile. -/
def NumericKind.width : NumericKind → Nat
  | .i1 | .u1 => 1
  | .i2 | .u2 => 2
  | .i4 | .u4 => 4
  | .i8 | .i => 8

/-- Whether a load sign-extends to the stack width: only the one- and two-byte signed kinds,
    since a four-byte load gives the same i32 bits either way. -/
def NumericKind.signed : NumericKind → Bool
  | .i1 | .i2 => true
  | _ => false

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

/-- The span constructor overloads, each building a checked view from its explicit arguments
    without changing memory. -/
inductive SpanConstructor where
  | array (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  | reference (width : Nat) (writable : Bool)
  | singleReference (width : Nat) (writable : Bool)
  /-- `ReadOnlySpan<byte>(void*, int)`, which must lie in extracted static data. -/
  | staticBytes
  deriving DecidableEq, Repr

/-- The checked memory operation underlying a span constructor. -/
def SpanConstructor.operation : SpanConstructor → MemoryOp
  | .array element writable range => .arraySpan element writable range
  | .reference width writable => .spanFromReference width writable
  | .singleReference width writable => .spanSingleReference width writable
  | .staticBytes => .spanCreate

/-- The element width and writability of every span the constructor builds. -/
def SpanConstructor.shape : SpanConstructor → Nat × Bool
  | .array element writable _ => (element.width, writable)
  | .reference width writable | .singleReference width writable => (width, writable)
  | .staticBytes => (1, false)

/-- Target of an overflow-checked conversion; `i` and `u` are native-sized. -/
inductive ConvTarget where
  | i1 | u1 | i2 | u2 | i4 | u4 | i8 | u8 | i | u
  deriving DecidableEq, Repr

/-- Result width in bits; native int is 64 bits on every admitted profile. -/
def ConvTarget.width : ConvTarget → Nat
  | .i1 | .u1 => 8
  | .i2 | .u2 => 16
  | .i4 | .u4 => 32
  | .i8 | .u8 | .i | .u => 64

/-- Whether the target range is signed. -/
def ConvTarget.signed : ConvTarget → Bool
  | .i1 | .i2 | .i4 | .i8 | .i => true
  | .u1 | .u2 | .u4 | .u8 | .u => false

/-- The metadata item an `ldtoken` names. A field token's runtime handle is modelled by the
    reference to the field's read-only storage, which `createSpan` consumes. -/
inductive TokenOperand where
  /-- A metadata type whose runtime handle `ldtoken` loads. -/
  | type (type : Extraction.TypeExpr)
  | field (field : Extraction.FieldRef)
  deriving DecidableEq, Repr

/-- The prefixes of a `call`: `tail.` retires the caller's frame before the transfer, and
    `constrained.` names the type on which the called member is resolved to an implementation. -/
structure CallPrefixes where
  tail : Bool := false
  constrained : Option Extraction.TypeExpr := none
  deriving DecidableEq, Repr

/-- One instruction. Branch targets and call indices are positions in the method's code
    and in the `Program`. Constructors that `CIL.step` does not execute are handled by the
    checked interpreter in `CIL.Safety`. -/
inductive Instruction where
  -- Division and remainder; `divideKind?` gives their flags.
  | div | div_un | rem | rem_un
  -- Overflow-checked arithmetic; `checkedKind?` gives their flags.
  | add_ovf | add_ovf_un | sub_ovf | sub_ovf_un | mul_ovf | mul_ovf_un
  -- Overflow-checked conversion to `target`, reading the operand as signed or as unsigned.
  | conv_ovf (target : ConvTarget) | conv_ovf_un (target : ConvTarget)
  /-- Fresh frame storage of the popped byte count, zeroed when `declared.initLocals` is set. -/
  | localloc
  /-- `newarr` of the declared element type `element`: a fresh zeroed array whose storage the
      method's layouts give that type (`CIL.Method.elementShape`). -/
  | newarr (element : Extraction.TypeExpr)
  | nop | neg | cgt
  -- Signed and unsigned compare-and-branch; more follow `switch` below.
  | bgt (target : Nat)
  | ble (target : Nat)
  | ble_un (target : Nat)
  -- Value-type aggregates and fields, by byte offset and width.
  /-- Read the value of the addressed type. -/
  | ldobj (type : Extraction.TypeExpr)
  /-- Store a value of the addressed type. -/
  | stobj (type : Extraction.TypeExpr)
  /-- Zero the storage of the addressed type. -/
  | initobj (type : Extraction.TypeExpr)
  /-- Push the storage width of the type in bytes. -/
  | sizeof (type : Extraction.TypeExpr)
  /-- Copy the initialized bytes of the type from source to destination. -/
  | cpobj (type : Extraction.TypeExpr)
  /-- `ldind` of `kind`: a load through a reference, or of the entry a native method table
      cursor names. -/
  | ldind (kind : NumericKind)
  /-- `stind` of `kind`: a store through a writable reference. -/
  | stind (kind : NumericKind)
  /-- `ldlen`: the element count of an array or of a managed handler table, as a native int. -/
  | ldlen
  /-- `ldelem` of `kind`: an element of a value array, or with `.i` the entry of a managed
      handler table. -/
  | ldelem (kind : NumericKind)
  /-- `ldelem.ref`: the reference an element slot of an array of class references holds. -/
  | ldelem_ref
  /-- `stelem` of `kind`: a store into an element of a value array. -/
  | stelem (kind : NumericKind)
  /-- `stelem.ref`: a store into an element slot of an array of class references, after the
      covariance check. -/
  | stelem_ref
  /-- `ldelem` of the declared element type `element`: an element of the storage the method's
      layouts give that type (`CIL.Method.elementShape`), or the entry of a managed handler
      table of that signature. -/
  | ldelem_any (element : Extraction.TypeExpr)
  /-- `stelem` of the declared element type `element`: a store into an element of the storage
      the method's layouts give that type. -/
  | stelem_any (element : Extraction.TypeExpr)
  /-- `ldelema` of the declared element type `element`: the address of an element of the
      storage the method's layouts give that type, read-only when `readOnly` records a
      `readonly.` prefix. -/
  | ldelema (element : Extraction.TypeExpr) (readOnly : Bool)
  -- Arguments and locals.
  /-- Pushes argument `index`, read as `Method.argumentAccess` says. -/
  | ldarg (index : Nat)
  /-- Stores the top of the stack into argument `index`'s home, as `storeArgument` says. -/
  | starg (index : Nat)
  /-- Pushes the address of argument `index`'s home, as `addressArgument` says. -/
  | ldarga (index : Nat)
  | ldloc (index : Nat)
  | ldloca (index : Nat)
  | stloc (index : Nat)
  /-- Push the managed method pointer authenticated by the method token and closed signature. -/
  | ldftn (identity : ManagedIdentity) (signature : ManagedSignature)
  /-- Call a managed function pointer with the standalone signature and optional tail prefix. -/
  | calli (signature : ManagedSignature) (tail : Bool)
  -- Constants, conversions, arithmetic and stack shuffling.
  | ldc_i4 (value : W32)
  | ldc_i8 (value : W64)
  /-- `ldnull`: the null object reference. -/
  | ldnull
  /-- `ldstr` pushes the interned object bound to the decoded user-string operand. -/
  | ldstr (text : String)
  /-- `cpblk` and `initblk` carry the alignment established by their preceding prefix. -/
  | cpblk (alignment : Nat) | initblk (alignment : Nat)
  | conv_i1 | conv_i2 | conv_u2
  | conv_i8 | conv_i4 | conv_u1 | conv_u4 | conv_u8 | conv_u | conv_i | not | add | sub | mul
  | and | or
  | xor | shl | shr | shr_un | clt | clt_un | cgt_un | ceq | dup | pop
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
  /-- `call` of `method`: it enters the body its pc links to with `method.argumentCount`
      popped values as arguments. Under `tail.` those are the whole stack and the caller's
      frame retires before the transfer. -/
  | call (method : Extraction.MethodRef) (prefixes : CallPrefixes := {})
  /-- A receiver call enters the direct body or dispatch table at its pc. Null receivers throw. -/
  | callvirt (method : Extraction.MethodRef)
  /-- `newobj` of `constructor`: a fresh zeroed instance of its owner, passed to the constructor
      the link at its pc names as its receiver ahead of the constructor's parameters, and pushed
      once it returns. The link states what is allocated: a value-type temporary for
      `.aggregate`, a class instance with its bases for `.object`. -/
  | newobj (constructor : Extraction.MethodRef)
  /-- `castclass`: the object unchanged when it is null or an instance of `type`;
      `InvalidCastException` otherwise. -/
  | castclass (type : Extraction.TypeExpr)
  /-- `isinst`: the object when it is null or an instance of `type`; null otherwise. -/
  | isinst (type : Extraction.TypeExpr)
  -- Instance fields, reached as `Method.fieldShape` resolves the field for the body.
  /-- `ldfld`: replaces the receiver on top of the stack with the value its field holds. -/
  | ldfld (field : Extraction.FieldRef)
  /-- `ldflda`: replaces the receiver with its field's address; a class field has none. -/
  | ldflda (field : Extraction.FieldRef)
  /-- `stfld`: pops a value and a receiver below it and stores the value into the field. -/
  | stfld (field : Extraction.FieldRef)
  -- Static fields; the descriptor extraction bound to the instruction's pc holds the storage.
  /-- `ldsfld`: the value of the static field `field`. -/
  | ldsfld (field : Extraction.FieldRef)
  /-- `ldsflda`: the address of the static field `field`, in read-only storage. -/
  | ldsflda (field : Extraction.FieldRef)
  /-- `stsfld`: a store to the static field `field`; no static is writable, so it faults. -/
  | stsfld (field : Extraction.FieldRef)
  /-- `ldtoken`: the runtime handle of the token `operand` names. -/
  | ldtoken (operand : TokenOperand)
  | ret
  /-- Throw the object on the evaluation stack. A recognized constructor fold supplies the
      exception type established by its checked operands. -/
  | throw (folded : Option ExceptionType := none)
  /-- `leave` to `target`: empties the stack and exits every protected range that holds the pc
      but not `target`, running the handler of each finally it exits first, innermost first. -/
  | leave (target : Nat)
  /-- `endfinally`: ends the running finally handler and resumes the `leave` or the raised
      exception that entered it. -/
  | endfinally
  /-- A hole carrying the raw `opcode` at its pc: an opcode no instruction family admits, or one
      outside the code the extractor reaches under the selected profile. It faults when stepped. -/
  | unadmitted (opcode : Nat)
  deriving Repr

/-- The name of the instruction type, for tactics that recognise its constructors. -/
def instructionTypeName : Lean.Name := ``CIL.Instruction

/-- `(signed, remainder)` of a division or remainder instruction. -/
def Instruction.divideKind? : Instruction → Option (Bool × Bool)
  | .div => some (true, false)
  | .div_un => some (false, false)
  | .rem => some (true, true)
  | .rem_un => some (false, true)
  | _ => none

/-- `(kind, signed)` of an overflow-checked arithmetic instruction. -/
def Instruction.checkedKind? : Instruction → Option (CheckedBinaryKind × Bool)
  | .add_ovf => some (.add, true)
  | .add_ovf_un => some (.add, false)
  | .sub_ovf => some (.sub, true)
  | .sub_ovf_un => some (.sub, false)
  | .mul_ovf => some (.mul, true)
  | .mul_ovf_un => some (.mul, false)
  | _ => none

/-- A literal, call or construction whose value a static constructor stores in a readonly field. -/
structure StaticInitializer where
  method : Nat
  arguments : List Value
  /-- A direct integer literal store; no method is called when this is present. -/
  literal : Option Value := none
  /-- Construct a zero-initialized aggregate with this instance constructor. -/
  construct : Bool := false
  deriving DecidableEq, Repr

/-- A static field the method reads: its bytes as extracted, and where they came from. `field` is
    the field as the instruction at the site names it, which metadata binding ties to its row;
    `identity` keys the field's storage. -/
structure StaticDescriptor where
  identity : Nat
  field : Extraction.FieldRef
  bytes : List (BitVec 8)
  /-- `some` for a value fixed by its static constructor, `none` for RVA data. -/
  initializer : Option StaticInitializer := none
  /-- Integer fields use their byte width and this signed-load flag; aggregates use `none`. -/
  scalar : Option Bool := none
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
    to `LayoutEnvironment.rawLayouts`. Only implicit receiver signatures are supported. -/
structure DeclaredSignature where
  /-- `some` exactly for an instance method. -/
  receiver : Option Receiver := none
  /-- Declared parameter types in order, `this` excluded. -/
  parameters : List Extraction.TypeExpr := []
  returnType : Extraction.TypeExpr := .void
  /-- The body's localsinit flag: `localloc` storage and locals start zeroed when set. -/
  initLocals : Bool := true
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
  /-- The raw table in positional order for model lookups during execution and validation. -/
  indexedRaw : Array Extraction.RawLayout := rawLayouts.toArray
  index_eq : indexedRaw = rawLayouts.toArray := by rfl
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
  /-- The body whose managed identity an `ldftn` pushes. Taking its address enters no body. -/
  | address (method : Nat)
  /-- `calli`: the bodies a method pointer of the site's signature may name. -/
  | indirect (catalog : List ManagedTarget)
  deriving DecidableEq, Repr

/-- Every method index a link may enter. -/
def Link.callees : Link → List Nat
  | .direct method | .aggregate method _ | .object method _ _ => [method]
  | .virtual targets => targets.map Prod.snd
  | .address _ => []
  | .indirect catalog => catalog.map ManagedTarget.method

/-- The constructor a `newobj` names; `none` for every other instruction. Its link is not implied
    by the operand: the link table states the constructor's index and the allocation. -/
def Instruction.constructor? (op : Instruction) : Option Extraction.MethodRef := by
  cases op
  case newobj constructor => exact some constructor
  all_goals exact none

/-- The instruction is a `newobj`. -/
def Instruction.constructs (op : Instruction) : Bool := op.constructor?.isSome

/-- An instruction that names a constructor is the `newobj` of it. -/
theorem Instruction.eq_newobj_of_constructor? {op : Instruction}
    {constructor : Extraction.MethodRef} (named : op.constructor? = some constructor) :
    op = .newobj constructor := by
  cases op <;> cases named <;> rfl

#print axioms Instruction.eq_newobj_of_constructor?

/-- Instructions whose metadata binding belongs to the method's link table. -/
def Instruction.statesLink (op : Instruction) : Bool := by
  cases op
  case call | callvirt | newobj | ldftn | calli => exact true
  all_goals exact false

/-- Instructions whose execution can consult the link at their pc. -/
def Instruction.readsLink (op : Instruction) : Bool := by
  cases op
  case call | callvirt | newobj | calli => exact true
  all_goals exact false

/-- What an exception clause does with an exception raised in its protected range. -/
inductive HandlerKind where
  /-- A typed catch of exceptions whose runtime class is `type` or derives from it. -/
  | catch (type : Extraction.TypeExpr)
  /-- A finally handler, which runs whenever control leaves the protected range. -/
  | finally
  deriving DecidableEq, Repr

/-- An exception clause of a method body (ECMA-335 II.19) in instruction indices: the protected
    range `[tryStart, tryEnd)` and the handler `[handlerStart, handlerEnd)`. A body lists a
    clause before every clause that encloses it. -/
structure ExceptionClause where
  tryStart : Nat
  tryEnd : Nat
  handlerStart : Nat
  handlerEnd : Nat
  kind : HandlerKind
  deriving DecidableEq, Repr

/-- Whether `pc` lies in the protected range of `clause`. -/
def ExceptionClause.protects (clause : ExceptionClause) (pc : Nat) : Bool :=
  clause.tryStart ≤ pc && pc < clause.tryEnd

/-- Whether `pc` lies in the handler of `clause`. -/
def ExceptionClause.handles (clause : ExceptionClause) (pc : Nat) : Bool :=
  clause.handlerStart ≤ pc && pc < clause.handlerEnd

/-- Whether `clause` is a finally clause. -/
def ExceptionClause.isFinally (clause : ExceptionClause) : Bool :=
  match clause.kind with
  | .finally => true
  | .catch _ => false

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
  links : List (Nat × Link) := []
  returnsValue : Bool
  /-- The exception clauses of the body, nested clauses first; see `ExceptionClause`. -/
  handlers : List ExceptionClause := []
  deriving Repr

/-- No exception clause of `body` protects `pc`, so a fault there leaves the activation. -/
def Method.unprotectedAt (body : Method) (pc : Nat) : Bool :=
  body.handlers.all fun clause => !clause.protects pc

/-- The link the first entry of `links` for `query` gives, `none` without one. -/
def linkLookup (links : List (Nat × Link)) (query : Nat) : Option Link :=
  (links.find? fun entry => entry.1 == query).map Prod.snd

/-- The link of the call-family instruction at `pc`, if the table has one; the first entry wins.
    An extracted method states each call site's link as a generated fact, so a proof need not
    evaluate this scan; for any other body the scan runs over its table, which for a body without
    a written `links` is empty. -/
def Method.linkAt (body : Method) (pc : Nat) : Option Link :=
  linkLookup body.links pc

/-- The static descriptor extraction bound to the static field instruction at `pc`; the first
    site with that pc wins. -/
def Method.staticAt (body : Method) (pc : Nat) : Option StaticDescriptor :=
  (body.staticSites.find? (fun site => site.1 == pc)).map Prod.snd

/-- Replace the code and clear the links, static sites and exception clauses keyed by its pcs. -/
def Method.withCode (method : Method) (code : List Instruction) : Method :=
  { method with code := code, links := [], staticSites := [], handlers := [] }

/-- Replacing the code clears its link table. -/
theorem Method.withCode_linkAt (method : Method) (code : List Instruction) (pc : Nat) :
    (method.withCode code).linkAt pc = none := rfl

#print axioms Method.withCode_linkAt

/-- A table that lists no key `pc` gives it no link. -/
theorem linkLookup_of_unlisted {links : List (Nat × Link)} {pc : Nat}
    (unlisted : ∀ entry ∈ links, entry.1 ≠ pc) : linkLookup links pc = none := by
  have none_found : (links.find? fun entry => entry.1 == pc) = none := by
    rw [List.find?_eq_none]
    intro entry member
    simpa using unlisted entry member
  simp [linkLookup, none_found]

#print axioms linkLookup_of_unlisted

/-- A body's table has no entry at a pc the table lists no key for. -/
theorem Method.linkAt_of_unlisted {body : Method} {pc : Nat}
    (unlisted : ∀ entry ∈ body.links, entry.1 ≠ pc) : body.linkAt pc = none :=
  linkLookup_of_unlisted unlisted

#print axioms Method.linkAt_of_unlisted

/-- The methods a call refers to, by index. -/
abbrev Program := List Method

end CIL
