import CIL.Safety.InstructionMemory

namespace CIL.Safety

def localWidth : CIL.LocalKind → Nat
  | .narrow kind => kind.width
  | .aggregate size => size
  | .byte => 1
  | .word32 => 4
  | .word64 => 8
  | .vector128 => 16
  | .vector256 => 32
  | .vector512 => 64
  | .reference => 0

inductive Opaque128Value where
  | known (bits : BitVec 128)
  | low64 (low : CIL.W64)
  deriving DecidableEq, Repr

def Opaque128Value.value : Opaque128Value → CIL.Value
  | .known bits => .v128 bits
  | .low64 low => .v128Low64 low

/-- Byref slots are roots, not byte encodings that unsafe integer accesses can
    reinterpret. Numeric homes are ordinary allocation-backed byte storage. -/
inductive LocalSlot where
  | bytes (kind : CIL.LocalKind) (reference : Reference)
  | root (value : Option ManagedReference)
  | opaque128 (value : Option Opaque128Value)
  deriving DecidableEq, Repr

structure Frame where
  activation : Nat
  locals : List LocalSlot
  owned : List AllocationId
  arguments : List (Nat × LocalSlot) := []
  deriving Repr

/-- Natural alignment for 32/64-bit scalar homes on the supported 64-bit targets
    (ECMA-335 I.12.6.2).
    Aggregate metadata retains only size; packed aggregates stay byte aligned. -/
def localAlignment : CIL.LocalKind → Nat
  | .word32 => 4
  | .word64 => 8
  | _ => 1

@[simp] theorem localAlignment_pos (kind : CIL.LocalKind) : 0 < localAlignment kind := by
  cases kind <;> simp [localAlignment]

def allocateHome (m : Memory) (activation width : Nat) (alignment : Nat := 1) :
    ExecutionResult (Reference × Memory) := do
  let (id, memory) ← checkedAt .null width (allocate m {
    kind := .frame activation
    layout := ⟨width, alignment, []⟩
    sentinels := [width] })
  let reference : Reference := ⟨id, 0⟩
  return (reference, { memory with
    views := ⟨id, 0, width, true, true⟩ :: memory.views })

def localNumber (kind : CIL.LocalKind) (value : CIL.Value) : ExecutionResult Nat :=
  if value.hasUnspecified then .error (.unsupported "Unspecified vector bytes") else
  match kind, value with
  | .narrow _, .i32 bits => .ok bits.toNat
  | .aggregate size, .aggregate bytes =>
    if bytes.length = size then .ok (byteNumber bytes) else .error .invalidState
  | .byte, .i32 bits => if bits.toNat < 256 then .ok bits.toNat else .error .invalidState
  | .word32, .i32 bits => .ok bits.toNat
  | .word64, .i64 bits => .ok bits.toNat
  | .vector128, .v128 bits => .ok bits.toNat
  | .vector256, .v256 bits => .ok bits.toNat
  | .vector512, .v512 bits => .ok bits.toNat
  | _, _ => .error .invalidState

/-- Readback after a typed store includes the CLI's narrowing and extension. -/
def localResult (kind : CIL.LocalKind) (value : CIL.Value) : CIL.Value :=
  match kind, value with
  | .narrow kind, .i32 bits => .i32 (kind.extend bits)
  | _, value => value

def localSnapshotShape : CIL.LocalKind → Option CIL.SnapshotShape
  | .aggregate size => some (.aggregate size)
  | .vector128 => some .vector128
  | .vector256 => some .vector256
  | .vector512 => some .vector512
  | _ => none

def storeLocal (m : Memory) (slot : LocalSlot) (value : Value) :
    ExecutionResult (LocalSlot × Memory) := do
  let selectedOpaque := match slot with | .opaque128 _ => true | _ => false
  if value.hasUnspecified && !selectedOpaque then .error (.unsupported "Byte home observes unspecified vector bits") else
  match slot, value with
  | .opaque128 _, .scalar (.v128 bits) => return (.opaque128 (some (.known bits)), m)
  | .opaque128 _, .scalar (.v128Low64 low) => return (.opaque128 (some (.low64 low)), m)
  | .root _, .reference reference =>
    let _ ← formValue m reference
    return (.root (some reference), m)
  | .bytes kind reference, .scalar (.snapshot shape bytes) =>
    if localSnapshotShape kind != some shape || bytes.length != localWidth kind then .error .invalidState else
      let memory ← checkedAt (.address reference) (localWidth kind) (writeSnapshot m reference bytes 1)
      return (slot, memory)
  | .bytes kind reference, .scalar value =>
    let number ← localNumber kind value
    let memory ← checkedAt (.address reference) (localWidth kind)
      (write m reference (numberBytes number (localWidth kind)) 1)
    return (slot, memory)
  | _, _ => .error .invalidState

def loadLocal (m : Memory) (slot : LocalSlot) : ExecutionResult Value := do
  match slot with
  | .opaque128 none => .error (.unsupported "Uninitialized opaque vector local")
  | .opaque128 (some value) => return .scalar value.value
  | .root none => .error .invalidState
  | .root (some reference) => formValue m reference
  | .bytes kind reference =>
    if let some shape := localSnapshotShape kind then
      if let .error .uninitialized := read m reference (localWidth kind) 1 then
        return .scalar (← loadSnapshot m (.address reference) shape)
    let bytes ← checkedAt (.address reference) (localWidth kind)
      (read m reference (localWidth kind) 1)
    let number := byteNumber bytes
    match kind with
    | .narrow kind => return .scalar (.i32 (kind.extend (BitVec.ofNat 32 number)))
    | .aggregate _ => return .scalar (.aggregate bytes)
    | .byte | .word32 => return .scalar (.i32 (BitVec.ofNat 32 number))
    | .word64 => return .scalar (.i64 (BitVec.ofNat 64 number))
    | .vector128 => return .scalar (.v128 (BitVec.ofNat 128 number))
    | .vector256 => return .scalar (.v256 (BitVec.ofNat 256 number))
    | .vector512 => return .scalar (.v512 (BitVec.ofNat 512 number))
    | .reference => .error .invalidState

def localAddress (m : Memory) (slot : LocalSlot) : ExecutionResult Value :=
  match slot with
  | .bytes _ reference => formValue m (.address reference)
  | .root _ => .error (.unsupported "Address of managed-reference local")
  | .opaque128 _ => .error (.unsupported "Address of opaque vector local")

/-- Initialized reads retain the original typed decoding, independently of the
    fallback used for partial aggregate/vector copies. -/
theorem loadLocal_of_read {m : Memory} {reference : Reference} {kind : CIL.LocalKind}
    {bytes : List (BitVec 8)} (loaded : read m reference (localWidth kind) 1 = .ok bytes) :
    loadLocal m (.bytes kind reference) =
      (match kind with
      | .narrow k => .ok (.scalar (.i32 (k.extend (BitVec.ofNat 32 (byteNumber bytes)))))
      | .aggregate _ => .ok (.scalar (.aggregate bytes))
      | .byte | .word32 => .ok (.scalar (.i32 (BitVec.ofNat 32 (byteNumber bytes))))
      | .word64 => .ok (.scalar (.i64 (BitVec.ofNat 64 (byteNumber bytes))))
      | .vector128 => .ok (.scalar (.v128 (BitVec.ofNat 128 (byteNumber bytes))))
      | .vector256 => .ok (.scalar (.v256 (BitVec.ofNat 256 (byteNumber bytes))))
      | .vector512 => .ok (.scalar (.v512 (BitVec.ofNat 512 (byteNumber bytes))))
      | .reference => .error .invalidState) := by
  simp only [loadLocal, loaded, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases kind <;> rfl

/-- Create one typed local without treating unknown bytes as initialized. -/
def makeLocal (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value) (m : Memory) :
    ExecutionResult (LocalSlot × List AllocationId × Memory) := do
  match kind with
  | .reference => match initial with
    | .nullRef => .ok (.root (some .null), [], m)
    | .unmodeled => .ok (.root none, [], m)
    | _ => .error .invalidState
  | _ => do
    let (reference, memory) ← allocateHome m activation (localWidth kind) (localAlignment kind)
    let slot := LocalSlot.bytes kind reference
    if initial = .unmodeled then return (slot, [reference.allocation], memory)
    else
      let (slot, memory) ← storeLocal memory slot (.scalar initial)
      return (slot, [reference.allocation], memory)

/-- Metadata and initializer lists must agree exactly. In particular an
    uninitialized local still has its extracted physical width. -/
def makeLocals (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (m : Memory) :
    ExecutionResult (List LocalSlot × List AllocationId × Memory) := do
  match kinds, initializers with
  | [], [] => return ([], [], m)
  | kind :: kinds, initial :: initializers =>
    let (slot, owned, memory) ← makeLocal activation kind initial m
    let (slots, other, memory) ← makeLocals activation kinds initializers memory
    return (slot :: slots, owned ++ other, memory)
  | _, _ => .error .invalidState

def makeOpaque128 (initial : CIL.Value) (m : Memory) :
    ExecutionResult (LocalSlot × List AllocationId × Memory) :=
  match initial with
  | .v128 bits => .ok (.opaque128 (some (.known bits)), [], m)
  | .unmodeled => .ok (.opaque128 none, [], m)
  | _ => .error .invalidState

def makeSelectedLocalsFrom (activation : Nat) (indices : List Nat) : Nat → List CIL.LocalKind →
    List CIL.Value → Memory → ExecutionResult (List LocalSlot × List AllocationId × Memory)
  | _, [], [], m => .ok ([], [], m)
  | index, kind :: kinds, initial :: initials, m => do
    let (slot, owned, memory) ← if index ∈ indices then
      if kind == .vector128 then makeOpaque128 initial m else .error .invalidState
      else makeLocal activation kind initial m
    let (slots, other, memory) ← makeSelectedLocalsFrom activation indices (index + 1) kinds initials memory
    return (slot :: slots, owned ++ other, memory)
  | _, _, _, _ => .error .invalidState

def makeSelectedLocals (activation : Nat) (indices : List Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (m : Memory) : ExecutionResult (List LocalSlot × List AllocationId × Memory) :=
  if indices.isEmpty then makeLocals activation kinds initializers m
  else makeSelectedLocalsFrom activation indices 0 kinds initializers m

/-- Methods without opaque locals retain the byte-home frame model. -/
@[simp] theorem makeSelectedLocals_nil (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (m : Memory) :
    makeSelectedLocals activation [] kinds initializers m = makeLocals activation kinds initializers m := rfl
#print axioms makeSelectedLocals_nil

/-- Aggregate argument instructions operate on a private snapshot home, never
    directly on the caller's by-value source. Their extracted indices identify
    the 256-bit vector representation supported by those CIL operations. -/
def makeArgumentHomes (activation : Nat) (indices : List Nat) (args : List Value)
    (m : Memory) : ExecutionResult (List (Nat × LocalSlot) × List AllocationId × Memory) := do
  match indices with
  | [] => return ([], [], m)
  | index :: rest =>
    if (args[index]?.map Value.hasUnspecified).getD false then
      .error (.unsupported "Argument home observes unspecified vector bits") else
    let some (.scalar (.v256 bits)) := args[index]? | .error .invalidState
    let (reference, memory) ← allocateHome m activation (localWidth .vector256)
    let (slot, memory) ← storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits))
    let (homes, owned, memory) ← makeArgumentHomes activation rest args memory
    return ((index, slot) :: homes, reference.allocation :: owned, memory)

def argumentHome (frame : Frame) (index : Nat) : ExecutionResult LocalSlot := do
  let some (_, slot) := frame.arguments.find? (fun home => home.1 == index) | .error .invalidState
  return slot

/-- Materialize only parameters that are assigned or addressed. By-value homes
    are private to the activation; byref parameters retain their reference value. -/
def makeParameterHomes (activation : Nat) (parameters : List (Nat × CIL.LocalKind))
    (args : List Value) (m : Memory) :
    ExecutionResult (List (Nat × LocalSlot) × List AllocationId × Memory) := do
  match parameters with
  | [] => return ([], [], m)
  | (index, kind) :: rest =>
    let some value := args[index]? | .error .invalidState
    let (slot, owned, memory) ← makeLocal activation kind .unmodeled m
    let (slot, memory) ← storeLocal memory slot value
    let (homes, other, memory) ← makeParameterHomes activation rest args memory
    return ((index, slot) :: homes, owned ++ other, memory)

def enterFrame (body : CIL.Method) (args : List Value) (m : Memory) : ExecutionResult (Frame × Memory) := do
  let activation := m.nextIdentity
  let (locals, owned, memory) ← makeSelectedLocals activation body.opaqueVectorLocals body.localKinds body.locals m
  let (arguments, argumentIds, memory) ← makeArgumentHomes activation body.vectorArgs args memory
  let (parameters, parameterIds, memory) ← makeParameterHomes activation body.parameterHomes args memory
  return (⟨activation, locals ++ parameters.map Prod.snd, (owned ++ argumentIds) ++ parameterIds, arguments⟩, memory)

def leaveFrame (frame : Frame) (m : Memory) : Memory :=
  frame.owned.foldl expire m

/-- The pre-opaque frame equation, under its explicit default-metadata premise. -/
theorem enterFrame_of_no_opaque (body : CIL.Method) (args : List Value) (m : Memory)
    (none : body.opaqueVectorLocals = []) :
    enterFrame body args m = (do
      let activation := m.nextIdentity
      let (locals, owned, memory) ← makeLocals activation body.localKinds body.locals m
      let (arguments, argumentIds, memory) ← makeArgumentHomes activation body.vectorArgs args memory
      let (parameters, parameterIds, memory) ← makeParameterHomes activation body.parameterHomes args memory
      return (⟨activation, locals ++ parameters.map Prod.snd, (owned ++ argumentIds) ++ parameterIds, arguments⟩, memory)) := by
  simp only [enterFrame, none, makeSelectedLocals_nil]
#print axioms enterFrame_of_no_opaque

end CIL.Safety
