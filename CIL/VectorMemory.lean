import CIL.ArrayTypes
import CIL.Memory
import CIL.WideMultiply

/-!
# Vector memory and unsafe references

128-, 256- and 512-bit loads and stores, `Unsafe` reference arithmetic, and the memory
instructions (`MemoryOp`) of the reference interpreter. In caller storage a vector is
stored little-endian, byte by byte, like scalars in `CIL.Memory`, so vector and scalar
accesses to the same bytes agree. A scalar local holds a whole vector value instead.

Exact overload references (.NET 10):
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.add?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.bitcast?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.interopservices.memorymarshal.getreference?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.readonlyspan-1.-ctor?view=net-10.0
   Unsafe.Add scales by element size. BitCast preserves storage bits.
   The shared value evaluator models static byte spans. Checked array-backed and
   reference-backed primitive spans use the memory rules in CIL.Safety.
   Static bytes come from the extracted RVA field.
-/

namespace CIL

/-- Vector values are snapshots; references continue to name the underlying bytes.
    No alignment assumption is imposed on caller accesses. -/
def read128 (memory : Memory) : Address → Option Value
  | .byte base => do return .v128 (BitVec.ofNat 128 (← readBytes memory base 16))
  | .local frame index => do
    let .v128 bits ← memory (.local frame index) | none
    return .v128 bits
  | .static bytes base => do return .v128 (BitVec.ofNat 128 (← readStaticBytes bytes base 16))
  | .home frame kind index offset =>
    if offset + 16 ≤ 32 then do
      return .v128 (BitVec.ofNat 128 (← readHomeBytes memory frame kind index offset 16))
    else none

/-- Reads a 256-bit vector; a home read must cover the whole 32-byte home. -/
def read256 (memory : Memory) : Address → Option Value
  | .byte base => do return .v256 (BitVec.ofNat 256 (← readBytes memory base 32))
  | .local frame index => do
    let .v256 bits ← memory (.local frame index) | none
    return .v256 bits
  | .static bytes base => do return .v256 (BitVec.ofNat 256 (← readStaticBytes bytes base 32))
  | .home frame kind index offset =>
    if offset + 32 ≤ 32 then do
      return .v256 (BitVec.ofNat 256 (← readHomeBytes memory frame kind index offset 32))
    else none

/-- Writes a 128-bit vector. Read-only data cannot be written; a home write must stay
    within its 32 bytes. -/
def write128 (memory : Memory) (address : Address) (bits : BitVec 128) : Option Memory :=
  match address with
  | .byte base => some (writeBytes memory base bits.toNat 16)
  | .local frame index => some (write memory (.local frame index) (.v128 bits))
  | .static _ _ => none
  | .home frame kind index offset =>
    if offset + 16 ≤ 32 then some (writeHomeBytes memory frame kind index offset bits.toNat 16)
    else none

/-- Writes a 256-bit vector. Read-only data cannot be written; a home write must cover the
    whole 32-byte home. -/
def write256 (memory : Memory) (address : Address) (bits : BitVec 256) : Option Memory :=
  match address with
  | .byte base => some (writeBytes memory base bits.toNat 32)
  | .local frame index => some (write memory (.local frame index) (.v256 bits))
  | .static _ _ => none
  | .home frame kind index offset =>
    if offset + 32 ≤ 32 then some (writeHomeBytes memory frame kind index offset bits.toNat 32)
    else none

/-- Reads a 512-bit vector; it does not fit in a home, so a home read is stuck. -/
def read512 (memory : Memory) : Address → Option Value
  | .byte base => do return .v512 (BitVec.ofNat 512 (← readBytes memory base 64))
  | .local frame index => do
    let .v512 bits ← memory (.local frame index) | none
    return .v512 bits
  | .static bytes base => do return .v512 (BitVec.ofNat 512 (← readStaticBytes bytes base 64))
  | .home .. => none

/-- Writes a 512-bit vector; read-only data cannot be written and a home is too small. -/
def write512 (memory : Memory) (address : Address) (bits : BitVec 512) : Option Memory :=
  match address with
  | .byte base => some (writeBytes memory base bits.toNat 64)
  | .local frame index => some (write memory (.local frame index) (.v512 bits))
  | .static .. | .home .. => none

/-- Only actual pointer representations may be reinterpreted as managed refs.
    In particular, a vector snapshot cannot become a pointer to caller storage. -/
def unsafeAsRef : Value → Option Value
  | .object base => some (.ref (.byte base))
  | .ref address => some (.ref address)
  | _ => none

/-- Byte-address arithmetic is unbounded, as in the existing scalar memory
    model. Negative offsets must remain nonnegative. Local slots are typed
    storage, so offsetting into neighboring slots is explicitly unsupported. -/
def unsafeAdd (sizeBytes : Nat) (offset : Int) : Address → Option Address
  | .byte base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address then some (.byte address.toNat) else none
  | .local frame index =>
    if offset = 0 then some (.local frame index) else none
  | .static bytes base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address then some (.static bytes address.toNat) else none
  | .home frame kind index base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address ∧ address ≤ 32 then some (.home frame kind index address.toNat) else none

@[simp ↓] theorem unsafeAdd_byte_natural (size base offset : Nat) :
    unsafeAdd size (offset : Int) (.byte base) = some (.byte (base + size * offset)) := by
  simp [unsafeAdd, ← Int.natCast_mul, ← Int.natCast_add]

/-- The integer arguments of an array-to-span conversion. -/
inductive ArraySpanRange where
  | whole | fromStart | counted
  deriving DecidableEq, Repr

/-- The array plus any start and length arguments. -/
def ArraySpanRange.argumentCount : ArraySpanRange → Nat
  | .whole => 1 | .fromStart => 2 | .counted => 3

/-- Reference-free representations transferred by the checked MemoryMarshal helpers. -/
inductive TransferKind where
  | scalar (width : Nat) (signed : Bool)
  | snapshot (shape : SnapshotShape)
  deriving DecidableEq, Repr

/-- The complete byte extent transferred by a value operation. -/
def TransferKind.width : TransferKind → Nat
  | .scalar width _ => width
  | .snapshot shape => shape.width

/-- Observations of existing views that neither read bytes nor grant write authority. -/
inductive ViewObservation where
  | spanEmpty | spanPinnable | arrayData
  deriving DecidableEq, Repr

/-- Exact memory calls and object opcodes supported by the reachable vector
    bodies. Widths and signedness are fixed by the validated overload. -/
inductive MemoryOp where
  /-- Inspect an existing view without accessing its element contents. -/
  | observeView (observation : ViewObservation)
  /-- Fixed-width endian-aware reads; short try-reads initialize the out value to zero. -/
  | binaryRead (width : Nat) (signed bigEndian trying : Bool)
  /-- Fixed-width endian-aware writes; short try-writes leave the span unchanged. -/
  | binaryWrite (width : Nat) (bigEndian trying : Bool)
  /-- Reinterpret existing bytes without changing their storage or authority. -/
  | spanReinterpret (sourceWidth targetWidth : Nat) (writable : Bool)
  /-- Snapshot copying permits overlapping spans; try-copy returns false for a short target. -/
  | spanCopy (width : Nat) (tryCopy : Bool)
  | spanFill (width : Nat) (clear : Bool)
  | bigMul64
  | copyBlock (alignment : Nat) | initBlock (alignment : Nat)
  | load128 | load256 | load512 | store128 | store256 | store512 | init256
  | asRef | add (sizeBytes : Nat) (signed : Bool)
  /-- The target-minus-origin byte displacement within one live allocation. -/
  | byteOffset
  /-- Read into a value or an out reference; a short try-read stores default(T). -/
  | marshalRead (kind : TransferKind) (tryRead : Bool)
  /-- Copy an in-reference value to a byte span; a short try-write has no memory effect. -/
  | marshalWrite (kind : TransferKind) (tryWrite : Bool)
  /-- A typed pointer transfer with independently validated alignment. -/
  | pointerTransfer (kind : TransferKind) (alignment : Nat) (store : Bool)
  | bitcast256 | bitcastByteBool | skipInit
  | bitcastValue (source target : SnapshotShape)
  | staticAddress (bytes : List (BitVec 8)) | spanCreate | spanReference
  /-- The value of a constructor-initialized readonly field; its address is never formed. -/
  | staticValue (bytes : List (BitVec 8))
  /-- A span of `width`-byte elements over a whole static field; indexing is bounds checked. -/
  | createSpan (width : Nat) | spanItem (width : Nat) | spanLength
  /-- Primitive spans over supplied storage; these operations never grant memory authority. -/
  | spanEmpty (width : Nat) (writable : Bool)
  | spanFromReference (width : Nat) (writable : Bool)
  | spanSingleReference (width : Nat) (writable : Bool)
  | spanSlice (explicitLength : Bool) | spanReadOnly
  /-- A span view over supplied reference-free array storage, without allocation or copying. -/
  | arraySpan (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  /-- Integer operations over supplied array storage; allocation is not modelled. -/
  | arrayLength | arrayLoad (width : Nat) (signed : Bool) | arrayStore (width : Nat)
  /-- A checked element address retains allocation provenance without granting authority. -/
  | arrayAddress (element : ArrayElement) (writable : Bool := true)
  /-- A typed reference-free element transfer retains byte initialization masks. -/
  | arrayTransfer (element : ArrayElement) (store : Bool)
  /-- `Unsafe.NullRef<T>` pushes the null reference; `Unsafe.IsNullRef<T>` tests for it. -/
  | nullRef | isNullRef
  deriving Repr

/-- Every popped operand; no default, so each new operation states what it reads. -/
def MemoryOp.argumentCount : MemoryOp → Nat
  | .observeView _ => 1
  | .binaryRead _ _ _ trying => if trying then 2 else 1
  | .binaryWrite .. => 2
  | .spanCopy .. => 2
  | .spanFill _ clear => if clear then 1 else 2
  | .marshalRead _ tryRead => if tryRead then 2 else 1
  | .marshalWrite .. => 2
  | .pointerTransfer _ _ store => if store then 2 else 1
  | .bigMul64 | .copyBlock _ | .initBlock _ => 3
  | .spanSlice explicitLength => if explicitLength then 3 else 2
  | .spanFromReference .. | .byteOffset => 2
  | .spanSingleReference .. => 1
  | .arraySpan _ _ range => range.argumentCount
  | .spanReinterpret .. | .spanReadOnly | .arrayLength => 1
  | .arrayLoad .. | .arrayAddress .. => 2
  | .arrayTransfer _ store => if store then 3 else 2
  | .arrayStore _ => 3
  | .store128 | .store256 | .store512 | .add .. | .spanCreate | .spanItem _ => 2
  | .staticAddress _ | .staticValue _ | .nullRef | .spanEmpty .. => 0
  | .load128 | .load256 | .load512 | .init256 | .asRef | .bitcast256 | .bitcastByteBool
  | .skipInit | .bitcastValue .. | .createSpan _ | .spanReference | .spanLength | .isNullRef => 1

/-- Signed Int32/native and unsigned native element offsets on the 64-bit target. -/
def offsetValue (signed : Bool) (value : Value) : Option Int :=
  match signed, value with
  | true, .i32 bits => some bits.toInt
  | true, .i64 bits => some bits.toInt
  | false, .i64 bits => some (bits.toNat : Int)
  | _, _ => none

/-- Runs a memory instruction on the evaluation stack (top first), giving the new memory and
    stack. Ill-typed operands, out-of-range accesses and writes to read-only data are stuck. -/
def evalMemory (op : MemoryOp) (stack : List Value) (memory : Memory) :
    Option (Memory × List Value) := do
  match op, stack with
  -- `Math.BigMul`: the low word is stored through the reference, the high word is pushed.
  | .bigMul64, .ref low :: .i64 right :: .i64 left :: rest =>
    return (← write64 memory low (left * right), .i64 (WideMultiply.high64 left right) :: rest)
  -- Vector loads and stores, through a reference or an object; `init256` stores zero.
  | .load128, .ref address :: rest => return (memory, (← read128 memory address) :: rest)
  | .load256, .ref address :: rest => return (memory, (← read256 memory address) :: rest)
  | .load256, .object base :: rest => return (memory, (← read256 memory (.byte base)) :: rest)
  | .load512, .ref address :: rest => do return (memory, (← read512 memory address) :: rest)
  | .store512, .v512 bits :: .ref address :: rest =>
    return (← write512 memory address bits, rest)
  | .store128, .v128 bits :: .ref address :: rest =>
    return (← write128 memory address bits, rest)
  | .store256, .v256 bits :: .ref address :: rest =>
    return (← write256 memory address bits, rest)
  | .store256, .v256 bits :: .object base :: rest =>
    return (← write256 memory (.byte base) bits, rest)
  | .init256, .ref address :: rest => return (← write256 memory address 0, rest)
  | .init256, .object base :: rest => return (← write256 memory (.byte base) 0, rest)
  -- `Unsafe` reinterpretation, offsets and skipped initialization.
  | .asRef, v :: rest => return (memory, (← unsafeAsRef v) :: rest)
  | .add size signed, offset :: .ref address :: rest =>
    return (memory, .ref (← unsafeAdd size (← offsetValue signed offset) address) :: rest)
  | .bitcast256, .v256 bits :: rest => return (memory, .v256 bits :: rest)
  | .bitcastByteBool, .i32 bits :: rest =>
    if bits.toNat < 256 then return (memory, .i32 bits :: rest) else none
  | .bitcastByteBool, .i8 bits :: rest =>
    return (memory, .i32 (bits.zeroExtend 32) :: rest)
  | .skipInit, .object _ :: rest | .skipInit, .ref _ :: rest => return (memory, rest)
  -- Null references.
  | .nullRef, _ => return (memory, .nullRef :: stack)
  | .isNullRef, .nullRef :: rest => return (memory, .i32 1 :: rest)
  | .isNullRef, .object _ :: rest | .isNullRef, .ref _ :: rest => return (memory, .i32 0 :: rest)
  -- Read-only static data and spans over it; span indexing is bounds checked.
  | .createSpan width, .ref (.static bytes 0) :: rest =>
    if 0 < width ∧ bytes.length % width = 0 then
      return (memory, .span (.static bytes 0) (bytes.length / width) :: rest)
    else none
  | .spanItem width, .i32 index :: .span (.static bytes offset) length :: rest =>
    if index.toNat < length then
      return (memory, .ref (.static bytes (offset + index.toNat * width)) :: rest)
    else none
  | .spanLength, .span _ length :: rest => return (memory, .i32 (BitVec.ofNat 32 length) :: rest)
  | .staticAddress bytes, _ => return (memory, .ref (.static bytes 0) :: stack)
  | .spanCreate, .i32 length :: .ref (.static bytes offset) :: rest =>
    if 0 ≤ length.toInt ∧ offset + length.toNat ≤ bytes.length then
      return (memory, .span (.static bytes offset) length.toNat :: rest)
    else none
  | .spanReference, .span address length :: rest =>
    if length = 0 then none else return (memory, .ref address :: rest)
  | _, _ => none

end CIL
