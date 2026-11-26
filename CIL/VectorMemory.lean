import CIL.ArgumentGuards
import CIL.ArrayTypes
import CIL.Memory
import CIL.TypeExpr
import CIL.WideMultiply

/-!
# Vector memory and unsafe references

128- and 256-bit loads, `Unsafe` reference arithmetic, and the operations bound to modeled
memory calls. In caller storage a vector is
stored little-endian, byte by byte, like scalars in `CIL.Memory`, so vector and scalar
accesses to the same bytes agree. A scalar local holds a whole vector value instead.

Exact overload references (.NET 10):
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.add?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.bitcast?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.interopservices.memorymarshal.getreference?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.readonlyspan-1.-ctor?view=net-10.0
   Unsafe.Add scales by element size. BitCast preserves storage bits.
   Checked static, array-backed and reference-backed spans use the memory rules in CIL.Safety.
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

/-- Reads a 256-bit vector. -/
def read256 (memory : Memory) : Address → Option Value
  | .byte base => do return .v256 (BitVec.ofNat 256 (← readBytes memory base 32))
  | .local frame index => do
    let .v256 bits ← memory (.local frame index) | none
    return .v256 bits
  | .static bytes base => do return .v256 (BitVec.ofNat 256 (← readStaticBytes bytes base 32))

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
  /-- Fill an exact typed array, optionally taking int32 start/count, through checked storage. -/
  | arrayFill (element : ArrayElement) (counted : Bool)
  /-- `Math.BigMul` on 64-bit words: store the low word, push the unsigned or signed high. -/
  | bigMul64 (signed : Bool)
  /-- Signed `Math.DivRem(left, right, out remainder)` on `width`-bit integers. -/
  | divRemOut (width : Nat)
  | copyBlock (alignment : Nat) | initBlock (alignment : Nat)
  | load128 | load256 | load512 | store128 | store256 | store512
  /-- `Vector128.LoadUnsafe` or `StoreUnsafe` on bytes: an unsigned native byte offset, when
      present, displaces the reference as `Unsafe.Add` does, then sixteen bytes move as in
      `load128` or `store128`. The store takes its vector below the reference. -/
  | vector128Unsafe (store offset : Bool)
  | asRef | add (sizeBytes : Nat) (signed : Bool)
  /-- The target-minus-origin byte displacement within one live allocation. -/
  | byteOffset
  /-- Read into a value or an out reference; a short try-read stores default(T). -/
  | marshalRead (kind : TransferKind) (tryRead : Bool)
  /-- Copy an in-reference value to a byte span; a short try-write has no memory effect. -/
  | marshalWrite (kind : TransferKind) (tryWrite : Bool)
  /-- A typed pointer transfer with independently validated alignment. -/
  | pointerTransfer (kind : TransferKind) (alignment : Nat) (store : Bool)
  | bitcastByteBool
  | bitcastValue (source target : SnapshotShape)
  | spanCreate | spanReference
  /-- A span of `width`-byte elements over a whole static field; indexing is bounds checked. -/
  | createSpan (width : Nat) | spanItem (width : Nat) | spanLength
  /-- Primitive spans over supplied storage; these operations never grant memory authority. -/
  | spanEmpty (width : Nat) (writable : Bool)
  | spanFromReference (width : Nat) (writable : Bool)
  | spanSingleReference (width : Nat) (writable : Bool)
  | spanSlice (explicitLength : Bool) | spanReadOnly
  /-- A span view over supplied reference-free array storage, without allocation or copying. -/
  | arraySpan (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  /-- `Unsafe.NullRef<T>` pushes the null reference; `Unsafe.IsNullRef<T>` tests for it. -/
  | nullRef | isNullRef
  /-- `ArgumentNullException.ThrowIfNull(argument, paramName)`: throws for a null argument. The
      parameter name is an opaque string nothing reads. -/
  | throwIfNull
  /-- An `ArgumentOutOfRangeException` guard testing a `width`-bit integer against zero. The
      parameter name is an opaque string nothing reads. -/
  | zeroGuard (guard : ZeroGuard) (width : Nat) (signed : Bool)
  /-- An `ArgumentOutOfRangeException` guard comparing a `width`-bit integer with a bound. The
      parameter name is an opaque string nothing reads. -/
  | comparisonGuard (guard : ComparisonGuard) (width : Nat) (signed : Bool)
  deriving DecidableEq, Repr

/-- Bytes the model reserves for each class instance field, in declaration order. The layout is
    sound only while code cannot observe field offsets, so `ldflda` on a class faults. -/
def objectFieldSlot : Nat := 8

/-- The model offset of the class instance field at `index` among the instance fields. -/
def objectFieldOffset (index : Nat) : Nat := objectFieldSlot * index

/-- Every popped operand; no default, so each new operation states what it reads. -/
def MemoryOp.argumentCount : MemoryOp → Nat
  | .observeView _ => 1
  | .binaryRead _ _ _ trying => if trying then 2 else 1
  | .binaryWrite .. => 2
  | .spanCopy .. => 2
  | .spanFill _ clear => if clear then 1 else 2
  | .arrayFill _ counted => if counted then 4 else 2
  | .marshalRead _ tryRead => if tryRead then 2 else 1
  | .marshalWrite .. => 2
  | .throwIfNull | .zeroGuard .. => 2
  | .comparisonGuard .. => 3
  | .pointerTransfer _ _ store => if store then 2 else 1
  | .vector128Unsafe store offset => (if store then 2 else 1) + (if offset then 1 else 0)
  | .bigMul64 _ | .divRemOut _ | .copyBlock _ | .initBlock _ => 3
  | .spanSlice explicitLength => if explicitLength then 3 else 2
  | .spanFromReference .. | .byteOffset => 2
  | .spanSingleReference .. => 1
  | .arraySpan _ _ range => range.argumentCount
  | .spanReinterpret .. | .spanReadOnly => 1
  | .store128 | .store256 | .store512 | .add .. | .spanCreate | .spanItem _ => 2
  | .nullRef | .spanEmpty .. => 0
  | .load128 | .load256 | .load512 | .asRef | .bitcastByteBool | .bitcastValue .. | .createSpan _
  | .spanReference | .spanLength | .isNullRef => 1

/-- Signed Int32/native and unsigned native element offsets on the 64-bit target. -/
def offsetValue (signed : Bool) (value : Value) : Option Int :=
  match signed, value with
  | true, .i32 bits => some bits.toInt
  | true, .i64 bits => some bits.toInt
  | false, .i64 bits => some (bits.toNat : Int)
  | _, _ => none

end CIL
