# CIL opcode support

Read this page to find whether `leancil extract` accepts an instruction or runtime call in your
method, and under which restrictions. The table below lists every opcode encoding the translator
handles. It is an inventory of implemented behaviour: it does not claim that every listed
opcode/operand combination has its own regression test, or that the model is equivalent to every
.NET runtime. Opcode meanings follow ECMA-335 as amended by the augments listed in the
[specification baseline](SOUNDNESS-SPEC.md).

- A row marked "Complete within the admitted model" implements the opcode's operation for its
  admitted operands; ordinary stack and value validity checks still apply.
- A row marked "Partial" lists additional type, layout, control-flow or runtime restrictions.
  Unsupported operand shapes can fail during checked execution even when translation succeeds.
- Extraction rejects every opcode the table does not list.

Every row is subject to the common target restrictions: Release IL-only .NET 11 assemblies,
64-bit little-endian execution, admitted types, no exception handlers and validated reachable
control flow. Ordinary managed calls must have an acyclic extraction order; checked tail
transfers may form cycles. A translated method still requires a proof of the desired property;
exhausted fuel, invalid states and unsupported operations are failures, never implicit successes.
Release configuration does not guarantee that a compiler emits only supported instructions:
reachable exception handling, for example, is rejected. A runtime-async method, which carries
the `Async` implementation flag, is rejected as an entry and as a callee: its body returns the
awaited result and the runtime builds the declared task.

## Translated opcodes

Ranges include every numbered form between the endpoints, and `.s` is the short encoding of the
same operation. Native `nint`/`nuint` values use `i64` on the validated 64-bit target. For mixed
native/int32 arithmetic and comparisons, extraction tracks stack types and emits an explicit
widening wrapper that sign-extends the int32 operand, except that unsigned checked arithmetic
zero-extends it; scalar `clt.un`/`cgt.un` sign-extend it too, matching the admitted runtime. The
wrapper preserves arithmetic faults and branch targets and cannot dispatch memory or calls.
Invalid native/int64 mixtures are rejected. Mixed native/int32 unsigned branches (`bne.un`,
`blt.un`, `bgt.un`, `ble.un`, `bge.un`, including short forms) are rejected because CoreCLR
widening depends on operand provenance; insert an explicit `conv.i` or `conv.u` to select
same-width semantics. The rows below describe scalar operands after this widening; other mixed
widths are unsupported.

`i32` and `i64` refer to the model's 32- and 64-bit integer stack values; managed references are
separate values and are not integer addresses.

Same-assembly enums backed by `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or
`ulong` execute as their underlying integer type in every operation below, including fields,
argument homes and typed memory instructions, and unnamed values are supported
([integer enums](SOUNDNESS-RUNTIME.md#integer-enums)). Boxing, `System.Enum` methods and
external enum dependencies are not supported.

| Opcodes | Status | Implemented behaviour and restrictions |
| --- | --- | --- |
| `newarr` | Partial | Fresh zero-initialized primitive integer, same-assembly enum, validated reference-free aggregate and integer-vector arrays, including native integers, `bool` and `char`. Composite element sizes must be positive and fit the CoreCLR 16-bit component-size field; byref-like elements are rejected. Int32/native lengths must be nonnegative and at most the .NET 10 CoreCLR ceiling `0x7fffffc7`; negative lengths raise `System.OverflowException`. Identity and resource premises are in [arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory). `newarr` of an admitted class, or of a non-generic class outside the model other than `object`, such as `string`, allocates an [array of class references](SOUNDNESS-RUNTIME.md#arrays-of-class-references) charged to the heap budget; a short budget is the model's `allocationFailure`. |
| `ldlen` | Partial | Length of a supplied integer, enum, reference-free aggregate or integer-vector array, including one loaded from a [value-array field](SOUNDNESS-RUNTIME.md#value-array-fields), or typed handler table, returned as a native integer. Null raises `System.NullReferenceException`. Also the length of an [array of class references](SOUNDNESS-RUNTIME.md#arrays-of-class-references). |
| `ldelema` | Partial | Checked element reference into a supplied integer, enum, reference-free aggregate or integer-vector array. The type token must match the array element type; null and bounds checks precede address formation. Grants no read/write authority and does not make uninitialized contents readable. References retain allocation lifetime across locals, calls and returns. Rejected by name on an array of class references, whose element slots hold references. |
| `readonly.` | Partial | Immediately precedes an admitted `ldelema`; branches into the following address instruction are rejected. Produces a restricted reference that remains readonly through byref locals, arguments and returns. Scalar and field reads are allowed and field addresses and element or byte offsets keep the restriction, while stores, field stores and adapters that would discard the restriction fail. Other authorized aliases can still update the backing bytes. |
| `ldelem.i1`, `ldelem.u1`, `ldelem.i2`, `ldelem.u2`, `ldelem.i4`, `ldelem.u4`, `ldelem.i8`, `ldelem.i`, `ldelem` | Partial | Checked integer array reads; narrow loads extend according to the opcode. Typed `ldelem` also supports validated aggregate and integer-vector tokens, matching the exact array element identity and width; it is rejected by name on an array of class references. Scalar reads require initialized bytes; aggregate/vector snapshot reads retain initialization masks. All reads require read authority. `ldelem.i` and typed `ldelem` also select typed entries from supplied handler tables. |
| `ldelem.ref`, `stelem.ref` | Partial | Element loads and stores of an [array of class references](SOUNDNESS-RUNTIME.md#arrays-of-class-references). Null raises `System.NullReferenceException`, then an index read unsigned at or past the length `System.IndexOutOfRangeException`; a store then raises `System.ArrayTypeMismatchException` when the stored instance's class does not derive from the element class, and null is always storable. Elements of an array of a class outside the model are opaque references. Storing a value whose runtime type is not a class, such as an array, is unsupported. |
| `stelem.i1`, `stelem.i2`, `stelem.i4`, `stelem.i8`, `stelem.i`, `stelem` | Partial | Checked integer array stores; narrow stores truncate. Typed `stelem` requires a matching integer, enum, aggregate or integer-vector token and is rejected by name on an array of class references. Stores require write authority; scalar stores initialize the selected element, while aggregate/vector stores preserve snapshot initialization masks. |
| `ldc.i4`, `ldc.i4.s`, `ldc.i4.m1`, `ldc.i4.0` to `ldc.i4.8` | Complete within the admitted model | Push the encoded 32-bit integer constant. |
| `ldc.i8` | Complete within the admitted model | Push the encoded 64-bit integer constant. |
| `ldnull` | Partial | Push the one object null for truth tests, identity comparison with class instance references, stack shuffles/discard, or a supplied supported array, typed handler-table or [class instance](SOUNDNESS-RUNTIME.md#class-instances) slot/call/return. Other object-typed values and object-null/managed-pointer mixtures are unsupported. |
| `ldstr` | Partial | Push the object the caller bound to the literal's text in `Memory.literals`; an unbound text stops as unsupported. Memory is unchanged. The value is an opaque [string](SOUNDNESS-RUNTIME.md#string-literals): passed, stored, compared for identity and tested against null, never read. Inside a folded `throw new E(...)` it emits `nop`. A text containing a surrogate, backspace or form feed is rejected. |
| `nop` | Complete within the admitted model | Advance without changing the stack or memory. |
| `dup`, `pop` | Complete within the admitted model | Duplicate or discard a supported stack value; stack underflow fails. |
| `ldarg`, `ldarg.s`, `ldarg.0` to `ldarg.3` | Partial | Load admitted argument values; struct instance methods have a managed-reference `this` at index zero, and instance methods of admitted classes an object-reference `this`; a `string` argument is an opaque object reference (see [class instances](SOUNDNESS-RUNTIME.md#class-instances)); narrow integers are truncated and sign- or zero-extended to `i32`. Reference values undergo validity checks. |
| `starg`, `starg.s` | Partial | Assign a private parameter home using its declared storage type. Narrow stores truncate; byref assignment changes the private reference slot. Does not overwrite the caller's by-value source. |
| `ldarga`, `ldarga.s` | Partial | Address the same private parameter home read by `ldarg` and written by `starg`. Addresses expire when the frame returns. Taking the address of a byref parameter is rejected; nested-reference storage is unsupported. |
| `ldloc`, `ldloc.s`, `ldloc.0` to `ldloc.3` | Partial | Load admitted scalar, vector, aggregate or managed-reference locals. Narrow integers are sign- or zero-extended to `i32`; initialization and lifetime rules apply. |
| `stloc`, `stloc.s`, `stloc.0` to `stloc.3` | Partial | Store values compatible with the declared local storage kind; narrow integer locals truncate an `i32` to their physical width. No general object or reference-bearing aggregate storage. |
| `ldloca`, `ldloca.s` | Partial | Form a checked reference to byte-backed local storage. Taking the address of a managed-reference local is explicitly unsupported. |
| `neg` | Partial | Wrapping negation of an `i32` or `i64`; the signed minimum maps to itself. No floating-point or reference operands. |
| `add` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values, plus the mixed native/int32 cases described above. Also accepts a checked reference and an int32 or native integer byte offset in either operand order, preserving allocation identity and its readonly restriction and checking lifetime and bounds when forming the result. Supplied immutable native handler tables also admit checked byte-offset addition. No floating-point operands or arbitrary numeric address fabrication. |
| `sub` | Partial | Wrapping scalar subtraction; also subtract an int32/native byte offset from a checked reference, preserving its readonly restriction, or compute the native byte difference of two live references within one allocation. Null, cross-allocation differences and invalid resulting positions fail. |
| `mul` | Partial | Wrapping arithmetic on two `i32` values or two `i64` values, plus the mixed native/int32 cases described above. No floating-point or reference/pointer operands. |
| `div`, `div.un`, `rem`, `rem.un` | Partial | Same-width `i32`/`i64` quotient or remainder. Signed quotient truncates toward zero; signed remainder follows the dividend sign. Zero divisors fault. Signed minimum with divisor -1 faults for both signed operations under the admitted runtime assumption. No floating-point, mixed-width operands or exception handlers. |
| `add.ovf`, `sub.ovf`, `mul.ovf`, `add.ovf.un`, `sub.ovf.un`, `mul.ovf.un` | Partial | Checked signed/unsigned arithmetic on same-width `i32`/`i64`. Compute the mathematical integer result, then reject values outside the destination range with a located overflow fault. No floating-point, reference arithmetic or exception handlers. |
| `and`, `or`, `xor`, `not` | Partial | Bitwise operations on `i32`/`i64`; binary operands must have the same width. |
| `shl`, `shr`, `shr.un` | Partial | Shift an `i32`, `i64` or native integer by an `i32` or native integer count, masked modulo the value width under the admitted runtime. `shr` is arithmetic; `shr.un` is logical. Native counts normalize to their low 32 bits; ordinary `int64` counts and reference operands are rejected by extraction and its certificate. |
| `conv.ovf.i1`, `conv.ovf.u1`, `conv.ovf.i2`, `conv.ovf.u2`, `conv.ovf.i4`, `conv.ovf.u4`, `conv.ovf.i8`, `conv.ovf.u8`, `conv.ovf.i`, `conv.ovf.u`, and each corresponding `.un` form | Partial | Checked conversion from `i32`/`i64`, preserving the mathematical value or producing a located overflow fault. `.un` interprets the input as unsigned; the destination controls the accepted range. Narrow results occupy `i32`; native destinations use the validated 64-bit profile. No floating-point or reference conversions. |
| `conv.i4`, `conv.u4` | Partial | `i64` to low 32 bits; `i32` identity. No floating-point or reference conversions. |
| `conv.i1`, `conv.i2` | Partial | Truncate an `i32` or `i64` to eight or sixteen bits, then sign-extend to an `i32` stack value. |
| `conv.u2` | Partial | Truncate an `i32` or `i64` to sixteen bits, then zero-extend to an `i32` stack value. |
| `conv.u1` | Partial | Low eight bits of an `i32` or `i64`, zero-extended to an `i32` stack value. |
| `conv.u8` | Partial | Zero-extend `i32` to `i64`, or preserve an `i64`. |
| `conv.i8` | Partial | Sign-extend `i32` to `i64`, or preserve an `i64`. No floating-point or reference conversions. |
| `conv.i` | Partial | Sign-extend an integer `i32` to the admitted 64-bit native width, or preserve an `i64`. No pointer/reference or floating-point conversion. |
| `conv.u` | Partial | Model native unsigned integers as 64-bit: zero-extend `i32`, or preserve `i64`. Does not convert a managed reference to an integer address. |
| `clt`, `clt.un`, `cgt`, `cgt.un`, `ceq` | Partial | Same-width `i32`/`i64` comparisons, returning `i32` zero or one. `clt` and `cgt` are signed; `.un` comparisons are unsigned. `ceq` additionally supports checked reference equality, identity of class instance references and exact closed `typeof` reference results as described below; `cgt.un` tests a class instance reference against null; `clt.un` and `cgt.un` additionally order live references within one allocation. Signed reference ordering is unsupported. No floating-point/unordered comparisons. |
| `br`, `br.s` | Partial | Unconditional branch to an admitted instruction boundary, including backward edges and self-loops. |
| `switch` | Partial | Pop an `i32` unsigned table index; branch to its target or fall through when outside the table. Empty and duplicate-target tables are supported. Every encoded target must be a valid instruction boundary and fold entry. Known int32 selectors prune untaken arms; otherwise every arm and the fallthrough participate in dependency and stack analysis. |
| `sizeof` | Partial | Push the validated storage width as `i32` for admitted integer types (including Boolean/char), same-assembly explicit- or sequential-layout reference-free aggregates, or the integer vectors listed below. Native integers use eight bytes under the validated profile. Closed same-assembly generic structs require validated sequential layouts. No reference types, floating-point or unsupported generic layouts. |
| `brfalse`, `brfalse.s`, `brtrue`, `brtrue.s` | Partial | Zero/nonzero tests of `i32` or `i64`. Also accepts checked references, including readonly references and null. Admitted forward and backward successors. |
| `blt`, `blt.s`, `bge`, `bge.s`, `bgt`, `bgt.s`, `ble`, `ble.s` | Partial | Signed comparison of same-width `i32`/`i64`, branching to admitted forward or backward targets. |
| `blt.un`, `blt.un.s`, `bge.un`, `bge.un.s`, `bgt.un`, `bgt.un.s`, `ble.un`, `ble.un.s` | Partial | Unsigned comparison of same-width `i32`/`i64` or two live references within one allocation, branching to admitted forward or backward targets. Cross-allocation reference ordering is unsupported. |
| `beq`, `beq.s`, `bne.un`, `bne.un.s` | Partial | Equality/inequality of same-width `i32`/`i64`, branching to admitted forward or backward targets. Also supports checked reference equality and exact closed `typeof` reference comparisons as described below. No floating-point comparison. |
| `ldind.i`, `stind.i` | Partial | Native-width integer load/store through checked managed references; eight bytes on the admitted target, with the same allocation, permission and lifetime checks. A native handler-table cursor also supports authenticated pointer loads through `ldind.i`; stores to these immutable tables are unsupported. |
| `ldind.i8`, `stind.i8` | Partial | Eight-byte integer load/store through a checked reference. Allocation bounds, permissions, initialization and lifetime rules apply; arbitrary numeric addresses are not accepted. |
| `ldind.i1`, `ldind.u1`, `ldind.i2`, `ldind.u2`, `ldind.i4`, `ldind.u4` | Partial | One-, two- or four-byte integer loads through a checked reference. Signed narrow loads sign-extend and unsigned loads zero-extend to `i32`; both four-byte forms return the same `i32` bits. Aggregate snapshots and numeric addresses are rejected. |
| `stind.i1`, `stind.i2`, `stind.i4` | Partial | Store the low one, two or four bytes of an `i32` through a checked reference. Allocation bounds, write permissions and lifetime apply; adjacent bytes remain unchanged. |
| `ldfld`, `ldflda`, `stfld` | Partial | Fields in same-assembly, validated explicit- or sequential-layout, reference-free value types, and `Item1`/`Item2` of an equal-width primitive `ValueTuple<T1, T2>` (see [value tuples](SOUNDNESS-RUNTIME.md#value-tuples)). Supported field storage is `sbyte`, byte/Boolean, `short`, `ushort`/`char`, 32-bit integer, 64-bit integer, native integer, integer-backed enum or nested reference-free aggregate. Nested snapshots and assignments copy all field bytes, including padding. Narrow stores truncate; narrow loads sign- or zero-extend to `i32` according to field metadata. `ldfld` accepts an aggregate byte snapshot or reference, including a readonly reference; `ldflda` of a readonly reference yields a readonly field reference, and `stfld` through one faults as unwritable. On an admitted [class instance](SOUNDNESS-RUNTIME.md#class-instances), `ldfld` and `stfld` access integer, Boolean, Char and enum fields of its class or any base, fields typed as a class or an array of a class (opaque when the class is outside the model), and [value-array fields](SOUNDNESS-RUNTIME.md#value-array-fields) typed as a single-dimensional array of integers, Booleans, chars, enums, reference-free structs or integer vectors; a null receiver throws `NullReferenceException`. `ldflda` on a class and other class field types are rejected. No other managed objects, auto-layout structs or static fields through these opcodes. |
| `ldobj`, `stobj` | Partial | Load/store admitted integer types through checked references, with narrow truncation/extension derived from the validated type token. Also copy validated aggregates of 1 to 65,536 bytes or admitted Vector128/256/512 integer values, retaining initialization masks. No general objects, reference-bearing storage or floating-point tokens. Native-integer tokens use eight-byte storage. `ldobj` of an admitted span type copies the view addressed by the immediately preceding argument, parameter-address or local-address load; span `stobj` is rejected. |
| `cpobj` | Partial | Copy validated integer, aggregate or admitted Vector128/256/512 integer storage through checked references. Requires initialized readable source and writable destination; self-copy is supported, partial overlap is rejected. No reference-bearing or floating-point tokens. |
| `initobj` | Partial | Zero the validated width of an admitted integer type, same-assembly explicit- or sequential-layout aggregate, or admitted Vector128/256/512 integer value. A checked `ldloca; initobj` pair resets an admitted span local to its empty view. Byte initialization leaves neighboring storage unchanged. No managed-object initialization. |
| `ldsfld` | Partial | Value of a same-assembly `static readonly` integer, enum or reference-free struct field that its static constructor fixes, with the declaring type named by `--assume-initialized` (see [static readonly values](#static-readonly-values)). An integer or enum field whose stored value extraction cannot compute is read from the caller's static binding instead (see [unknown readonly values](#unknown-readonly-values)). System.Runtime's `BitConverter.IsLittleEndian` is the profile constant `true`. Other static fields are rejected. |
| `ldsflda` | Partial | Address of validated same-assembly static readonly RVA data, or a constructor-initialized readonly value under the initialization assumption. Uses identity-keyed immutable storage with checked write denial. See [static span tables](#static-span-tables) and [static readonly values](#static-readonly-values). Not arbitrary static fields or mutable global state. |
| `call` | Partial | Acyclic calls to supported static methods, reference-free struct instance methods (including direct constructor calls) or instance methods and constructors of admitted classes, which run the named body on an object-reference `this` ([class instances](SOUNDNESS-RUNTIME.md#class-instances)), in the same assembly or a pinned `--reference` assembly ([CLI](CLI.md#extract-from-referenced-assemblies)), concrete generic-method specializations, or exact runtime/intrinsic signatures in the allowlist, including integer BinaryPrimitives byte-span transfers and no-read span/array accessors. Closed generic declaring types are admitted for static calls, including nested owners; validated closed sequential structs also admit direct instance methods and constructors. No arbitrary external calls, instance methods of classes that are not admitted or virtual dispatch through `call`. |
| `newobj` | Partial | Same-assembly constructors of validated reference-free structs: zero-initialize caller-owned storage, invoke the constructor with managed-reference `this`, then return a checked value snapshot. Also admitted `Span<T>` and `ReadOnlySpan<T>` constructors over checked existing storage for supported integer, enum, aggregate and integer-vector elements, from a single reference, `(void*, int)`, an array, or `(array, start, length)`. Also constructors of admitted non-abstract classes, which allocate a fresh [class instance](SOUNDNESS-RUNTIME.md#class-instances) charged to `Memory.heapBudget` (`allocationFailure` when short) and push it once the constructor returns; the constructor's `System.Object::.ctor()` call only pops its receiver. Unsupported generic constructors and cyclic dependencies are rejected. |
| `ldtoken` | Partial | A type token as an operand of a decided closed type test, which emits a no-op, or a static data field token for `RuntimeHelpers.CreateSpan<T>`, which emits the field's address (see below). Other tokens are rejected. |
| `throw` | Partial | Exact `throw new E(...)` with `ldstr`/`ldnull` arguments raises a located `thrown "E"` fault. Adjacent `ldnull; throw` raises `System.NullReferenceException`. Other throws are rejected. |
| `constrained.`, `callvirt` | Partial | Adjacent prefix and `callvirt` (instance slot) or `call` (static interface slot) resolving to a concrete struct implementation or, for a static slot, the most specific interface-level body, within the extracted and pinned assemblies; see [constrained struct calls](#constrained-struct-calls). No boxing. Without the prefix, `callvirt` of a non-virtual method of an admitted class calls it after a receiver null check that throws `System.NullReferenceException` ([class instances](SOUNDNESS-RUNTIME.md#class-instances)); `callvirt` of a virtual method of an admitted class dispatches on the receiver's runtime type through a table Lean rechecks ([virtual dispatch](SOUNDNESS-EXECUTION.md#virtual-dispatch)). Interface calls and slots declared outside the extracted assemblies are rejected by name. |
| `castclass`, `isinst` | Partial | Test an object reference against an admitted class other than `System.Object`: null passes, and an instance whose lineage lacks the class gives null (`isinst`) or throws `System.InvalidCastException` (`castclass`); see [class instances](SOUNDNESS-RUNTIME.md#class-instances). Interfaces, `System.Object`, value types and classes that are not admitted are rejected by name. |
| `ldftn` | Partial | Exact static same-assembly managed method addresses, retaining scoped identity and closed signature. Callable values have no numeric address representation. See typed indirect dispatch below. |
| `calli` | Partial | Static default-managed signatures over admitted integer/enum, reference-free aggregate and integer-vector values, and managed references to these types. The pointer must identify an authenticated catalog entry with the exact signature. Ordinary indirect calls select a forward target; tail calls permit cycles. Supplied immutable native tables also admit checked byte offsets and `ldind.i` with authenticated target provenance. No unmanaged conventions or arbitrary numeric targets. |
| `tail.` | Partial | Adjacent `tail. call ret` or `tail. calli ret` with exactly its arguments and optional function pointer on the stack and the same return type. Retires caller storage before entering the callee and revalidates argument lifetimes. Admitted same-assembly transfers may form cycles; virtual, imported and intrinsic tail calls are unsupported. |
| `ret` | Partial | Return from an admitted method with exactly zero or one result according to its signature. Narrow integer results are truncated and sign- or zero-extended to `i32`. The checked model validates returned references and rejects references that escape expired local storage. |
| `initblk`, `cpblk` | Partial | Managed references and unsigned 32-bit counts; checked block alignment and access rules. Nonempty overlapping copies are rejected. |
| `unaligned.` | Partial | Values 1, 2 and 4 before supported ordinary or block memory accesses; malformed prefix sequences and interior branch targets are rejected. |
| `localloc` | Partial | Frame-owned storage within an explicit per-activation quota; checked initialization, alignment and expiry. See [dynamic stack allocation](#dynamic-stack-allocation). |

## Typed indirect dispatch

Managed function pointers can be held in typed locals or supplied as parameters. Supplied
immutable single-dimensional handler tables support `ldlen` and `ldelem.i`; each entry has one
exact signature and must name a non-null catalog target. A null table raises
`NullReferenceException`, and an invalid index raises `IndexOutOfRangeException`.

The catalog holds closed same-assembly `ldftn` targets and already extracted methods with
matching signatures. An open address such as `&Algo<TGas>.Run` in a generic body is catalogued
only through a specialized body that takes it, so a supplied table can reach a generic target
only if some extracted body takes that closed address. Each entry binds the scoped metadata
identity, generic arguments and program index to an extracted body, and pointer identities
survive linking. Supported signatures have primitive integer, enum, reference-free aggregate or
integer-vector parameters and results, managed references to those types, and void results.
Closed generic structs keep their exact scoped identity, and calling conventions are checked
exactly.

Supplied immutable `nint*` tables admit byte-offset addition in either operand order, `ldind.i`
and native target locals. Offsets are int32 or native integers; other scalar types are rejected.
An explicit binding identifies the static allocation and authenticated catalog identities;
numeric bytes alone cannot establish callable provenance
([struct instance calls](SOUNDNESS-RUNTIME.md#struct-instance-calls)). Loads check bounds,
eight-byte alignment, initialization and read authority; a one-past reference can be formed but
not loaded. Each body requires one exact supported managed indirect-call signature; handler
signatures carrying native table pointers are not supported.

Table allocation, updates, null entries, pointer fields and numeric-address conversions are
not supported, so mutable raw-pointer dispatch tables are not supported. All-tail cycles are
supported; mixed ordinary/tail recursive graphs may be rejected. Tail cycles consume ordinary
execution fuel; admitting a cycle neither proves termination nor makes exhaustion successful.

## Dynamic stack allocation

`localloc` accepts an unsigned int32 or native byte count as its sole stack operand. It creates
fresh allocation-relative storage owned by the current activation. The caller supplies
`Memory.stackLimit`, a per-activation quota up to 65,536 bytes; its default is zero. Each nonempty
request charges its size rounded to 16 bytes. Insufficient quota produces a distinct
`stackAllocationFailure`; a zero request returns null and consumes no quota.

The raw method's `localsinit` flag controls zero initialization. Otherwise bytes remain unreadable
until written. Checked pointer offsets, typed loads and stores, and admitted span construction
retain allocation bounds and authority. Returning a reference or span into expired stack storage
fails. Numeric address fabrication and general pointer casts are unsupported.

The quota is a deployment premise; it does not measure the physical stack. Ordinary frame and
call overhead are outside it; see
[the soundness boundary](SOUNDNESS-EXECUTION.md#definitions-and-proved-properties).

## Reference observations

Reference truth tests and equality check lifetime and formation but need no read authority or
initialized bytes, and readonly references keep their write restriction. Equality within one
allocation compares offsets, and interior references into separate allocations are unequal.
Cross-allocation comparisons involving an end sentinel are rejected, and comparing invalid or
expired references fails, even when both operands are identical. The reason and the runtime
address premise are in [reference observations](SOUNDNESS-EVIDENCE.md#reference-observations).

An `ldnull` object is tracked separately from managed references and cannot be stored or passed
as a managed pointer. `Unsafe.NullRef<T>` values are managed references and can take part in
reference comparisons. Numeric zero never becomes a reference.

The managed-reference overloads of `Unsafe.AreSame`, `IsAddressLessThan` and
`IsAddressGreaterThan` use these checked comparisons. Ordering and
`Unsafe.ByteOffset(origin, target)` require two live references in the same allocation;
`Unsafe.ByteOffset` returns the native-width byte displacement from origin to target.
`Unsafe.AddByteOffset` and `SubtractByteOffset` accept `nint` or `nuint` offsets.
`Unsafe.Subtract<T>` accepts `int`, `nint` or `nuint` element offsets for admitted scalar,
aggregate and vector storage. Scaling and subtraction wrap at the native 64-bit width, and the
resulting reference must still be live and in bounds. These operations grant no read or write
authority. The pointer overloads `Unsafe.Add<T>(void*, int)` and
`Unsafe.Subtract<T>(void*, int)` are described under [runtime calls](#runtime-calls-and-simd).

Pointer parameters and locals admit `char` and validated same-assembly integer-enum elements
alongside supported integer, vector and reference-free aggregate storage
([integer enums](SOUNDNESS-RUNTIME.md#integer-enums)). Boolean, floating-point, nested-pointer
and reference-bearing pointees are unsupported.

## Block memory and alignment prefixes

`initblk` takes a value whose low eight bits it writes; `cpblk` needs initialized, readable
source bytes. Both take checked managed references and an unsigned 32-bit byte count, and need
writable destination bytes in reference-free storage. Every nonempty overlapping copy, including
an exact alias, is rejected because CLI overlap behaviour is unspecified. Zero counts access no
memory and permit null references. The lifetime, bounds and authority checks are in
[arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory).

Unprefixed block operations require eight-byte alignment. Model-owned 32-bit and 64-bit scalar
local and parameter homes have four- and eight-byte alignment, so aligned block access can
succeed on a 64-bit scalar home; aggregate, vector and narrow homes have byte alignment. An
immediately preceding `unaligned. 1`, `2` or `4` selects that requirement. A branch cannot enter
between a prefix and its instruction, and prefix combinations with unsupported modifiers are
rejected.

`unaligned.` is also accepted before supported integer `ldind.*`/`stind.*`, `ldobj`/`stobj` and
`ldfld`/`stfld`. These accesses already use byte alignment, so the prefix lowers to a no-op and
bypasses no safety check.

The exact managed-reference and pointer overloads of `Unsafe.InitBlock`, `InitBlockUnaligned`,
`CopyBlock` and `CopyBlockUnaligned` use these same operations. Pointer arguments must come from
admitted allocation-relative references; arbitrary integer addresses are unsupported. The
certificate binds each helper's exact signature, operation and alignment.

## Pointer subtraction and ordering

Pointer subtraction uses byte offsets, signed int32/native displacements and native-width
wrapping arithmetic, followed by the usual formation checks. The difference of two references
in one allocation is native integer bits; `clt.un`, `cgt.un`, `blt.un`, `ble.un`, `bgt.un` and
`bge.un` (including short branches) compare allocation-relative offsets. Both operands must be
non-null, live and well formed; a declared end position is allowed without granting byte access.
Cross-allocation differences and orderings, numeric-minus-pointer and signed reference orderings
are unsupported. `sub.ovf.un` is scalar-only.

## Unsupported opcodes

Supplied arrays admit `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`,
`nint`, `nuint`, `bool`, `char`, admitted enums, validated reference-free aggregates and
supported integer Vector128/256/512 elements over existing storage
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)). Indexing
checks null before bounds; on a valid non-null array, negative and out-of-range indices raise
`System.IndexOutOfRangeException`. Reading the length needs no readable contents. Admitted
reference-free arrays with element sizes from 1 to 65535 bytes can also be allocated with
`newarr`. Array-root address-taking, object identity tests of value arrays, floating-point
elements and reference elements outside [arrays of class
references](SOUNDNESS-RUNTIME.md#arrays-of-class-references) are outside this subset.

Extraction rejects every opcode outside the translated-opcode table. The table below lists
examples of rejected opcodes and forms.

| Area | Examples rejected by extraction |
| --- | --- |
| Debugger and prefixes | `break`, `volatile.`; `tail.` outside admitted same-assembly calls; `readonly.` outside the checked array-element subset; `constrained.` outside the checked struct-call subset |
| Other conversions | Floating-point conversions |
| Other indirect/block memory | `ldind.ref`, floating-point `ldind.*`, `stind.ref`, floating-point `stind.*` |
| Objects, arrays and metadata | `ldstr` of a text containing a surrogate, backspace or form feed, `box`, `unbox`, `unbox.any`, `castclass` and `isinst` of interfaces, `System.Object`, value types or classes that are not admitted, byref-like, floating-point and non-class reference `newarr`, floating-point `ldelem.*`/`stelem.*` and `ldelem.ref`/`stelem.ref` outside arrays of classes, interface and `object` arrays, `ldtoken` of a method or of a type outside a decided type test |
| Static field values | `stsfld`, `ldsfld` and `ldsflda` of fields outside the admitted readonly subset |
| Dispatch and exceptions | Unconstrained `callvirt` of interface methods, of methods declared outside the extracted assemblies, or of virtual methods whose hierarchy the table cannot close, `jmp`, `ldvirtftn`, `throw` outside a folded throw, `rethrow`, `leave`, `leave.s`, `endfinally`, `endfilter` |
| Floating-point constants | `ldc.r4`, `ldc.r8` |

### Type tests

Closed `typeof(A) == typeof(B)` and `!=` tests use two adjacent
`ldtoken; call Type::GetTypeFromHandle` pairs followed by `Type::op_Equality` or
`op_Inequality`, with exact `System.Runtime` signatures. The four operands emit `nop`
and the comparison emits its decided Boolean. `ReferenceEquals(typeof(A), typeof(B))`
used as a Boolean value ends in operandless `ceq`, which emits the same decided Boolean.
Its negation uses the ordinary integer comparison of that result with zero. Reference-equality
branches use the same operands followed by short or long `beq` or `bne.un`; they emit
an unconditional branch to the original target or a fallthrough `nop`. No instruction
slots are inserted. Feature and scalar certificates share the selected successor.

Types are equal when their metadata is identical, and different when their full names
differ; one full name in two scopes, decorated names and `void` stay undecided. Every
encoded target must be valid, even when unselected. Undecided tests, instructions
between the five, entry into the last four, other `System.Type` members and `Type`
values in locals are rejected. A direct `Object.ReferenceEquals` call is
outside this subset.

### Throws

`throw new E(...)` compiles to one `ldstr` or `ldnull` per constructor argument, `newobj` of
`E`'s constructor and `throw`. For an exact allowlisted `System.Runtime` constructor, the loads
and `newobj` emit `nop` and `throw` emits `.throw "E"`, which ends execution with a fault located
at the `throw`. A `[DoesNotReturn]` helper containing only this pattern is an ordinary call.
Other arguments, any instruction between the parts, a branch past the first part, rethrowing a
stored exception and exception handlers are rejected.

The adjacent `ldnull; throw` form emits `nop` followed by the same named-fault operation for
`System.NullReferenceException`, located at the raw `throw`. A branch may target the null load,
but cannot enter at the throw. Nulls passed through locals, arguments or intervening instructions
do not satisfy this exact fold.

In addition to the admitted string constructors, `Exception`, `InvalidOperationException`,
`ArgumentException` and `ArgumentOutOfRangeException` admit a message with a null inner exception.
`ArgumentException` also admits message, parameter name and null inner exception;
`ArgumentOutOfRangeException` admits parameter name, null actual value and message.
Only the thrown type is observed. Constructor signatures and null operands are checked
independently; expressions with effects or faults are not discarded. Prefix recognition inspects
at most four loads.

### Constrained struct calls

An adjacent `constrained. T; callvirt` pair supports a concrete, reference-free struct `T` and a
method declared on that struct or a directly implemented interface. `T`, the slot's interface and,
for an interface-level body, every interface of `T` must be declared in the extracted assembly or a
[pinned reference](CLI.md#extract-from-referenced-assemblies), in any combination, so a caller's
struct may implement a slot of a referenced interface. An interface of any other assembly is never
read for dispatch, so a body that needs it is rejected.
Closed sequential generic structs admit direct slots and directly implemented interface slots,
including closed generic interfaces. The slot's closed declaring owner must match exactly.
Implicit implementations must uniquely match the public name and signature; explicit `MethodImpl`
overrides take precedence and retain the closed interface owner as well as the method token.
Slots with [`in` parameters](#in-parameters-of-virtual-members) match only implementations
that carry the same modifier.
Closed generic helpers can use a directly implemented closed interface constraint.
The original managed-reference receiver is passed to the resolved implementation, so mutations
remain visible to the caller without boxing.

A `constrained. T; call` pair dispatches a static virtual interface member, such as an operation
or flag struct selected by a type argument. The slot must be static and virtual on an interface,
possibly generic such as `I<T>`, that the struct `T` implements directly. A closed generic struct
such as `G<uint>` dispatches through the interface its `InterfaceImpl` names, instantiated at its
type arguments, so `struct G<T> : IScale<T>` implements `IScale<uint>`, and the selected
implementation or interface-level body is closed at those arguments. In the runtime's order,
the target is `T`'s explicit `MethodImpl` override, else the unique public static method of `T`
with the slot's name and signature, else the most specific interface-level body. The candidates
for that last step are the slot's own body (a C# `static virtual` member) and every interface
`MethodImpl` of the slot (a derived interface's `static R I.M(...) => ...`) on an interface of
`T`. The winner is the candidate whose interface inherits every other candidate's, so the
deepest derived interface's body is selected, and it may supply the body of a base
`static abstract` slot. Two unrelated interfaces that both override the slot leave no winner,
and a winner that re-abstracts the slot leaves no body; both are rejected, as is an abstract
slot with no implementation. The winner is instantiated at its own closed interface and the
site's method type arguments. A public same-signature method of `T` without a `MethodImpl`
beside a slot body is ambiguous and rejected. Interface-level selection requires every interface
of the receiver, including inherited ones, to be listed on it and declared in an extracted or
pinned assembly, so no candidate is unseen. The slot may be a generic method: the site's method
type arguments must be closed and match its arity, and the selected override or body is
instantiated at them. The call passes no receiver. `callvirt` never dispatches a static slot and
`call` never dispatches an instance slot.

The Lean certificate resolves the dispatch again from serialized metadata of the pinned
assemblies ([extraction evidence](SOUNDNESS-EVIDENCE.md#independently-checked-extraction-evidence),
[pinned referenced assemblies](SOUNDNESS-EVIDENCE.md#pinned-referenced-assemblies)). A branch
cannot bypass the prefix. Reference receivers, boxing fallbacks, inherited dispatch, instance
default-interface methods, generic instance methods on interfaces and receivers left open after
specialization are unsupported. Unconstrained virtual calls on classes use
[virtual dispatch](SOUNDNESS-EXECUTION.md#virtual-dispatch).

A static Boolean getter used as a compile-time flag selects code the way the JIT does: when a
plain `call` or the resolved target of `constrained. T; call` takes no parameters, returns
`System.Boolean` and its own feature certificate shows the same 0 or 1 at every reachable `ret`,
the pushed word feeds the [feature-flow analysis](#runtime-calls-and-simd) and the block it rules
out is emitted as unsupported placeholders, so code there is never translated or validated. The
getter may compute its word from other flag getters, type tests and feature tests, as in
`=> A.IsActive && !B.IsActive` or `=> TFlag.IsActive || typeof(TFlag) == typeof(Forced)` in a
closed generic type; a getter supplied by a derived interface folds the same way. The call itself
is still emitted and executed. Lean reads the word from the callee's certificate, which the
callee's own obligation validates. A getter that reads a static field or an untracked value, a
tail call, a call cycle and a call to an imported method leave both edges live.

### Static span tables

`Span<T>` and `ReadOnlySpan<T>` over the eight fixed-width integer types, `nint`, `nuint`,
`char`, `bool`, admitted same-assembly enums, validated reference-free structs and supported
integer Vector128/256/512 types are admitted as by-value parameters and reusable locals.
Length, indexing, slicing and readonly conversion keep the element width and allocation
lifetime. `MemoryMarshal.CreateSpan` and `CreateReadOnlySpan` form views over existing storage.
Forming a view, or a reference from one, keeps the backing allocation, lifetime and readonly
capability, allocates nothing, neither reads nor initializes bytes and grants no byte-access
authority; other writable aliases can still update a readonly view's memory
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)). Slicing
checks signed input ranges and permits an empty view at the allocation end. General ref structs
are outside this support; see [span reference parameters](#span-reference-parameters) for `in`
and `ref readonly` spans.

Aggregate span widths come from the validated target-specific layout, including vector-field
alignment; vectors use their exact storage width. Indexing yields a checked element reference
for typed loads and stores. Single-reference constructors form one-element views over live
storage, and pointer constructors take an explicit int32 length; both accept primitive, enum,
aggregate and integer-vector elements. Opaque values and numeric addresses cannot fabricate
references.

`Span<T>.Empty` and `ReadOnlySpan<T>.Empty` return a null, zero-length view with the element
width and readonly capability of the span type. Explicit `default` initialization or
reassignment of a span local accepts the exact `ldloca; initobj` pair, including resetting a
nonempty local; the initialized type must match the local, and branches cannot enter at
`initobj`.

Span `IsEmpty` and `GetPinnableReference` do not read the view's bytes. An empty span's
pinnable reference is null, and readonly views return readonly references.
`MemoryMarshal.GetReference<T>(Span<T>)` returns a writable span's start reference, including
for an empty span. The `ReadOnlySpan<T>` overload returns a reference restricted as `readonly.`
results are, although .NET types it `ref T`: reads and field reads through it succeed and stores
fault as unwritable. An empty readonly view also yields its own validated reference, and a read
through it is checked against the allocation. Static data spans also accept the overload.
`MemoryMarshal.GetArrayDataReference<T>` supports all admitted array elements: an empty array
keeps its data reference, and a null array raises `NullReferenceException`.

Array constructors, implicit array conversions and the array overloads of
`MemoryExtensions.AsSpan` form views over supplied integer, enum, aggregate and integer-vector
arrays. Enum views keep their exact enum identity through locals, slices, calls and returns;
equal-width enums are not interchangeable. `AsSpan` accepts a whole array, a start index, or a
start and length. A null array produces an empty span only for a zero range; an invalid range
raises `ArgumentOutOfRangeException`. Non-array `AsSpan` overloads are unsupported.

In-place construction of a span local accepts `ldloca`, up to three simple argument loads or
integer constants, and its exact constructor call. The address cannot escape or be duplicated,
and control flow cannot enter the sequence after its first instruction. The local may be
reused or reinitialized; construction faults remain at the call instruction.

`Array.Fill<T>(T[], T)` and its `(T[], T, int startIndex, int count)` overload support primitive
integers, Boolean, character and integer-backed enums. A null array throws
`ArgumentNullException` before range checks; a negative index or count, or a range outside the
array, throws `ArgumentOutOfRangeException`. Empty ranges, including at the array end, need no
write authority. Reference-bearing, aggregate and vector elements are not supported.

`Span<T>.Clear` initializes the whole view, including aggregate and vector elements. `Fill`
repeats a captured primitive, enum, aggregate or integer-vector value; unspecified
low-lane-only vector values are rejected. A filled aggregate or vector snapshot keeps its
initialization mask, so unknown bytes stay uninitialized. Both need write authority but not initialized or
readable destination bytes, access no bytes for an empty span and preserve neighbouring bytes,
including other slices of the same allocation. Readonly views do not admit these members.

`MemoryMarshal.AsBytes` and `Cast<TFrom,TTo>` reinterpret admitted integer, enum, aggregate
and integer-vector spans without copying or reading their bytes. The result length is the source
byte extent divided by the target element width, rounded down; a length above `int.MaxValue`
raises `OverflowException`.

`CopyTo` and `TryCopyTo` copy from a writable or readonly source span to a writable destination
span of the same element type. They capture the initialized, readable source bytes before
writing, so either overlap direction and exact aliases are supported. A short destination
raises `ArgumentException` or returns false without reading or writing bytes. Empty copies need
no byte access; nonempty copies need write authority and preserve neighbouring bytes.

`MemoryMarshal.Read<T>`, `Write<T>`, `TryRead<T>` and `TryWrite<T>` transfer admitted integer,
aggregate or integer-vector values through byte spans. Short `Read`/`Write` calls raise
`ArgumentOutOfRangeException`. A short `TryRead` writes initialized `default(T)` to its out
reference and returns false; a short `TryWrite` returns false without reading the input value
or modifying memory. Successful transfers preserve snapshot initialization masks and retain
the checked model's bounds, lifetime and authority requirements. `Vector128.Create<byte>` and
`Vector256.Create<byte>` over a `ReadOnlySpan<byte>` are the same checked `Read` of the vector.

A collection-expression property such as `static ReadOnlySpan<uint> Table => [...]` compiles to
`ldtoken <field>; call RuntimeHelpers::CreateSpan<uint>` over a static data field (`ldsflda`
rules, packing 1, 2, 4 or 8, with an RVA that is a multiple of the packing, inside one section's
raw data, in a section whose virtual address and file offset agree modulo 8 so that flat and
mapped loads keep the alignment). The span covers the whole field and has `size / sizeof(T)`
elements, for any primitive integer `T`. As in CoreCLR, which throws `ArgumentException` for data
misaligned for `T`, `sizeof(T)` must divide the field's packing; otherwise the call is an
`unsupported` fault. Roslyn emits each such field with packing `sizeof(T)` at an 8-byte-aligned
RVA, in a section whose virtual address and file offset are multiples of 512. A caller reads it
as `stloc s; ldloca s; [index;] call get_Item` or `stloc s; ldloca s; call get_Length`: the store
and address emit `nop`, so the span stays on the stack as the receiver. `get_Item` faults with
`System.IndexOutOfRangeException` at the call when the index, compared unsigned as in .NET, is
out of range. `MemoryMarshal.GetReference` also accepts these spans. The fold is used only for a
single-use receiver with a single-load or constant index; other supported uses keep typed span
storage. Branches into a folded receiver are rejected.

### Span reference parameters

`in` and `ref readonly` parameters of an admitted `Span<T>` or `ReadOnlySpan<T>` type receive
the referenced view, as `ldloca` and `ldarga` of a span local or parameter do. Callers pass a
span local, span parameter or temporary by address, and callees read the length, index, slice,
copy or forward the reference to another readonly span parameter. The view keeps its element
width, write capability and allocation, so element writes through `in Span<T>` still need write
authority, and expired backing storage faults where the argument is passed
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)).

The callee cannot replace the caller's span: `starg` or `ldarga` of the parameter, span
`stobj`, `initobj` or `cpobj` outside the checked local reset, and copies from anything but a
directly loaded span address are rejected. `ref` and `out` span parameters, span references
in locals, returns, fields and imported signatures are unsupported.

A generic specialization keeps its definition's parameter flags and attributes, so a closed
generic helper's `in` and `ref readonly` span parameters follow the same rules, and its `ref`
span parameters are rejected.

### `in` parameters of virtual members

C# encodes an `in` parameter of a virtual, abstract or interface member, and of its explicit
implementations, as `T& modreq(System.Runtime.InteropServices.InAttribute)`. The modifier is
admitted only directly on a by-reference parameter and only with the exact `System.Runtime`
scope, and the parameter then behaves as a non-virtual `in` parameter of the same type: an
ordinary reference, or the referenced view for an admitted span type (see
[span reference parameters](#span-reference-parameters)). Selectors, recorded signatures,
specialization keys and constrained-slot matching keep the modifier. A method whose declaring
type also has a modifier-only twin is rejected
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)).
`modopt`, other `modreq` types, the modifier on a by-value parameter, inside the reference or on
a return, and an `InAttribute` from any other scope are rejected. Imported and exported contract
signatures admit no modifier.

### `init` accessors

C# marks an `init` accessor by returning
`System.Void modreq(System.Runtime.CompilerServices.IsExternalInit)`, and the accessor runs as
the void method it is, as an entry or behind a call. The modifier is admitted only directly on
`System.Void`. Like C#, the extractor recognizes the marker by its full name from any assembly,
so a library that declares its own `IsExternalInit` for an older framework is admitted too.
Selectors, recorded entries and the Lean signature string keep the modifier; a method whose
declaring type also has a modifier-only twin is rejected
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)).
`modopt`, other `modreq` types, an `IsExternalInit` in another namespace and the modifier on a
value-returning method or a parameter are rejected with the modified type in the message. An
`init` accessor cannot be exported, since contract exports are static methods.

### Static readonly values

A same-assembly `static readonly` field is read as a fixed value when its static constructor
stores it exactly once and its declaring type is named by `--assume-initialized`. The admitted
initializers are a checked helper call, a copy of an earlier field, a direct integer literal and
a direct struct construction, described in that order below.

`public static readonly Word256 One = 1ul;` compiles to
`ldc.i4.1; conv.i8; call op_Implicit(ulong); stsfld One` in the static constructor. A reachable
`ldsfld` of such a field emits `.staticValue bytes`, which pushes the field's value as an
aggregate and touches no memory. The static constructor must store the field exactly once,
unconditionally (no control flow before the store and no branch back to it). A helper-call
initializer uses a same-assembly static call whose arguments are integer constants (`ldc.i4*`,
`ldc.i8` with `conv.i4`/`conv.u4`/`conv.i8`/`conv.u8`/`conv.i`/`conv.u`). A field may instead
copy (`ldsfld G; stsfld F`) such a field stored earlier, as in `MinValue = Zero`. The called
method and its callees become part of the extracted program and must not access static fields.
The static site records the call, and the extraction certificate reruns it in the checked
interpreter;
`Extracted.translation_valid` fails unless the result is exactly the emitted bytes.

Primitive integer fields (including Boolean, Char and 64-bit native integers) and same-assembly
integer enums also admit a direct integer literal, optionally widened with the supported integer
conversions. They may instead use the same checked helper-call initializer or copy an earlier
field of the same type. Loads truncate to the declared storage width and sign-extend signed
8-/16-bit fields, and Lean binds the load width and signedness to the raw field type. Mutable
fields, address-taking during initialization, repeated stores and conditional initialization
are rejected.

Direct `new T(integer constants)` initialization is also admitted for same-assembly
reference-free structs, including closed generic structs stored on nongeneric declaring types.
Closed constructors use the ordinary checked generic specialization. How Lean checks each stored
value, and what the initialization assumption covers, is in
[static storage](SOUNDNESS-RUNTIME.md#static-storage).

`ldsflda` of an admitted readonly field uses the same identity-keyed immutable storage as RVA
data. Repeated accesses share one allocation; distinct fields remain distinct even when their
bytes agree. The reference can be passed to supported helpers and instance methods. Checked
writes through it fail, including writes through `Unsafe.AsRef`.

Extraction rejects a declaring type without the assumption; aggregate values built by other code
shapes; a second store, a store outside the static constructor, or `ldsflda` of the field during
initialization; and `stsfld` in an extracted method.

#### Unknown readonly values

An integer, Boolean, Char or enum field that passes the same store checks, but whose stored value
comes from code extraction does not evaluate (such as a hash seed drawn from
`RandomNumberGenerator`), is admitted as fixed but unknown. Its static site has
`opaqueValue := true`, no initializer and zero placeholder bytes that give only the width.
`StaticValuesValid` requires exactly that shape
([static storage](SOUNDNESS-RUNTIME.md#static-storage)).
`ldsfld` reads the field from the caller's static binding for its identity, with the field's
width and signedness, and faults as `unsupported` when the caller's memory has no binding. The
placeholder is never read, so a proof about the method holds for whatever value the binding
holds and cannot fix a particular one. `Memory.boundStatics` in
[StaticBindings.lean](../CIL/Safety/StaticBindings.lean) builds caller memory that binds chosen
values; [OpaqueSeeds.lean](../Examples/Proofs/OpaqueSeeds.lean) proves a seeded hash for every
pair of seeds. Symbolic values stop evaluation, so such proofs use `with_unfolding_all rfl` or
stepping rather than plain `rfl` evaluation. `ldsflda` of an unknown field is rejected, as are
aggregate fields whose value cannot be computed. Each such field is listed in
`opaqueStaticValues`.

## Runtime calls and SIMD

SIMD and hardware features enter compiled CIL mostly through `call`, rather than dedicated SIMD
CIL opcodes. [SIMD](SIMD.md) lists the admitted vector and hardware-intrinsic overloads with
their element types and profile requirements, and links the extractor sources that define them.
The portable bitwise and equality forms admit no floating-point equality and no observation of
[unspecified lanes](SOUNDNESS-RUNTIME.md#unspecified-vector-lanes).
Supporting one overload or CPU feature does not mean the entire API is supported.

Reachable same-assembly generic methods are specialized for supported primitive, enum,
reference-free aggregate and vector type arguments. Specialization substitutes types in the
original CIL parameters, locals, type operands and nested generic calls; it does not replace
method bodies with functional summaries. Repeated uses share a specialization, and different
type arguments get separate bodies. Extraction rejects more than 256 distinct specializations.

Select a non-generic entry method whose compiled calls supply the concrete type arguments, or
close a generic entry with `--type-argument`: a primitive integer, or a non-generic value type
of the selected module that specialization then validates like any other argument. Typed
contract imports admit only primitive integer arguments, since they bind across assemblies.
Static calls on closed same-assembly generic declaring types support nested owners and combined
owner/method type arguments. Closed same-assembly sequential generic structs admit reference-free
storage, field accesses, direct instance methods and constructors after substituting their
owner arguments. Every specialized body's instructions undergo the normal validation.

Generic methods and generic struct owners admit a closed same-assembly interface constraint
when the concrete struct directly declares that exact interface. Generic methods, including
static methods of generic interfaces, also admit an interface constraint naming their own type
parameters, such as `where T : struct, I<T>`: the certificate closes it at each instantiation's
arguments and requires the struct to declare the closed interface directly. Dispatch follows the
[constrained struct-call rules](#constrained-struct-calls). Unconstrained parameters and admitted
value-type, default-constructor and unmanaged constraints support the reference-free value
types above.

Explicit/auto generic layouts, reference-containing instantiations, reference constraints,
open interface constraints on generic struct owners, inherited interface matching, boxing and
general runtime dispatch are unsupported. Runtime members called on a type built from the
helper's own type parameters, such as `ReadOnlySpan<T>.Length`, `Slice` or its indexer in a
generic method or on a generic (including nested) owner, are admitted: the open call target
spells the owner with ECMA-335 parameter positions (`ReadOnlySpan`1<!!0>`, `<!0>`), and the
certificate substitutes that owner segment of the identity, and nothing else, exactly as the
runtime instantiates it. Owner arguments must be primitive, enum, aggregate or integer-vector
types with ASCII names. Generic runtime methods such as `MemoryMarshal.GetReference<T>` keep one
identity and are checked.

`Unsafe.SizeOf<T>()`, the managed-reference `Unsafe.Add<T>` overloads with `int`, `nint` or
`nuint` offsets, and the pointer `Unsafe.Add<T>(void*, int)`/`Unsafe.Subtract<T>(void*, int)`
overloads use validated layouts for supported integer primitives, enums, reference-free structs
and supported Vector128/256/512 types. Sizes include managed packing and padding; offsets scale
by that size and wrap at the validated native width. Forming the resulting reference checks
allocation identity, lifetime and bounds, including admitted one-past positions, and grants no
read or write permission; an offset from a readonly reference stays readonly, so stores through
it fault ([pointer element offsets](SOUNDNESS-RUNTIME.md#pointer-element-offsets)). Classes,
pointer/byref type arguments and unsupported layouts fail extraction.

`Unsafe.SkipInit<T>(out T)` admits the same storage types. It validates the managed reference
and leaves memory, initialization flags and access permissions unchanged, so reads of the output
still require initialized bytes. Extraction evidence checks the exact runtime call identity and
its translation to `skipInit`.

`Unsafe.NullRef<T>()` and `Unsafe.IsNullRef<T>(ref readonly T)` admit the same
storage types. `NullRef` pushes the model's null managed reference, which a
byref local or argument can hold like any other reference. `IsNullRef` returns
1 for it and 0 for every other reference, live or not, without accessing memory.
Every load, store, copy, initialization or field access of one or more
bytes through null faults with `nullDereference`, the model's
`NullReferenceException`, and no address is formed from it; zero-length block
operations access nothing. Extraction evidence binds each call to its operation in both
directions, as for `SkipInit`.

Reference `add` admits either operand order, matching the
[.NET 10 importer](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/importer.cpp#L5093-L5106);
see its table row. Reference sums, ordinary int64 offsets and reversed reference subtraction are
unsupported.

The runtime allowlist also includes specific `Unsafe.AsRef`, `Unsafe.As`, `Unsafe.BitCast`,
`MemoryMarshal.GetReference` and span constructor signatures. These signatures are narrow
translations into reference, memory or vector operations; they do not make those classes
supported as a whole.

Managed byte-reference and pointer `Unsafe.ReadUnaligned<T>` and `WriteUnaligned<T>` support
admitted integer, aggregate and integer-vector storage. They are the typed loads and stores
with byte alignment, keeping bounds, lifetime, access authority and snapshot initialization
masks. Readonly source references are accepted; writes require writable references and byte
authority. Pointer overloads require allocation-relative references, not numeric addresses.
`Unsafe.Read<T>(void*)` and `Write<T>(void*, T)` reuse those checked transfers after an alignment
check. Primitive integers require their storage width; aggregates require their computed layout
alignment, including packing. Integer vectors conservatively require alignment to their full byte
width. This subset can reject vector addresses that a particular runtime accepts; the unaligned
overloads remain available. Alignment checks do not repeat the per-byte authority scan.
`Unsafe.AsRef<T>(void*)` preserves that provenance and forms a live reference without reading or
initializing bytes or granting access authority. Reference-bearing value types are unsupported.

`Unsafe.BitCast<TFrom,TTo>` is admitted between equal-size validated unmanaged aggregates and
`Vector128`/`Vector256`/`Vector512` values with `byte`, `int`, `uint`, `long` or `ulong`
elements, in both directions and under the scalar profile. Byte snapshots keep their
initialization flags through the cast
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)), so numeric
reads and vector arithmetic cannot consume unknown bytes of a partially initialized result.

`CIL.Safety.ValueBitCasts` supplies byte/vector round-trip lemmas and
`bitcastValue_preserves_snapshot`; `CIL.Safety.SnapshotMemory` supplies checked snapshot
write/readback facts. Access witnesses in `AccessAlignment` distinguish initialized reads/writes
from snapshot copies, which preserve flags instead of asserting initialization.

Reachability is evaluated under the chosen feature profile, and instructions it excludes are
emitted as unsupported placeholders
([feature getters and profiles](SIMD.md#feature-getters-profiles-and-execution-restrictions)).
Execution that reaches a placeholder fails.

Exact `IntPtr.Size`, `UIntPtr.Size` and `System.Environment.Is64BitProcess` getters produce `8`, `8`
and `true` ([runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions)).
`ldsfld BitConverter.IsLittleEndian` produces `true`, since every valid profile is
little-endian. The extractor checks the exact System.Runtime field and that it is
`static readonly`, and rejects same-named types and fields from other assemblies and other
`BitConverter` fields. The certificate binds the raw call signature, or the raw field owner, type
and static load, and the emitted value. Raw field operands carry no member name, so the
certificate relies on
`IsLittleEndian` being the only static Boolean field of System.Runtime's `BitConverter`.

These constants feed the feature-flow analysis. Known int32 words propagate through bitwise
operations and `ceq`, `cgt`, `cgt.un`, `clt` and `clt.un`.
Single-condition branches and all short/long signed or unsigned comparison branches select an
edge when their operands are known. Unknown operands, including native and int64 values, keep
both edges; joins and backedges discard conflicting constants. A known int32 switch selector
chooses its indexed arm, or falls through when its unsigned value is out of range. Unknown
selectors retain every successor. Every encoded branch or switch target remains bounds-checked
and must enter a folded sequence or tail transfer at its start, even when unselected.

`RuntimeHelpers.IsReferenceOrContainsReferences<T>()` produces `false` for supported primitive
integer, Boolean, character, integer-enum and integer-vector types and for reference-free
aggregate layouts, including padded and closed generic ones, and feeds the same branch analysis.
A validated byref-like aggregate without reference or byref fields is admitted; classes, arrays,
spans, byref/pointer arguments and unsupported storage are rejected. What the query does and
does not establish is in [runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions).

## Implementation sources

The implementation this inventory describes is:

- [InstructionTranslation.cs](../Extractor/InstructionTranslation.cs): opcode translation and
  default rejection.
- [MetadataValidation.cs](../Extractor/MetadataValidation.cs),
  [Reachability.cs](../Extractor/Reachability.cs) and [StaticData.cs](../Extractor/StaticData.cs):
  type, call, control-flow and static-data restrictions.
- [Semantics.lean](../CIL/Semantics.lean): scalar operand cases and conversions.
- [Execution.lean](../CIL/Safety/Execution.lean), [Frames.lean](../CIL/Safety/Frames.lean),
  [InstructionMemory.lean](../CIL/Safety/InstructionMemory.lean) and
  [StaticMemory.lean](../CIL/Safety/StaticMemory.lean): checked execution, local storage and
  memory behaviour.

See [validation](VALIDATION.md) for the suites that test it and [soundness](SOUNDNESS.md) for
the runtime assumptions and trusted base.

## Portable scalar runtime helpers

The helpers in the table below are exact `call` signatures and add no CIL opcodes. They work with
every admitted hardware profile.

| Runtime type | Supported methods and overloads | Semantics |
| --- | --- | --- |
| `System.Numerics.BitOperations` | `RotateLeft` / `RotateRight` on `uint`, `ulong` or `nuint`, with `int` count | Circular rotation, count modulo 32/64, including negative counts |
| Primitive integer types | Static `RotateLeft` / `RotateRight` on `int`, `uint`, `long`, `ulong`, `nint` or `nuint`, with `int` count | The same 32/64-bit rotation semantics, including signed inputs and negative counts |
| `System.Byte`, `System.UInt16` | Static `RotateLeft` / `RotateRight`, with `int` count | Input truncates to 8/16 bits; count is modulo the width, including negative counts; result is zero-extended to `i32`. |
| `System.Numerics.BitOperations` | `PopCount`, `LeadingZeroCount`, `TrailingZeroCount` on `uint`, `ulong` or `nuint` | `int` result; zero has 32/64 leading/trailing zeros |
| `System.Int32`, `System.UInt32`, `System.Int64`, `System.UInt64`, `System.IntPtr`, `System.UIntPtr` | Static `PopCount`, `LeadingZeroCount`, `TrailingZeroCount` | Result retains the input's integer type; zero has 32/64 leading/trailing zeros. Native integers use the validated 64-bit target. |
| `System.Byte`, `System.SByte`, `System.UInt16`, `System.Int16` | Static `PopCount`, `LeadingZeroCount`, `TrailingZeroCount` | Input truncates to the declared width; count results retain the input type and use `i32` stack values. Zero has 8/16 leading/trailing zeros. |
| `System.Byte`, `System.UInt16` | Static `Log2` | Input truncates to the declared width; result retains the input type, represented on the CIL stack as `i32`. |
| `System.Numerics.BitOperations` | `IsPow2` on `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | True for positive powers of two; false for zero and signed negative values |
| Primitive integer types | Static `IsPow2` on `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | The same signedness-aware power-of-two test, returning `bool`; narrow arguments truncate before interpreting the sign bit. |
| `System.Numerics.BitOperations` | `Log2` on `uint`, `ulong` or `nuint` | Floor base-two logarithm as `int`; zero input returns zero |
| `System.UInt32`, `System.UInt64`, `System.UIntPtr` | Static `Log2` | Floor base-two logarithm in the input's integer type; zero input returns zero. |
| `System.Numerics.BitOperations` | `RoundUpToPowerOf2` on `uint`, `ulong` or `nuint` | Least power of two at least the input; zero for zero input or overflow |
| `System.Buffers.Binary.BinaryPrimitives` | `ReverseEndianness` on `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | Reverse bytes within the value; preserve signed return conventions; byte/sbyte are identity operations |
| `System.ArgumentNullException` | `ThrowIfNull(object, string)` | Raises `ArgumentNullException` for a null argument and otherwise pops both operands; the parameter name is never read |
| `System.ArgumentOutOfRangeException` | `ThrowIfZero`, `ThrowIfNegative`, `ThrowIfNegativeOrZero`, `ThrowIfEqual`, `ThrowIfNotEqual`, `ThrowIfGreaterThan`, `ThrowIfGreaterThanOrEqual`, `ThrowIfLessThan`, `ThrowIfLessThanOrEqual` on `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`, `nint` or `nuint` | Raises `ArgumentOutOfRangeException` exactly when the integer test holds, comparing unsigned types as unsigned, and otherwise pops its operands; see [argument guards](SOUNDNESS-RUNTIME.md#argument-guards) |

Signed 8/16-bit rotations and primitive signed `Log2` are unsupported.

`System.Math.Min`, `Max` and `Clamp` support signed and unsigned 8-, 16-, 32-, 64-bit and native
integers. `Abs` and `Sign` support the signed types; `Sign` returns an `int`. `Abs` of the
signed minimum produces an arithmetic overflow fault. `Clamp` with a lower bound greater than
its upper bound produces an invalid-bounds fault. These failures terminate checked execution;
exception handlers are not modelled.

The corresponding static `Min`, `Max` and `Clamp` methods on `sbyte`, `byte`, `short`,
`ushort`, `int`, `uint`, `long`, `ulong`, `nint` and `nuint` use the same operations.
Signed types also admit `Abs` and `Sign`, with the same overflow behavior and `int` sign result.

`System.Math.BigMul(ulong, ulong, out ulong)` returns the high 64 bits of the unsigned product
and writes the low 64 bits through the checked output reference. The destination must be live,
in bounds and writable; its previous bytes need not be initialized. `CIL.Safety.bigMul64_succeeds`
exposes the exact result, low-word readback, allocation preservation and preservation of cells
outside the output's eight bytes.
`Math.BigMul(long, long, out long)` writes the same low word and returns the signed high word
`CIL.WideMultiply.signedHigh64`; `signedHigh64_decomposition` proves that the high word's signed
value times `2^64` plus the low word's unsigned value is the exact `Int` product, and
`CIL.Safety.bigMul64_signed_succeeds` gives the same memory guarantees as the unsigned overload.
`Math.BigMul(int, int)` and `Math.BigMul(uint, uint)` return the exact product as a `long` or
`ulong` stack value; they never fault.

`System.Math.DivRem(T, T)` returns `(T Quotient, T Remainder)` for `sbyte`, `byte`, `short`,
`ushort`, `int`, `uint`, `long`, `ulong`, `nint` and `nuint`. The result is an aggregate with
Item1 at offset 0 and Item2 at the element width. Extraction requires the recomputed equal-width
`ValueTuple<T, T>` layout to match that shape. `Math.DivRem(int, int, out int)` and
`Math.DivRem(long, long, out long)` push the quotient and store the remainder through the
checked output reference. The quotient is the CIL `div` of the operands and the remainder is
`left - quotient * right` with wrapping. A zero
divisor raises `DivideByZeroException` and, for `int`, `long` and `nint`, `MinValue / -1` raises
`OverflowException`, both before any output store. The narrow overloads divide in `int` and
truncate, so `sbyte.MinValue / -1` and `short.MinValue / -1` return the wrapped quotient
`MinValue` and remainder 0 rather than faulting. `CIL.divRemBits_signed`,
`divRemBits_unsigned` and `divRemBits_narrow_signed` state the exact quotient and remainder,
and `divRemBits_zero` and `divRemBits_overflow` the faults.

Native-width overloads use the validated 64-bit target. The 128-bit (`Int128` and `UInt128`
`BigMul`), generic-math and other unlisted helper overloads are unsupported. The extractor
validates the exact .NET 11 runtime assembly identity, declaring type, static calling convention
and signature. Correspondence to the runtime's implementation is an assumption; see
[portable bit helpers](SOUNDNESS-RUNTIME.md#portable-bit-helpers).

`BinaryPrimitives.Read{Int,UInt}{16,32,64}{Little,Big}Endian`, their `TryRead` forms,
native-width `IntPtr`/`UIntPtr` counterparts, `Write` forms and `TryWrite` forms, 64 exact
signatures in all, operate on checked byte spans. Reads sign- or zero-extend according to the
named integer type after applying byte order, and writes store exactly that width. Short
ordinary transfers raise `ArgumentOutOfRangeException`; short try-reads write zero to the output
and return false, and short try-writes return false without modifying memory
([arrays, views and bulk memory](SOUNDNESS-RUNTIME.md#arrays-views-and-bulk-memory)).
Floating-point and 128-bit span overloads are not admitted.

### Vector storage and fields

`sizeof`, `initobj`, `ldobj`, `stobj` and `cpobj` admit `Vector128<T>`, `Vector256<T>`
and `Vector512<T>` for `byte`, `int`, `uint`, `long` and `ulong`. Exact type-token
checks bind each operation to its storage width. Loads, stores, parameters and returns
retain initialization masks; using unknown lanes as numeric values is rejected.
`cpobj` requires initialized source bytes even when the token names a vector.

Instance fields support `Vector128<T>` and `Vector256<T>` for `byte`, `int`, `uint`, `long` and
`ulong`. The owner must have a validated, reference-free sequential or explicit layout. Other
vector element types and 512-bit fields are rejected, and auto-layout tuples do not admit vector
fields. Layout computation uses CoreCLR's default packing limit of 64 bytes. `Vector128<T>` has
natural field alignment 16, and `Vector256<T>` has 32 under x64 profiles and 16 under ARM64
profiles; explicit packing caps these values. The checked method profile selects the layout in
both the extractor and the Lean certificate. A scalar profile selects no target architecture, so
it must use an explicit packing limit of at most 16 for `Vector256<T>` fields. Field widths come
from the vector type, and Lean recomputes each field offset
([extraction evidence](SOUNDNESS-EVIDENCE.md#independently-checked-extraction-evidence)).

Field reads and writes use the ordinary byte-aligned access rule, so a packed field does not
require vector-width alignment. Checked accesses keep allocation bounds and initialization
masks. `Unsafe.As` can expose these fields through an admitted struct reference without changing
its address or access bounds.
