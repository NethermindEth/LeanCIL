# Runtime and storage assumptions

## Runtime assumptions

The supported runtime convention is 64-bit, little-endian .NET 10, with fixed hardware capability
flags throughout execution. ISA-specific instructions require their declared features; portable
vector operations use the supplied software semantics. A selected profile describes runtime-visible
availability, including runtime/OS disabling, not merely physical CPU features.

The model assumes admitted `initobj` operations and zero-initialized local storage clear the entire
declared reference-free byte layout, including padding. This target-runtime storage assumption is
not proved against a JIT. Unknown locals remain uninitialized until written.

`Vector128.CreateScalarUnsafe(ulong)` leaves the upper lane unspecified. The checked value
`v128Low64 low` stands for every 128-bit vector whose lane 0 is `low` (`CIL.Vector128Represents`).
`checkedIntrinsic` sends any operand list holding one to `CIL.evalUnspecifiedIntrinsic`, which
admits exactly four consumers and rejects every other intrinsic: `Vector128.As*` reinterpretation
(the result stays unspecified), `GetElement` at index 0, and the count operand of
`Avx2.ShiftLeftLogical`/`ShiftRightLogical`, which reads lane 0 alone.
`CIL.Safety.checkedIntrinsic_unspecified` proves that every successful checked evaluation agrees
with the ISA result on every concretisation of its operands. Every other instruction rejects such
operands before running: `observerCount` and `MemoryOp.argumentCount` name the operands each op
reads, with no default case, and stores, bitcasts, byte homes and argument homes reject them as
well. Only internal forwarders pass them on (`dup`, `pop`, opaque local stores and loads). Returns,
ordinary call arguments and constructor arguments reject them before exposing a result or entering
another method. Stores to caller-visible memory also reject them. Contracts cannot certify a
successful boundary crossing with unspecified lanes; consume the known low lane within the method or
construct a fully defined vector first. Constructor setup lemmas require both checked values and the
absence of unspecified argument bits; concrete arguments discharge the latter automatically.
`invoke_return_known` and `step_call_known` state the fully specified return and call-argument
guarantees. Unaddressed `Vector128<ulong>` locals are `opaque128` slots only in methods whose
reachable code uses `CreateScalarUnsafe`; other methods retain byte homes. This intrinsic is the
only producer of unspecified lanes, reinterpretation only preserves them, and method-boundary guards
reject incoming unspecified arguments. Thus ordinary callees without a reachable producer cannot
obtain unspecified vector values through their arguments. If an external invocation supplies
unspecified inputs directly, byte-home stores still reject unspecified bits. `OpaqueLocalsValid`
checks the emitted producer and recomputes eligible locals from the raw body (no `ldloca`), so
extraction cannot choose the set. Passing an unspecified vector to a private helper in the same
assembly is also rejected, even if the helper would read only lane 0; opaque by-value parameter
homes are not yet supported. That the JIT never exposes the upper lane through these consumers is a
runtime correspondence assumption.

Small integers use `i32` on the evaluation stack. `sbyte` and `short` loads sign-extend;
byte/Boolean and `ushort`/`char` loads zero-extend. Narrow stores truncate. Extracted argument loads
and returns carry narrow type annotations so method boundaries apply the same normalization,
including when a caller omits an explicit conversion. Field instructions retain signedness as well
as their validated width. These rules follow the CLI small-integer storage model. The older
sequential `methodBlock` helper explicitly rejects annotated narrow argument/return instructions;
use `CIL.Safety.invoke` for verification.

Ordinary reference-free accesses use alignment 1, for the modeled CoreCLR x64/ARM64 normal-memory
convention. This is not a proof of the portable CLI natural-alignment rule. Aligned APIs,
volatile/atomic instructions, device memory, concurrency, GC relocation internals and arbitrary
object headers are outside the extracted subset. The memory model's relocation results concern
allocation-relative references, not a verified garbage collector.

Primitive indirect loads/stores and integer `ldobj`/`stobj` use those same access checks and one-,
two-, four- or eight-byte storage. They accept managed references, not numeric addresses or
aggregate snapshots. Narrow stores truncate; loads extend according to the opcode or validated type
token. Integer `initobj` zeroes and initializes exactly that storage width. `sizeof` emits a
constant from validated integer widths or validated aggregate layout metadata, under the same layout
correspondence assumption as aggregate memory operations; it is not a model of arbitrary runtime
type layout.

Integer `Vector128<T>`, `Vector256<T>` and `Vector512<T>` storage accepts the already admitted
`byte`, `int`, `uint`, `long` and `ulong` elements. `sizeof`, `initobj`, `ldobj`, `stobj` and
`cpobj` use the exact 16-, 32- or 64-byte type width, independently of ISA availability. The
extraction certificate checks the raw object opcode and exact runtime type identities against the
emitted vector operation and width. Loads and stores retain byte initialization masks through the
existing checked snapshot operations. Typed copies require initialized source bytes and reject
partial overlap; they do not turn unreadable bytes into concrete values. The guards against
observing unspecified SIMD lanes remain in force. Fields admit the same integer elements at 128 and
256 bits using the existing architecture-dependent layout rules. Vector512 fields remain unsupported
because their aggregate alignment is not established by this layout model. These storage forms do
not admit floating-point vector operations or additional vector element types.

`switch` uses unsigned `i32` indexing, with out-of-range indices falling through. Reachability
includes every target and the fallthrough, conservatively even for a constant index. Reachable
backedges are validated by the same fixed-point feature and stack analyses as other branches;
switch-only dependencies and unsupported arms receive the normal validation. These rules follow the
[CLI switch
operation](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.switch); they
do not establish loop termination or admit exception-region transfers.

A null managed reference is a distinct value, not address zero. `Unsafe.NullRef<T>` produces it and
`Unsafe.IsNullRef<T>` compares against it without any access check, as .NET compares the pointer.
Every checked memory instruction faults with `nullDereference` on it, before forming a field or lane
offset; this models the `NullReferenceException` that the runtime raises for an access through a
null byref, under the same runtime correspondence assumption as other faults. The fault is not
`thrown`, so an `OutcomeContract` cannot name it as raised; methods with handlers remain rejected,
so nothing observes it.

Static data is immutable, extraction-bound RVA storage with field identities retained separately
from contents. Static initializers that could execute unmodelled code are rejected.

Supplied one-dimensional integer, enum, reference-free aggregate and integer-vector arrays retain an
element type, length and checked allocation-relative data reference. The runtime correspondence
premise must identify these with the actual array's element type, length and backing bytes;
constructing a model view does not establish that correspondence. Array operations reuse existing
allocation, lifetime, initialization and authority checks. A readonly permission set grants no write
authority, while aliases over the same allocation observe the same bytes. A valid null array raises
the named `System.NullReferenceException`; an out-of-range index on a valid non-null array raises
`System.IndexOutOfRangeException`. Invalid extents, expired storage and missing authority remain
model faults and cannot prove either expected exception. Reference elements, multidimensional arrays
and taking the address of an array root are outside this subset.

`newarr` allocates primitive integer arrays, including native integers, `bool` and `char`, using the
existing fresh-allocation primitive. The payload is zero-initialized and has read/write authority;
its heap identity survives the allocating frame's return. Empty arrays are non-null and have
distinct fresh identities. Negative int32/native lengths raise `System.OverflowException`. The model
admits nonnegative lengths up to `0x7fffffc7`, the .NET 10 CoreCLR element-count ceiling, with
checked native byte extents; larger lengths and allocator consistency failures remain model faults,
not named CLR exceptions. A successful model execution assumes that the runtime supports and can
allocate each requested array. The ceiling follows [the .NET 10
allocator](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/gchelpers.cpp); it does not
establish available heap capacity. Object headers, GC behavior, out-of-memory outcomes and
allocation of enum, struct, vector or reference elements are not modeled. Zero initialization uses a
constant cell function rather than constructing a byte list proportional to the array length.

The scalar certificate checks array opcode families, integer widths, load signedness, native integer
distinctions and typed element tokens against the emitted operations. Aggregate arrays bind the
exact element identity and computed layout width, and integer-vector arrays bind their exact
admitted vector type and width. Typed element loads/stores reuse snapshot transfers, so
uninitialized bytes remain uninitialized instead of becoming concrete values. Array-to-span
conversions and data-reference accessors retain this same descriptor without allocating storage.
Even a null array descriptor must carry a valid positive native-bounded element width; frame
initialization and local stores enforce that condition.

Same-assembly integer-backed enum arrays retain the full assembly/type identity separately from
their underlying integer width and narrow-load signedness. Typed element tokens and array-to-span
factories must match that identity; equal widths do not permit substitution. Enum span metadata
keeps its identity and write capability in scalar-flow states across locals, calls, returns, joins
and backedges. Span storage remains a physical checked view; it does not encode a CLR type tag or
grant additional memory authority. Enum elements reuse the existing initialization, lifetime, bounds
and readonly checks without heap allocation.

For `readonly.; ldelema`, the certificate additionally binds the readonly flag to the immediately
preceding raw prefix and disallows branch entry between the two instructions. Restricted references
keep their tag through argument checks, calls, returns and local stores. A local holding a
restricted reference uses `LocalSlot.readOnlyRoot`; loading it cannot produce an unrestricted
reference. Reads still require initialized readable bytes. Stores through the restricted view fail
even when memory contains write authority, and unsupported reference adapters cannot strip the tag.
This is an access restriction, not an immutability or uniqueness claim: writes through other
authorized aliases remain visible. The subset excludes reference element arrays and their
covariance/type-check behavior.

Generated static identities are unsigned natural numbers from SHA-256 of the full assembly identity
and full field name. The assembly identity text is `Name, Version=a.b.c.d, Culture=<culture or
neutral>, PublicKeyToken=<16 lowercase hex digits or null>`, followed by `, Retargetable=Yes` for a
retargetable name. It is built from the name's components, not from a metadata library's display
string. The field name is Mono.Cecil's `FieldReference.FullName`, `<field type> <declaring
type>::<name>`. A fixed test vector detects a change to either text or to the encoding. Each UTF-8
component is preceded by its byte length as a little-endian 32-bit integer. The hash bytes are
interpreted as one unsigned big-endian number. MVID and method bodies are excluded. No proof assumes
that this hash is injective. Extraction and import checks reject key collisions. Full verification
also proves `linkChecked` for the composed program, so every linked descriptor is compatible there.
The raw `link` function has no collision guarantee.

`StaticWorldValid descriptors memory` constrains cached contents only for the listed descriptors.
`StaticRegistryValid memory` still requires unique keys, distinct allocations and live immutable
storage for every registry entry. Thus another assembly's loaded fields do not make a library world
false. Composition joins descriptor lists over one memory whose shared keys name equal descriptors;
it does not merge memories or infer allocation disjointness from key disjointness.
`StaticIdentitiesAbsent` supplies a public first-use premise only. Repeated calls with loaded fields
use a published `StaticWorldValid` precondition. RVA exports carry a kernel-checked static identity
set in their certification. Import extraction recomputes the selected implementation's reachable
static set at the selected profile. This analysis remains trusted metadata processing, not a proof
of CLR execution or library correctness. Static-value and type-init assumptions are still rejected
by the closed-export producer.

A static readonly integer, enum or reference-free struct field set by its static constructor admits
`ldsfld` and `ldsflda`, under `--assume-initialized` for its declaring type, with value loads
producing a constant scalar or aggregate and address loads resolving immutable field storage. Two
parts are trusted: the extractor's recognition that the constructor stores an integer literal,
`M(constants)`, `new T(constants)`, or a copy of such a field stored earlier exactly once and
unconditionally, and the runtime assumption that nothing writes the field after that store. The
extractor rejects other stores in the module and `ldsflda` of the field in the constructor or its
same-assembly callees, and binds each extracted address to shared immutable storage. Checked writes
through the address fail; writes through reflection or other unmodelled code are excluded by
assumption, as the JIT also treats an initialized `static readonly` field as constant. The value
itself is kernel checked: `StaticValuesValid`, part of `TranslationValid`, reruns `M` on its
recorded arguments from empty memory, with constructor-initialized sites removed so that no
initializer can read a value it justifies, and requires exactly the emitted bytes after
storage-width truncation. Direct struct constructors run through the existing checked
aggregate-construction operation; its zero initialization, lifetime and readback checks determine
the bytes. Direct literal descriptors are checked against their emitted bytes with the same
integer-storage rules; recognizing and faithfully decoding the literal expression remains trusted.
The per-method shape validator binds scalar load width and signedness to the raw field type,
including enum storage. `M` runs under the selected profile, so this also assumes the profile
matches the runtime during initialization. Reports list each such field as a caller assumption next
to the initialization assumption. Unsafe reference arithmetic wraps at the modeled native width and
retains allocation provenance; every resulting reference must pass formation checks. A valid end
sentinel grants no access permission.

## Argument storage

The scalar certificate permits interchange between `word64` and `native` only at a metadata-bound
64-bit local home, argument home or return boundary. Both have the checked interpreter
representation `i64` on the validated 64-bit target. This representation rule does not permit a
mixed native/int64 arithmetic operation, int32 widening, or recovery of numeric width from `other`.

Pointer parameters, locals and results for admitted primitive integers, reference-free aggregates
and integer vectors carry checked allocation-relative references. Raw `void*` remains opaque except
as an allocation-relative reference operand at exact `Unsafe` block-helper, `Read<T>`, `Write<T>`,
`ReadUnaligned<T>`, `WriteUnaligned<T>` and `AsRef<T>` overloads, and supported `System.Runtime` 10
`Span<T>(void*, int32)` and `ReadOnlySpan<T>(void*, int32)` constructors over integer, enum,
aggregate and integer-vector storage. Span-constructor scalar evidence checks the exact declaring
type, external signature, parameter/result metadata, element width and mutability against the
emitted `spanFromReference` operation. The existing `ReadOnlySpan<byte>` constructor retains its
exact `spanCreate` check. Each constructor requires a checked reference and an int32 length; an
opaque value or native integer cannot fabricate a reference through this rule. Other pointer element
types remain unsupported by extraction.

Single-reference span constructors form a one-element view over a checked live reference; readonly
references can construct only readonly views. Both pointer and single-reference constructors
validate the complete extent without requiring byte-read authority. In-place constructor folds
retain the original local and argument positions. Aggregate widths are bound by mandatory layout-use
evidence for both direct and folded constructor calls; primitive/vector widths and write capability
are checked exactly. Constructor analysis is cached by target architecture, so vector-field layouts
cannot reuse another architecture's width.

A raw `stloc` into a validated int32 or narrow integer home with a known `word64` or `native` input
is an explicit terminal `invalidState` case. The checked home store rejects every such `i64` input.
The certificate therefore requires no successful successor from that store; it does not convert the
value or treat later instructions as a successful execution. The rule requires the exact emitted
local index. Unknown values, references and missing or different homes cannot use this exception.
All covered arithmetic and conversion encodings still require their exact checks, including after
the terminal store.


Assigned or addressed parameters receive private frame-owned storage with the declared physical
type. Argument loads, assignment and address-taking share that storage; ordinary by-value calls copy
values into the callee's home. A byref parameter is a private reference slot: assigning it changes
that slot, while writing through it affects the referenced allocation. Addresses of byref slots are
explicitly rejected because nested managed-reference storage is outside the model.

Narrow stores truncate and typed loads extend, following the [starg
rules](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.starg). The
[ldarga
operation](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.ldarga) uses
the existing allocation-relative reference and access checks. All owned parameter homes expire at
return, and returned references are checked after expiration. The original argument list remains
available for untouched parameters; extraction redirects every load of a materialized parameter to
its home. This mapping and the validated storage metadata are part of the extractor trust boundary.

## Sequential struct layout

Sequential layouts are computed for admitted same-assembly value types, including closed generic
structs, containing supported primitive integer, integer-backed enum or nested reference-free
aggregate fields. Generic owners must be closed and sequential; owner parameters are substituted in
the original fields before layout computation. Reference-containing arguments or fields, open
owners, explicit/auto generic layouts and interface/reference-constrained generic structs are
rejected. The kernel layout schema binds the owner, arity, ordered arguments, constraints and
original fields to their substituted layout. Layouts are cached per closed identity and target
architecture. Nested field alignment comes from the validated child layout, capped by the parent
packing; it is not inferred from the child byte size. Field order, packing, declared size and the
validated 64-bit native width determine offsets and size. Default packing is eight; explicit packing
is restricted to the supported powers of two. Inferred sizes include trailing alignment padding,
explicit sizes cannot truncate fields, and empty structs occupy at least one byte. Inline arrays,
auto layout (other than the [value tuples](#value-tuples) below), reference fields and
floating-point fields are rejected transitively. Recursive layouts and nesting beyond 128 active
types fail explicitly.

This models managed storage, not interop marshalling. In particular Boolean and Char retain their
managed widths. Runtime correspondence follows the admitted [.NET 10 sequential layout
implementation](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/classlayoutinfo.cpp),
with independent runtime size/offset probes and execution comparisons. Extracted layouts still carry
kernel-checked bounds theorems; those theorems validate the emitted layout, not the CLR
implementation itself.

## Value tuples

`System.ValueTuple<T1, T2>` from the exact `System.Runtime` 10.0.0.0 reference is the admitted
generic external aggregate layout; closed same-assembly sequential generic structs use their
independently validated definitions. Its metadata declares **auto** layout, not sequential: CoreCLR
[places auto-layout
fields](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/methodtablebuilder.cpp)
largest first, so `(uint, ulong)` stores Item2 at offset 0 and Item1 at offset 8. Auto layout
coincides with sequential placement only when every field has the same width, so only tuples of two
primitive integer type arguments of equal width are admitted; mixed widths, enums, nested aggregates
and other arities are rejected. The raw layout records `auto := true`, and Lean's `computeLayout`
accepts it only for equal-width primitive fields without explicit offsets, packing or declared size,
so the equal-width condition is kernel-checked rather than trusted. The definition is resolved
through Cecil and must be ``System.ValueTuple`2`` in `System.Private.CoreLib` with exactly the
instance fields `Item1 : T1` and `Item2 : T2`. Field operands are serialized with the instance's
type arguments in place of `T1`/`T2`. The ordering rule is a runtime correspondence assumption;
`Tests/TupleDivision.cs` probes the running runtime's offsets for both the admitted and the
reordered shapes and compares returned tuple bytes. Tuple construction (`newobj` of the external
constructor), tuple methods and tuple fields inside other structs remain unsupported.

## Typed copies

`cpobj` uses the validated operand type's byte width and the same checked read/write operations as
other memory instructions. A generic theorem, `CIL.Safety.copyObject_writes_snapshot`, proves that
every byte in a successful destination copy equals its corresponding source snapshot byte and is
initialized. This includes padding in the admitted byte-storage model. Source initialization,
permissions, allocation bounds, lifetimes and GC-sensitive intervals remain checked. Identical
addresses are allowed; partially overlapping ranges are explicitly unsupported.

Runtime comparisons exercise exact `cpobj` instructions emitted with Cecil, including primitive
values, explicit/sequential structs and the admitted vectors. C# assignment commonly emits
`ldobj`/`stobj`; the fixtures deliberately test `cpobj` itself. Runtime agreement for the supported
type/layout profile, including padding, remains an assumption beyond the Lean operational semantics;
these tests are evidence, not a proof of the JIT.

References carry allocation identity and offset, not nominal CLR type tags. Relating a `cpobj` proof
to runtime execution assumes that both references designate storage compatible with its validated
type token, as required by the [opcode
contract](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.cpobj?view=net-10.0).
Byte-level access safety alone does not establish that nominal type compatibility.

## Struct instance calls

The extractor admits direct calls to methods on validated reference-free structs. The implicit
`this` argument is a managed reference, not an aggregate snapshot; field accesses use existing
allocation, permission, initialization and lifetime checks. By-value struct parameters still copy
values into their own frame storage. Parameter assignment/addressing accounts for the shifted
argument indices.

Direct calls to a void instance constructor are allowed on existing struct storage. Such calls do
not allocate an object or bypass initialization checks. `newobj` for admitted structs allocates
zero-initialized caller-owned temporary storage, passes a managed-reference `this` to the
constructor, requires a void return and reads back a checked aggregate snapshot. Constructor calls
propagate arithmetic and memory faults. The temporary remains owned by the caller until frame
cleanup; resource exhaustion is not modelled. Zero-initialized fields follow the CIL construction
contract; correspondence of padding bytes and physical runtime layout remains a runtime assumption.
Direct instance calls and construction also admit validated closed sequential generic structs. Class
instance methods and indirect instance dispatch remain unsupported.

Direct `tail.; call; ret` transfers are admitted for the existing same-assembly managed-call subset.
The certificate binds the prefix to its call and immediate return, requires exactly the call
arguments on the stack, checks the complete callee signature and equal return types, and rejects
branches into the call or return. The checked driver retires the current frame before revalidating
arguments and entering the callee. References or views into that frame's locals therefore fail even
if the callee would ignore them; references to still-live caller storage remain valid. The callee
result returns directly, without a caller continuation. Typed `ldftn`/`calli` values retain a scoped
method identity and exact closed signature. Each possible call target is bound by the certificate to
an extracted body. Linking relocates catalog indices without changing pointer identities. Supplied
immutable handler tables contain non-null identities of one signature; a null table and out-of-range
indexes raise their named exceptions. Integer conversion cannot manufacture callable provenance.

Supplied immutable native tables additionally use a checked static allocation binding and an
explicit array of target identities. Byte-offset arithmetic and `ldind.i` retain that provenance
through native target locals; unrelated native locals remain numeric scalars. Loads require
eight-byte alignment, bounds, initialized readable backing storage and an exact catalog signature.
The target identity is supplied explicitly, never decoded from raw address bytes. The supplied
binding must faithfully describe the runtime slots. Each method body requires a unique supported
managed indirect-call signature; handler signatures carrying native table pointers remain
unsupported. Mutable or dangling backing storage cannot establish a target.

Direct and indirect tail transfers may form cycles, using the same frame-retirement checks.
Execution remains fuel-bounded and termination needs a proof. Only default-managed static signatures
over admitted integers, enums, reference-free aggregates, integer vectors and managed references to
these types are supported. Callable identities normalize layout-table indexes while retaining exact
scoped type names; raw argument and result layouts remain independently checked. Snapshot
initialization masks and ordinary argument/return lifetime checks remain intact. Imported or
intrinsic tail calls, mutable handler tables, null entries, unmanaged conventions and raw
native-integer targets remain unsupported. This does not model arbitrary mutable raw-pointer EVM
tables.

## Integer enums

Same-assembly, non-generic enums use the storage of their validated underlying integer type:
`sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long` or `ulong`. The extractor validates the
`System.Enum` base identity and the single `value__` instance field before normalizing types for
execution. Method signatures retain enum names for artifact identity. Narrow enum loads and returns
use the same truncation and sign/zero extension as their underlying integers; enum fields use that
integer's size and alignment.

All underlying bit patterns are admitted, including values without a named constant and combinations
of flags. This follows the unboxed enum execution model in [ECMA-335, partitions I.8.5.2 and
I.12.1](https://ecma-international.org/wp-content/uploads/ECMA-335_6th_edition_june_2012.pdf). This
does not add boxing, `System.Enum` instance methods, reflection or external enum dependencies.
Metadata validation and its translation to existing Lean integer operations remain part of the
extractor trust boundary.

## Portable bit helpers

`CIL.ScalarIntrinsics` defines rotations using Lean bit-vector rotations, population and zero counts
by enumerating the value's bits, and endian reversal by reversing bytes. `Intrinsic.scalar` reuses
the existing intrinsic dispatch without hardware requirements; profile-equivalence proofs cover this
new family. The finite 32-bit count representation gives the .NET rotation count modulo 32/64,
including negative `int` values.

Integer logarithms use Lean's natural-number `log2`, including zero mapping to zero. Rounding up
constructs the power of two determined by the leading-zero count of the wrapping predecessor;
truncation gives zero for zero input and overflow. Power-of-two checks require a single set bit and,
for signed operands, a clear sign bit. Native overloads use the admitted 64-bit target. Byte-sized
endian reversal preserves the low byte with the declared signed or unsigned extension.

The trust boundary includes correspondence between these definitions and the selected .NET 10
`BitOperations` and `BinaryPrimitives` overloads. Exact signature/scope validation and
boundary/runtime comparison tests support that correspondence; they do not verify CoreCLR or a JIT.
See the [BitOperations
API](https://learn.microsoft.com/en-us/dotnet/api/system.numerics.bitoperations?view=net-10.0) and
[ReverseEndianness
API](https://learn.microsoft.com/en-us/dotnet/api/system.buffers.binary.binaryprimitives.reverseendianness?view=net-10.0).

