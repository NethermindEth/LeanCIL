# Runtime and storage assumptions

<!-- audience: maintainers -->

## Runtime assumptions

Deployment must use the selected supported 64-bit, little-endian .NET 10 profile. Feature flags
describe runtime/OS-visible availability and remain fixed during execution. ISA-specific operations
require their features; portable operations use software semantics. Profile validity is checked,
but the verifier does not discover a deployment's actual CPU, runtime or resource availability.
See [runtime profiles](RUNTIME-PROFILES.md).

`IntPtr.Size`, `UIntPtr.Size` and `Environment.Is64BitProcess` use the profile's required
64-bit process assumption. Their exact getters translate to constants `8`, `8` and `true`;
they do not inspect the verifier host or establish a deployment's actual process width.

`RuntimeHelpers.IsReferenceOrContainsReferences<T>()` returns `false` only for supported primitive
integers, booleans, characters, integer enums and vectors, or a reference-free aggregate admitted
by the layout validator. Closed generic and padded aggregates use that same validator. A byref-like
aggregate is admissible when its validated fields contain neither references nor byrefs; spans,
arrays, classes, open generic arguments and unsupported storage are rejected. The query establishes
neither initialized padding nor memory access, lifetime or escape authority.

The exact runtime signature and generic argument bind the constant independently of extraction.
Feature and scalar certificates receive `rawLayouts.toArray`, including types used only by queries;
the enclosing translation certificate checks the complete layout table. Aggregate queries compare
their index and identity without repeating layout computation. Runtime correspondence assumes the
.NET 10 helper's reference-and-byref classification, rather than inspecting the verifier host.

| Area | Model convention / deployment premise | Excluded claim |
| --- | --- | --- |
| Numeric operations | Bit-vector wrapping; checked arithmetic/conversions use mathematical bounds; signed division truncates toward zero | Floating-point conversion and arbitrary CLI/runtime behavior |
| Native integers | 64-bit representation; metadata-bound native/int32 widening, with zero extension for unsigned checked arithmetic | Native/int64 arithmetic mixtures, numeric fabrication of references |
| Mixed unsigned branches | Native/int32 unsigned conditional branches require explicit conversions | A uniform implicit widening rule: CoreCLR argument/constant provenance can affect the result |
| Signed minimum remainder -1 | Overflow, matching the admitted runtime behavior | Architecture-independent CLI success for that input |
| Ordinary memory access | Alignment 1 on admitted CoreCLR x64/ARM64 normal memory | Portable natural alignment, device memory, volatile/atomic/concurrent execution |
| Initialization | `initobj` and zero-initialized homes clear the full reference-free layout, including padding | Unknown locals being readable before a write |
| Resources | Requested modeled stack/heap storage can be supplied by the runtime | Absence of physical stack/heap exhaustion |

The [native runtime evidence](evidence/native/README.md) records exact CIL, inputs, outputs, runtime
and binary hashes on pinned x64/ARM64 binaries. It is differential evidence; it is neither a CLR
proof nor a reproducible source-to-binary build. Small integers use i32 stack values; narrow
stores truncate and loads/returns sign- or zero-extend by the declared type. Boolean bytes need
not be canonical.

### Pointer element offsets

`Unsafe.Add<T>(void*, int)` and `Unsafe.Subtract<T>(void*, int)` use the same checked,
allocation-relative element offsets as their managed-reference counterparts. Runtime correspondence
assumes .NET 10's native-width multiplication by `sizeof(T)` followed by addition or subtraction.
They admit existing storage for supported integer,
enum, vector and reference-free aggregate types; neither fabricates addresses nor grants authority.
Negative offsets wrap at native width before the resulting reference is checked for lifetime and
bounds. Null and invalid resulting references fail. Exact signature checks bind the pointer overload;
primitive/vector stride and signedness are checked directly, and aggregate stride uses layout evidence.

### Unspecified vector lanes

Portable 128-, 256- and 512-bit integer vector bitwise operators, whole-vector equality, `Zero` and
`AllBitsSet` share their bit-level semantics for byte, signed/unsigned 32-bit and signed/unsigned
64-bit elements. The intrinsic certificate checks the exact runtime call, element, width, generic
arguments and emitted operation. Floating-point equality and unspecified-lane observations are excluded.

`v128Low64 low` represents every vector with that low lane. `checkedIntrinsic` admits only consumers
proved independent of the upper lane: reinterpretation, lane-zero extraction and the count operands
of the admitted AVX2 logical shifts. Reinterpretation preserves uncertainty. Other observations,
byte stores, bitcasts, returns and call/constructor arguments reject unspecified bits. Internal
dup/pop and eligible opaque locals may forward them. `invoke_return_known` and `step_call_known`
state the boundary guarantees; a contract cannot expose an unknown lane as a concrete value.

`OpaqueLocalsValid` requires a reachable admitted producer and independently recomputes eligibility
from raw local uses, excluding address-taken locals. Opaque by-value helper parameters are unsupported.
Agreement between the permitted consumers and the actual JIT remains a runtime assumption.
See [intrinsic semantics and coverage](SIMD.md) and the [runtime-call inventory](COMPILER-COVERAGE.md).

### Arrays, views and bulk memory

Supplied arrays carry exact element identity, length and allocation-relative backing storage.
The caller must relate that descriptor to the runtime array. Primitive integers, enums, admitted
aggregates and integer vectors share checked lifetime, initialization, bounds and authority rules.
Reference-element and multidimensional arrays, covariance and addresses of array roots are excluded.
Valid null/index failures raise their named exceptions; invalid descriptors, expired storage and
missing authority remain model faults and cannot discharge those exceptional contracts.

`newarr` allocates primitive integer/bool/char/native arrays, same-assembly integer-backed enums,
validated reference-free aggregates and supported integer vectors. Enum payloads start at zero
even when the enum declares no zero member. Fresh non-null
identities survive frame return, including for empty arrays. Payloads start zeroed and writable.
Negative lengths raise `OverflowException`; lengths above `0x7fffffc7`, invalid native extents and
allocator inconsistency are model faults. The [CoreCLR ceiling](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/gchelpers.cpp)
does not establish available memory. GC, object headers and out-of-memory behavior are not modeled.

Array component sizes range from 1 to 65535 bytes, matching CoreCLR's
[16-bit component-size field](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/methodtable.h).
Composite payloads have eight-byte base alignment on the admitted 64-bit targets, independent of
element stride: the [array header](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/object.h)
preserves the [GC pointer alignment](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/gc/env/gcenv.base.h).
Vector arrays do not acquire 16-, 32- or 64-byte alignment from their element width. Padding bytes,
like fields, start initialized to zero. Byref-like structs cannot be array elements or fields of
heap-storable structs. The raw byref-like marker is decoded from metadata; faithful decoding and
serialization remain extractor assumptions, while the Lean layout and array checks enforce it.

Spans, slices, array conversions and `MemoryMarshal` views preserve backing identity and capability;
creating a view neither reads/initializes bytes nor grants byte authority. Readonly views permit
other authorized aliases to write. Cast lengths truncate incomplete elements and raise overflow
above Int32.MaxValue. Single-reference constructors require a live checked reference; pointer
constructors require a checked extent, not a numeric address. Raw `void*` is admitted only at exact
supported helpers/constructors. Arbitrary pointer element types and reference-bearing layouts remain
unsupported. [OPCODES](OPCODES.md) specifies the exact constructor and receiver forms.

`MemoryMarshal.GetReference` of a readonly view returns a readonly-restricted reference even
though .NET types the result `ref T`. A write through it faults instead of taking the CLR meaning,
so no proof relies on mutating storage a readonly span exposes. Element and byte offsets from a
readonly reference (CIL `add`/`sub`, `Unsafe.Add`, `Subtract`, `AddByteOffset`) take the writable
reference's allocation, bounds and lifetime checks and stay readonly, so they never regain write
permission. An empty view yields its own validated reference, never null, and any read through
it is still checked against the allocation.

Empty span getters and explicit default resets use null, zero-length views. Their element width
and write capability remain bound to the exact span type; aggregate widths and identities are
checked against the layout table. Resetting a local replaces its view without modifying backing
memory, granting authority or extending a lifetime.

A readonly span reference parameter (`in` or `ref readonly`) carries the referenced view rather
than the address of the caller's span home, as span-local addresses already do. Carrying the view
is sound only because the home cannot change during the call: the extractor rejects `starg` and
`ldarga` of such a parameter, span `stobj`, `initobj` and `cpobj` outside the checked local
reset, `ref` and `out` span parameters, and span references in locals, returns and fields, so no
admitted code can rebind, address or overwrite a span home. The parameter's readonly attributes,
which a generic specialization copies from its definition, and these rejections are trusted
extractor decisions; the Lean validators still bind the raw argument to
a managed reference, reject its address and accept an empty emission for `ldobj` only at a span
type. Loads, stores and comparisons that expect a byte reference fault on a view rather than
reading it as an address.

An `in` parameter of a virtual member carries `modreq(InAttribute)` on its reference. The
modifier has no run-time effect, so the Lean signature types, parameter kinds and dispatch
metadata record the plain reference. The extractor admits only the exact `System.Runtime`
modifier on a by-reference parameter, and rejects an entry, callee or constrained slot whose
declaring type has another method with the same name and signature once the modifier is erased.
No admitted certificate therefore contains two methods that differ only in that modifier. C#
never emits such overloads.

An `init` accessor returns `System.Void modreq(IsExternalInit)`. The modifier has no run-time
effect either, so the Lean method and call metadata record a plain void return, while the
signature string keeps it. The extractor admits the modifier only directly on `System.Void`,
naming `System.Runtime.CompilerServices.IsExternalInit` from any assembly, as C# does; and the
same twin rejection covers a method equal to the accessor once the modifier is erased.

Equal-size aggregate/vector `Unsafe.BitCast` uses the same snapshot representation for validated
`byte`, `int`, `uint`, `long` and `ulong` vector elements. Element signedness does not initialize
unknown bytes or change their bits. Aggregate/vector loads and stores preserve initialization masks.
Fill captures its value before writing, including aliasing cases, and preserves those masks;
Clear initializes every byte.

Whole-array and ranged `Array.Fill<T>` require the exact runtime signature and primitive or
integer-backed enum element identity. Typed array views must describe live, valid storage before
named runtime exceptions can be selected. Valid null inputs fault before range checks; other
inputs delegate to checked span slicing and filling. Range bounds use widened natural arithmetic
over the unsigned int32 arguments, retaining rejection of negative or overflowing ranges. Empty
non-null ranges perform no write. The view supplies no additional memory authority, and the shared span fill
preserves confinement and initialization guarantees. Other element families are not modeled.
Nonempty destinations need write authority, not prior readability. Copy requires initialized source
bytes. Empty operations grant no authority. Empty spans have null pinnable references; empty arrays
retain their data reference. Null array data-reference access raises its named exception.

Block copies require disjoint regions; `cpobj` permits identical addresses but rejects partial
overlap. Nonempty block accesses check lifetime, bounds, permissions, initialization, alignment and
GC-reference exclusion. Block alignment is eight unless a valid `unaligned.` prefix selects 1/2/4.
Zero-byte blocks access no memory, including through null. Prefix operands/followers and entry edges
are validated; correspondence to CoreCLR remains assumed.

`BinaryPrimitives` span operations bind width, endian order, signedness and try behavior exactly.
Native integer overloads use eight-byte transfers under the validated 64-bit deployment profile.
Short ordinary operations raise `ArgumentOutOfRangeException`; short try-reads initialize the output
to zero and short try-writes preserve memory. Reads capture source before writing an aliased output.
These behaviors are runtime-helper assumptions backed by validation; they are not verified
runtime implementations.

### Static storage

RVA storage is immutable and extraction-bound. Static keys hash full assembly/field identities;
hash injectivity is not assumed: extraction/import checks reject collisions, and composed full
verification proves `linkChecked`. Raw `link` alone supplies no collision guarantee.

An RVA field's descriptor alignment is its packing. The extractor checks the RVA, and that its
section's virtual address and file offset agree modulo 8; the runtime premise is that CoreCLR
places the image at an 8-byte-aligned base. Its loader maps or copies images to page-aligned
memory, and the bundler pads single-file assemblies to 64 bytes or more, but a flat image the host
supplies through external assembly probing is used at the host's address, which is assumed to be
8-byte aligned and is not checked.

`StaticRegistryValid` requires unique keys, distinct allocations and live immutable storage.
`StaticWorldValid` constrains the listed descriptors. Composition requires shared keys to have equal
descriptors in one memory; it neither merges memories nor infers disjointness from different keys.
First-use absence and repeated-call world-validity are distinct caller premises.

Constructor-initialized readonly values require named initialization assumptions and no later
unmodeled mutation. Recognizing unconditional permitted initializer stores and faithfully decoding
metadata are trusted. `StaticValuesValid` checks literal bytes or re-executes admitted initializer
computation without circular access to the values being justified. A scalar whose initializer is
not computed is opaque: loads read the caller's binding, so a theorem binds no value the deployment
might not store, and `StaticValuesValid` only checks its width and empty initializer.
Profile-dependent initialization must match deployment. Reflection and other unmodeled writers are
excluded. Reports expose these assumptions; they do not establish that initialization occurred.

## Argument storage

Assigned/addressed by-value parameters have private typed homes; loads, assignment and addressing
share those homes. Byref assignment changes a private root slot; writes through it affect its
referenced allocation. Addresses of byref slots are unsupported. Owned homes expire at return and
returned references are checked after expiry. Extraction binds parameter-home indices to raw uses.

The certificate permits word64/native interchange only at metadata-bound 64-bit storage/returns.
A known i64 store into an i32/narrow home is a terminal invalid-state case and is never a
conversion or successful successor. Unknown values and mismatched homes cannot use that rule.
Null managed references are distinct from numeric zero. Access faults on null are not automatically
named throws; only explicit outcome mappings establish a named exception.

## Class instances

An admitted class is non-generic, derives from `System.Object` in `System.Runtime` directly or
through admitted classes, has sequential or auto layout and no finalizer; an abstract class is
admitted as a type but never constructed. A reference to it is `Value.object`: null, or offset 0
of a live allocation whose kind is `.object` with a runtime type (`formObject`). The runtime type
records the instance's class and its bases, nearest first, up to but excluding `System.Object`
(`RuntimeType.bases`); the class and its bases form its lineage (`RuntimeType.lineage`). Object
references carry no byte position, so code cannot
form one from an integer, a byref or an interior offset, and `ldnull` pushes the one null
object reference; `Unsafe.NullRef` keeps the distinct null byref. `ceq`, `beq` and `bne.un`
compare identities; `cgt.un` and `brtrue`/`brfalse` test presence against null only. Object
locals and parameters are roots without bytes and have no address.

`ldfld` and `stfld` of an integer, Boolean, Char or enum field of a class reach the field's
bytes in the object's allocation (`objectFieldAddress`). The model chooses the layout
independently of CoreCLR: one 8-byte slot per instance field, the fields of the furthest base
first and each class's own in declaration order after its base's (`objectFieldOffset`), so a
field keeps its offset in every derived instance. Lean rechecks the offset against each
instruction's raw field index and type; that the raw index counts the fields of the declaring
class's bases first is metadata the extractor decodes. The model's layout needs no
correspondence with CoreCLR's layout because code cannot observe it: `ldflda` on a class is
rejected, and object references have no integer form. Each access checks that the field's
declaring class is in the allocation's lineage, so a field of a base class is reached on every
derived instance and a field of an unrelated class on none, and a null receiver throws
`NullReferenceException`, as `ldfld` and `stfld` do; a null byref keeps its distinct
`nullDereference` fault.

`newobj` of an admitted class (`.newObject`) checks the constructor's arguments, then allocates
a fresh live instance (`allocateObject`): an allocation of kind `.object` with the class and its
bases as its runtime type, one zeroed 8-byte slot per instance field, inherited fields included,
and authority over all of it. It charges the
instance's size to `Memory.heapBudget`, the bytes the caller grants for objects, and fails with
`allocationFailure` when the budget is short; that fault is a model resource fault and is not a
CLR exception, so no proof of an expected exception can rest on it. The budget never grows back:
it is a conservative bound that ignores collection. The constructor then runs with the
instance as its receiver, and the instance is pushed once it returns. Lean rechecks that the
call site's declaring class is the instance's class, that its bases are those the constructor's
raw method records (`RawMethod.objectBases`), that the constructor takes an object receiver, and
that the size is one slot per instance field of the constructor's class, inherited fields
included. `newobj` of an abstract class is rejected by name, as the runtime rejects it. A derived
constructor's chained call to its base's constructor is an ordinary instance `call` with the new
instance as receiver ([DerivedObject](../Examples/Proofs/DerivedObject.lean)).
Inside an admitted constructor, `call System.Object::.ctor()` with the exact `System.Runtime`
scope only pops the receiver: the runtime's constructor has no effect on an instance, and Lean
rechecks that exact target wherever `.pop` stands for a call. No frame owns
an instance, so leaving the method that created it never expires it: an instance lives as long
as a reference can observe it, which is the reachability the collector maintains.

Memory a caller passes may record any runtime type, so `Memory.WellFormed` alone does not stop
one allocation from claiming two unrelated classes, and fields of two such classes may then
alias. A proof that needs instances of unrelated classes to be different objects states
`Memory.ClassesConsistent (declaredClasses Extracted.methodEvidence) memory` as a premise
([class catalog](../CIL/Safety/ClassCatalog.lean)): each cataloged class in an object's lineage
brings its whole base chain as the lineage's tail, which single inheritance makes true of every
CLR object. The catalog lists the class and admitted bases that each object-receiver method's
metadata records (`RawMethod.owner`, `RawMethod.objectBases`); these are metadata the extractor
decodes, and each extraction's translation certificate covers the evidence that holds them.
Under the premise, `Memory.ClassesConsistent.allocation_ne` separates objects located as
instances of two unrelated cataloged classes.

A caller states the premise once, for its entry memory, and execution keeps it
([execution classes](../CIL/Safety/ExecutionClasses.lean)). Only `newobj` and `newarr` of a class
create instances: `newobj` of the class and bases it records, `newarr` an array of its element
type. Frame homes, statics, value arrays and expiry create none. `ObjectSitesConsistent catalog
program` checks every such site of the program text against the catalog, once per extraction by
`decide`. Given it, `step_preserves_classes`,
`run_preserves_classes` and `invoke_preserves_classes` keep the premise through every step,
nested call and frame exit. Formed calls and constructions hand their continuation the same
fact for the callee's final memory (`ClassesPreserved`, part of `FrameInvariants`). Nothing is
assumed about memory the program cannot produce: the entry premise stays the caller's.

References held by fields are kept apart from bytes: `Memory.slots` records, by allocation and
field offset, the object reference a field holds, and fresh storage holds null. No byte encodes
a reference, so no byte access can forge or observe one. `Memory.WellFormed` requires every
held reference to name an identity already issued, so a later allocation can never make a
dangling reference live; `Confined`, `MemoryBelow`, `Memory.Equivalent` and `Memory.Renamed`
each relate field references alongside bytes, the last through the allocation map.

`ldfld` and `stfld` of a field whose type is an admitted class (`.objectReferenceField`,
`.setObjectReferenceField`) locate the field like a scalar one, so a null receiver throws
`NullReferenceException` and the owner is checked against the runtime type, then check the
field's 8-byte slot for read or write authority inside the object. A load pushes the reference
the slot holds once it forms again (`loadSlot`); a store requires the value to form, that is to
be null or a live object, and changes only that slot (`storeSlot`), so no byte and no authority
changes and every held reference stays issued. The model checks that a stored value is an
object, not that its class is the field's type: that is the verifier's typing, as for arguments,
and an object of another class read back through the field fails its next field access with
the owner check rather than reading another class's fields.

A field whose type is a class outside the model, such as `string`, an interface, a delegate or a
generic or library class, holds its reference in a slot through the same operations
([OpaqueTag](../Examples/Proofs/OpaqueTag.lean)). Its value is opaque: the reference can be
loaded, stored into another such field, compared for identity and tested against null, but no
admitted operation takes its type as a field owner, call receiver, argument, local or result, so
nothing reads through it. Its referent is an object allocation like any other, whose recorded
runtime type the model never inspects. Fields of generic parameter type or a modified type are
rejected, as are fields holding multi-dimensional arrays, whose shape a slot cannot recover from
the allocation it names.

`System.String` of `System.Runtime`, matched exactly, is the one such class that is also admitted
as the type of an argument, a local and a result ([StringValues](../Examples/Proofs/StringValues.lean),
[StringLabel](../Examples/Proofs/StringLabel.lean)). A string is an object reference on the stack
and in a root, typed `.object` with its exact scope and name, so it is passed, returned, stored in
an opaque field, compared for identity and tested against null like any object reference, and
an argument must form like one: null or a live object allocation. No string method is admitted
as a call, so nothing reads its length or characters, and a string root has no address: `ldarga`,
`ldloca` and `string&` are rejected by name, as for class instances. A modified string type is
rejected.

An instance method of an admitted class, virtual or not, is an entry whose receiver `this` is an
object reference and is not a byref. A theorem about a virtual method is about that body, which
a `call` (a base call, or a direct call into it) runs exactly. The raw method records the class
receiver (`objectReceiver`), from which Lean derives the receiver's storage and scalar kind. Lean
rejects the address of the receiver and of any class-typed local or argument, so no byref can
stand in for an object receiver.

`callvirt` without a `constrained.` prefix, which C# emits for every instance call on a class,
is admitted when its target is a non-virtual method of an admitted class. It has exactly one
target, so it is a call (`callInstance`) that first checks its receiver: a null receiver throws
`System.NullReferenceException` at the `callvirt`, in the caller, before the callee is entered
(ECMA-335 III.3.19), and a receiver that is no object reference is ill-typed. Lean admits a
`callInstance` only at `callvirt`, only into a method whose receiver is an object, counting the
receiver among its arguments, and rejects a plain `call` emitted for `callvirt`, which would skip
the check. It also rejects a `callInstance` into a method whose metadata attributes mark it
virtual, since `callvirt` selects such a body by runtime type; the attributes are metadata the
extractor decodes, as it decodes `hasThis`.

`callvirt` of a virtual method of an admitted class is a `callVirtual` whose table names the body
for each class of the extraction's assemblies that derives from the slot's class
([virtual dispatch](SOUNDNESS-EXECUTION.md#virtual-dispatch)). It checks the receiver for null
like `callInstance`, then enters the body listed for the receiver's runtime type, which the
allocation records. Lean admits a `callVirtual` only at `callvirt` and only into virtual methods
with the slot's signature and an object receiver
([AnimalLegs](../Examples/Proofs/AnimalLegs.lean)).

`castclass` and `isinst` of an admitted class other than `System.Object` are an `objectTest` of
that class. It keeps a reference whose runtime type, its own class or one of the admitted bases
the allocation records, is the class, passes null through, and otherwise gives null (`isinst`)
or throws `System.InvalidCastException` (`castclass`) (ECMA-335 III.4.3, III.4.6). Those classes
are the instance's whole lineage below `System.Object`, so the test is exact. For an instance
the method does not construct, the runtime type, class and bases alike, is the theorem's
hypothesis, as for field access and dispatch; one it constructs records its constructor's bases.
Lean admits an `objectTest` only at `castclass` or `isinst` of the same class, on an object reference, and only
against a pinned catalog class that is no interface
([DogTest](../Examples/Proofs/DogTest.lean), [DogCast](../Examples/Proofs/DogCast.lean)).

Interface, generic, explicit-layout and finalizable classes, classes deriving from a class that is
not admitted, `newobj` of an abstract class, byrefs to class
instances, field addresses on class instances, element addresses and typed element accesses
on arrays of class references, class fields of multi-dimensional array, generic parameter,
modified or non-integer value types,
interface calls, virtual calls whose hierarchy the table cannot close or resolve, type tests
against interfaces, `System.Object` or classes that are not admitted, and the address
of a class receiver, local or argument are each
rejected by name during extraction.

An instance of a class with no fields is an allocation of size zero: it costs no heap budget,
has no byte any access could reach, and is still distinct from every other instance, since
identity is the allocation and not an address
([TwoMarkers](../Examples/Proofs/TwoMarkers.lean)).

Object identity, runtime type and field positions are allocation metadata, which byte writes
never change, so distinct object references are distinct allocations and their fields never
share a byte; [object framing](PROOFS-CONTRACTS.md#frame-class-instances) states this for
proofs.

## Arrays of class references

An array of a class `E` is itself a class instance: `.newReferenceArray E` allocates,
through `allocateObject`, an allocation of kind `.object` whose runtime type is `E[]`
(`referenceArrayType`) with no bases, one 8-byte slot per element and nothing else, so its
length is its size over the slot width. Its elements are references held in
`Memory.slots`, as class-typed fields are, and fresh elements are null. The array is charged
to `Memory.heapBudget` like any instance, without the CoreCLR header and length word the model
does not lay out, and a short budget is the model's `allocationFailure`. The length decodes as
`newarr` decodes it for value arrays: a negative `int32` or native length throws
`System.OverflowException`, and one above `0x7fffffc7` is unsupported.

`ldlen`, `ldelem.ref` and `stelem.ref` on such an array (`.referenceArrayLength`,
`.referenceArrayLoad`, `.referenceArrayStore`) locate it with `referenceArrayOf`: a null array
throws `NullReferenceException`, and a reference to anything but offset 0 of a live array of
class references is an ill-typed state. An index read unsigned at or past the length then
throws `IndexOutOfRangeException` (`referenceArraySlot`), so a negative int32 index is out of
range, as in CoreCLR. A load pushes what the element's slot holds through `loadSlot`, as a
class-typed field load does. A store first checks covariance (`storableIn`): null is always
storable, and an instance of a class, admitted or opaque, is storable exactly when the array's
element class is in its lineage, which records every base up to `System.Object`, so a `Square`
stored into a `Shape[]` that is really a `Circle[]` throws `ArrayTypeMismatchException`. The
covariance check is the CLR's rule only because the array's element type is a class: an instance
is never assignable to a class outside its base chain, while an interface element would also
admit the instances implementing it, which the lineage does not record. Any other stored value,
such as an array, is unsupported rather than an exception: the model does not record the
interfaces or array covariance the CLR would consult for it. The store itself is
`storeSlot`, so it changes only that slot. The checks run in CoreCLR's order: null array,
index, then type.

## Value-array fields

A class field typed as an array of a value element `E` (`.arrayField`, `.setArrayField`) holds
the array's reference in the object's slot for that field, as a class-typed field does; the
array's bytes stay in their own allocation. The field is located like any other, so a null
receiver throws `NullReferenceException`, and the slot needs read or write authority. A store
(`storeArraySlot`) keeps null for the null array, and otherwise the array's origin, which must
be offset 0 of a live heap allocation exactly `length * width E` bytes long, with element type
`E`; anything else, such as a slice, a caller buffer or an array of another element, is an
ill-typed state. A load (`loadArraySlot`) rebuilds the array from the slot: null gives the null
array, and an origin gives the whole allocation as an array of `E`, its length the allocation's
size over the element width, validated like any array before it is pushed. A load of what a
store kept therefore returns the stored array exactly. The caller assumes the same of memory it
supplies: a value-array field slot holding a reference at entry names offset 0 of a heap
allocation that is the whole runtime array of the field's element type, the relation to the
runtime array a supplied array argument already requires. The allocation records no element type,
so the field's declared element is what the load trusts.

The extractor emits these operations for a field typed as a single-dimensional array of an
integer, Boolean, char, integer-backed enum, reference-free struct or integer vector, and Lean
rechecks the emitted element against the raw field token, and a stored value against an array of
that element on the evaluation stack. A vector's width is fixed by its type. A struct's comes
from its layout: the raw body names the field access as a layout use of the struct
(`LayoutUsesComplete`), and `MethodLayoutsValid` requires the emitted width to be the size Lean
computes for that layout, as for any other array of the struct
([TilePairs](../Examples/Proofs/TilePairs.lean)).

The extractor admits a single-dimensional array of an admitted class, or of a non-generic class
outside the model other than `System.Object`, such as `string`, as a parameter, local, return or
`newarr` type, typed as an object on the evaluation stack. An array of such a static type holds
elements of a class derived from it at run time, so its element type is a class, as the
covariance check needs; an array typed by an interface or `object` may be an interface array and
is rejected. An element of an array of a class outside the model is an opaque reference, which
is loaded, stored, compared and tested for null but never read through. The extractor names the
element class as an object in the raw array type, and Lean rechecks each
`newarr`, `ldlen`, `ldelem.ref` and `stelem.ref` against its raw opcode and operand kinds. An
element address (`ldelema`) or a typed `ldelem`/`stelem` on such an array is rejected by name,
since a byref to a reference slot is outside the model, as is the address of an argument or
local holding such an array. A class field typed as such an array holds the array's reference
in its slot and is read and written as a class-typed field is, the raw field type rechecked as
an array of a class. Multi-dimensional arrays, arrays of interfaces, `object`, generic
instantiations or value types other than the admitted value arrays are rejected.

## String literals

`ldstr` pushes the object `Memory.literals` binds to its text; the model never allocates one
([StringLiterals](../Examples/Proofs/StringLiterals.lean),
[StringDefault](../Examples/Proofs/StringDefault.lean)). Execution never changes the bindings
(`invoke_literals`),
so within a run one text always loads one object, and two loads of it are identical. ECMA-335
III.4.16 gives this guarantee. Roslyn marks assemblies
`CompilationRelaxations(NoStringInterning)`, which lets a runtime drop that guarantee, so the
claim rests on CoreCLR: in .NET 10,
`StringLiteralMap::GetStringLiteral` (`src/coreclr/vm/stringliteralmap.cpp`) resolves every
literal through the one `SystemDomain::GetGlobalStringLiteralMap()`, collectible modules
included, and never consults the relaxation.

The model claims nothing further. Distinct texts may bind one object, and a literal may be the
same object as a caller's string, as interning that string at run time makes it. The bound object
must form as a live object; an unbound text stops as unsupported rather than loading null, since a literal is
never null. A literal is an opaque string like any other, so nothing reads its length or
characters. Each bound literal must name an issued identity (`Memory.LiteralsBounded`) for a
contract to transfer across [allocation renaming](PROOFS-BINDING.md), since a literal names the
caller's object and not one the method allocates. The extractor rejects a text containing a
surrogate, backspace or form feed, which a Lean string literal cannot carry exactly.

## Argument guards

`ArgumentNullException.ThrowIfNull(object, string)` and the integer instances of
`ArgumentOutOfRangeException`'s `ThrowIfZero`, `ThrowIfNegative`, `ThrowIfNegativeOrZero`,
`ThrowIfEqual`, `ThrowIfNotEqual`, `ThrowIfGreaterThan`, `ThrowIfGreaterThanOrEqual`,
`ThrowIfLessThan` and `ThrowIfLessThanOrEqual` run as checked operations
([CIL/ArgumentGuards.lean](../CIL/ArgumentGuards.lean)). Each ends in the named outcome
`.thrown "System.ArgumentNullException"` or `.thrown "System.ArgumentOutOfRangeException"` exactly
when its condition holds, and otherwise pops its operands and leaves memory unchanged
([GuardCount](../Examples/Proofs/GuardCount.lean), [GuardIndex](../Examples/Proofs/GuardIndex.lean),
[GuardRequired](../Examples/Proofs/GuardRequired.lean)). The contracts follow the .NET 10 sources:

- `src/libraries/System.Private.CoreLib/src/System/ArgumentNullException.cs`: `ThrowIfNull` throws
  `new ArgumentNullException(paramName)` when `argument is null` and returns otherwise.
- `src/libraries/System.Private.CoreLib/src/System/ArgumentOutOfRangeException.cs`: `ThrowIfZero`,
  `ThrowIfNegative` and `ThrowIfNegativeOrZero` test `T.IsZero` and `T.IsNegative`
  (`INumberBase<T>`); `ThrowIfEqual` and `ThrowIfNotEqual` use
  `EqualityComparer<T>.Default.Equals`; the four ordering guards compare `value.CompareTo(other)`
  with zero (`IComparable<T>`). Every throw goes through a `[DoesNotReturn]` helper that throws a
  new `ArgumentOutOfRangeException`.

On `sbyte`, `byte`, `short`, `ushort`, `int`, `uint`, `long`, `ulong`, `nint` and `nuint` these
members are the mathematical tests on the integer the type denotes, which is what
`ZeroGuard.throws` and `ComparisonGuard.throws` state over `guardOperand`: a narrow value takes
the low bits of its `int32` stack slot, unsigned values are never negative, and the native
integers take the 64-bit target. Only the exception type is claimed. Its message, `ParamName` and
`ActualValue` are not modeled, and the outcome allocates nothing, as with any `.thrown` outcome.
The `paramName` argument, a compiler-supplied literal, is popped unread, so a proof binds that
literal like any other.

The extractor maps each exact signature (`Extractor/ArgumentGuards.cs`) and Lean decodes each
emitted guard again from the raw call's owner, name, type argument, parameter types and external
identity (`CIL.Extraction.guardCallMatches`); no other instruction may emit a guard. Other
instantiations, among them `char`, floating-point and `decimal`, the `void*` overload of
`ThrowIfNull`, and the string guards such as `ThrowIfNullOrEmpty`, which read characters, are
rejected calls. `ThrowIfNull` on a value array or any other operand that is not a class instance or
null is rejected by name, since the model tests only object references.

## Sequential struct layout

Admitted layouts are reference-free and bounded by 65,536 bytes. Sequential fields include supported
integers/enums, nested aggregates and admitted vectors. Closed same-assembly generic owners bind
their original fields, arguments and constraints to substituted layouts. Field order, packing, size
and target architecture determine offsets. Unset packing is a limit of 64 bytes; nested alignment
comes from the child layout, capped by packing. Inferred sizes include tail padding, declared size cannot
truncate fields, and empty structs occupy at least one byte. Explicit overlap follows byte storage.

Open generic owners, explicit/auto generic layouts, reference/float fields, inline arrays and
recursive/depth-over-128 layouts are rejected. Vector512 fields are excluded because their aggregate
alignment is not modeled. Storage is managed layout and is not interop marshalling.
Correspondence to
[CoreCLR layout](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/vm/classlayoutinfo.cpp)
is assumed; runtime probes and kernel layout bounds supply different kinds of evidence.

## Value tuples

Only the exact supported `System.ValueTuple<T1,T2>` identity with two equal-width primitive integer
fields is admitted. CoreCLR auto-layout can reorder mixed-width fields; those tuples, other arities,
enums/nested aggregates, tuple construction/methods and tuple fields inside structs are excluded.
Lean checks the equal-width auto-layout restriction. Faithful resolution and runtime ordering remain
assumptions; [tuple tests](../Tests/TupleDivision.cs) probe both admitted and reordered layouts.

## Typed copies

`copyObject_writes_snapshot` proves destination bytes equal the source snapshot and are initialized,
including padding. Access and initialization premises remain mandatory. References have provenance
and offsets, not nominal CLR type tags: relating `cpobj` to the runtime additionally assumes both
storage regions are compatible with its validated type token. Runtime tests are not a JIT proof.

## Struct instance calls

Admitted direct instance calls use a managed-reference `this`; by-value arguments have private homes.
Existing-storage constructors do not allocate or bypass initialization checks. Aggregate `newobj`
uses zeroed caller-owned temporary storage, a void constructor and checked snapshot readback.
Padding/layout correspondence and resource availability remain assumptions.

Tail transfers retire the caller frame before checking callee arguments, so references into retired
storage fail even if unused. Typed `ldftn`/`calli` identities carry exact closed signatures and
certificate-bound targets; integers cannot fabricate them. Tail cycles need termination proofs.
Only the admitted default-managed static signature subset is supported; imported/intrinsic tail
calls, unmanaged conventions, null table entries and mutable tables are excluded.

Immutable native handler tables require a faithful explicit runtime-slot binding, live static
storage, aligned initialized readable bytes and an exact catalog signature. Targets are supplied
identities and are not decoded addresses. Each method has one supported indirect signature;
table-pointer handler signatures are excluded. These handler tables are not arbitrary mutable
raw-pointer dispatch.

## Integer enums

Same-assembly non-generic enums retain identity but execute with their validated integer storage.
All underlying bit patterns are admitted, including those without a named constant. Narrow
extension/truncation follows the underlying type. Boxing, reflection, enum instance methods and
external enum dependencies are excluded; equal byte widths do not authorize replacing one enum
identity with another.

Checked pointer parameters and locals admit these enum types and `char`, using the existing
allocation-relative reference representation and integer loads/stores. Enum pointees retain their
validated declaration identity and underlying storage; character pointees require the exact runtime
type identity. This admission does not extend to floating-point, nested-pointer or
reference-bearing pointees.

## Portable bit helpers

Rotations use modulo-width counts; counts/reversal and log2 follow the scalar bit-vector model.
Log2(0) is zero. Round-up returns zero for zero/overflow; signed power-of-two tests exclude the sign
bit. Native overloads assume 64 bits. Primitive signed and unsigned 32-bit, 64-bit and native
`RotateLeft`/`RotateRight` overloads share the same bit-vector rotation model. Primitive integer
population/leading-zero/trailing-zero counts reuse the same count functions, with the result
encoded in the declared 32-bit or 64-bit stack representation. Unsigned primitive `Log2` uses
the same logarithm function and result encoding. Primitive `IsPow2` uses the signedness-aware
power-of-two model. Signed `Log2` is unsupported.
Correspondence to these primitive methods and the selected .NET BitOperations and BinaryPrimitives
overloads remains a runtime assumption backed by exact signature checks and boundary/runtime
comparisons.
See [SIMD](SIMD.md) and [OPCODES](OPCODES.md).

`Math.DivRem` and the 32-bit and signed 64-bit `Math.BigMul` overloads are modelled from the
pinned .NET 10 `Math.cs` source: the quotient reuses CIL `div`, narrow operands divide in
`int` and wrap, and the remainder is `left - quotient * right`. The equal-width tuple layout is
recomputed from metadata and probed at run time. Correspondence to the runtime remains an
assumption backed by exact signature checks and boundary comparisons that include both faults.
