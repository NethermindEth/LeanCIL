# Buffer content proofs

## Describe span contents

`CIL.Safety.SpanContents` is the vocabulary for what a span holds. `SpanContents memory view width
values` says the view has element width `width`, its length is `values.length`, a null view holds
`[]`, and an addressed view's elements read back from its base as `Contents`. It asserts neither
validity nor write authority; state `view.validate memory = .ok ()` and the access mode separately.
`SpanContents.nil` builds the empty case for any zero-length view. For a valid view,
`SpanContents.load` gives element `index` as a successful `view.element` reference whose scalar
load is `numericOfWidth width value.toNat`; `SpanContents.head` is that fact for the first element
of `value :: rest`. `SpanContents.drop` and `SpanContents.tail` give the successful
`view.slice memory count (view.length - count)`, its validity, its unchanged mode and the contents
of the remaining elements, so a loop that reads `values[0]` and continues with `values.Slice(1)`
carries its invariant without unfolding views, slices or byte reads.
`SpanView.length_word_ne_zero` discharges a `Length != 0` guard for a valid nonempty view.

Callee frames allocate locals above the caller's memory. For well-formed caller memory,
`SpanView.validate_below`, `SpanView.slice_below` and `SpanContents.after_below` transport validity,
successful slices and contents to any memory related by `MemoryBelow memory.nextIdentity`, such as
the memory after frame entry and local stores.

The [AllZero span loop](../Examples/Proofs/SpanAllZero.lean) decides whether every element of an
arbitrary-length `ReadOnlySpan<uint>` is zero, with the invariant `remaining.all (· == 0) = result`
and exact memory preservation. The [Sum span fold](../Examples/Proofs/SpanSum.lean) returns the
wrapping sum of a `ReadOnlySpan<ulong>` with the invariant `total + remaining.sum = result`; its
running total lives in a frame home, so its state keeps the span facts in caller memory and
transports them to the current frame memory with the `_below` lemmas. Both measure the remaining
length and cover null empty spans.

## Describe buffer contents

`CIL.Safety.BufferContents` states what a contiguous run of integer elements holds, over the checked
memory model. `Contents m base width xs` says element `i` of `xs : List (BitVec (8 * width))` reads
back at `base.element width i` (offset `base.offset + width * i`, same allocation) as `numberBytes
x.toNat width`, with the byte alignment scalar loads and stores use. `Contents.load` (from
`load_scalar_of_read`) turns an element at any `ScalarWidth` (1, 2, 4, 8, 16, 32 or 64 bytes) into
the `loadValue` result `numericOfWidth width x.toNat`: widths 1 to 4 zero-extend to `.i32`, 16 and
up are vectors, and width 8 yields `.i64 (BitVec.ofNat 64 x.toNat)`, so `Contents.load_word`
(`load_word64_of_read`) stays the direct route to `.i64 x`. `byteNumber_elementBytes` decodes a
whole buffer as the sum of its elements, element `i` scaled by `256 ^ (width * i)`, and
`byteNumber_elementBytes_lt` bounds it by `256 ^ (width * xs.length)`. Rewriting with it at a
literal width such as 8 makes the kernel unfold the powers and can hit deep recursion; prove the sum
at symbolic width and instantiate, as `byteNumber_elementBytes_four` does for four limbs
(instantiate, then `simp only [Nat.reduceMul, Nat.reducePow] at h`), or peel one limb at a time with
`byteNumber_elementBytes_cons`. Contents grant no write authority: `Writable m base width start
count` is write authority alone, and `Filled m base width xs room` is an initialized prefix followed
by `room` writable elements that need not be readable. An empty `Contents` asserts nothing.
`Contents.read` joins the elements into one checked read only given that read's `access`, so a
zero-width read keeps its formation check and elements separated by a reference slot do not join;
`Contents.of_read` splits a checked read through `read_slice_bytes`. `take`, `drop` and `append`
move between adjacent subranges. `Contents.write_element` and `Contents.write_run` update one
element or a run; `Contents.after_write_apart` and `Contents.after_confined` keep contents `Apart`
from a write or every footprint entry, including disjoint slices of one allocation; `Filled.push`
extends the prefix by one element write without reading the room. `Filled.fill` and
`Contents.transform` prove fill and in-place map loops of any length (`writeElements`,
`transformElements`) as sequence properties confined to the buffer; `add_element` steps `Unsafe.Add`
to an element, and the [buffer fill proof](../Examples/Proofs/FillWords.lean) carries `Filled` as
the invariant of a compiled loop. `Tests/BufferContents.lean` checks unchanged neighbouring bytes
and sibling slices, and refutes uninitialized, past-end, overlapping, unjoined and stale claims.

`SpanView.slice_reference` identifies the allocation-relative start of a successful addressed
slice; `SpanContents.drop` combines it with `Contents.drop`. Slice validity alone does not assert
readable contents.

For `Span<T>.Fill` and `Clear`, `SpanView.fill_contents` derives the repeated sequence from the
successful checked fill, without a readable-input premise. `Contents.after_span_fill` preserves
sequences outside a nonempty fill's extent. The operation checks the whole range once and performs
one write; callers need no element-by-element execution proof.

`Span<T>.CopyTo` and `TryCopyTo`, including readonly sources, capture all source bytes before a
destination write, so both overlap directions and self-copy preserve the original sequence.
`writeIndexed_readback` and `writeIndexed_outside` expose exact readback and neighboring-byte
preservation for the retained snapshot. The snapshot uses array indexing for constant-time byte
lookup. Short destinations throw `ArgumentException` or return false without a source read or
destination write; empty copies require no byte access.

Aggregate and integer-vector spans use the same `SpanView`, indexed references, checked
loads/stores, byte snapshots and copy rules. Supply the validated element width rather than assuming
one of the primitive widths. `Clear` initializes the byte extent. Aggregate/vector `Fill` repeats a
captured snapshot with its initialization flags through `SpanView.fillSnapshot`;
`spanFillSnapshot_effect` exposes its checked snapshot-write effect. Scalar `Fill` retains the
existing sequence-content lemmas. Vector loads and stores preserve initialization masks, while span
copies require readable, initialized source bytes. View creation and reinterpretation alone
establish neither initialization nor read/write authority.

`Tests/AggregateSpans.cs` demonstrates aggregate buffers, vector masks, overlap-safe copying and
target-dependent layouts. `Tests/AggregateSpanFill.cs` checks repeated masked snapshots, aliased
inputs and neighboring bytes. `Tests/SpanConstructors.cs` checks single-reference and pointer
constructors, including target-dependent layouts, empty getters and in-place local resets.
`memoryInstruction_emptySpan` proves that every supported element width and capability produces
a null, zero-length view without changing memory. `SpanConstructor.empty` uses that same operation
when `initializeSpanLocal` replaces a local's previous view.
An `in` or `ref readonly` span parameter is passed as the referenced `.bufferSpan` view, so a
contract states the same view argument as a by-value span and reuses `SpanView.validate`,
`Contents` and the span element lemmas; `Tests/SpanReferenceContracts.lean` proves an indexed
read this way and `Tests/SpanReferences.cs` covers callers that pass span locals and temporaries.
`MemoryMarshal.GetReference` of a readonly view steps by `step_memory_spanReference_readOnlyView_eq`
to a `.readOnlyReference`; loads, field loads and `ldflda` accept it, so
`Tests/SpanReferenceWordContract.lean` proves the first-element load with the same lemmas.
Element and byte offsets of a readonly reference step by the `step_memory_add_readOnly_*`
equations to a `.readOnlyReference` with the writable form's address, so `add_element` applies
unchanged; `Tests/SpanReferenceSecondContract.lean` proves `Unsafe.Add(..., 1)` this way.
`Tests/BinarySpans.cs` demonstrates integer byte-order transfers and short-span behavior.
`Tests/ViewAccessors.cs` checks observations without byte authority. Supplied aggregate/vector
arrays reuse the same checked snapshot loads/stores, indexed references and span conversions; no
backing storage is allocated. `Tests/AggregateArrays.cs` and `Tests/AggregateArrayStorage.lean`
cover exact types, masks, authority and lifetime. `ArrayView.null_valid` requires a valid element
width, and `InitializerFits` includes that condition for array locals, even when initialized to
null.

Closed generic-owner helpers use the ordinary specialized managed-call proof interface;
`Tests/GenericOwners.cs` covers nested owners and mixed owner/method arguments. Closed sequential
generic structs use the existing checked layout, field and construction rules after substituting the
owner arguments. Prove calls against the specialized closed body; no separate generic runtime or
heap representation is introduced. `Tests/GenericLayouts.cs` covers fields, nested layouts, instance
calls and construction. Constrained interface calls on these closed owners use the same direct-call
proof interface after the certificate resolves and binds the exact implementation;
`Tests/ConstrainedCalls.cs` covers implicit and explicit mutating implementations.

For supplied native dispatch tables, provide an immutable allocation binding and exact catalog
target identities in `MethodTable.backing`. Checked byte offsets and `ldind.i` preserve
authenticated callable provenance; numeric address bytes alone are insufficient.
`Tests/NativeManagedDispatch.cs` and `Tests/NativeMethodTables.lean` cover dispatch and rejection
obligations. These tables require a unique supported managed indirect-call signature in each body;
handler signatures cannot carry native table pointers. Ordinary call and tail-call lifetime and fuel
obligations still apply.

Managed indirect calls admit aggregate and integer-vector values and references through the ordinary
checked argument/return storage. `Tests/ManagedDispatch.cs` covers normal and tail transfers, exact
closed generic identities, initialization masks and rejected unspecified lanes. Pointer overloads of
`Unsafe` block helpers use the same block operations and proof rules as their managed-reference
overloads; `Tests/Blocks.cs` covers exact overload/alignment evidence.
