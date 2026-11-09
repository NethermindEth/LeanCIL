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

[`CheckedSpan`](../CIL/Safety/SpanContents.lean) `memory view width writable values` bundles the
view's validity, access mode and contents, and [`SpanSuffix`](../CIL/Safety/SpanContents.lean)
is a loop state over such a view. `span.facts` is the view's validity, width and mode for the
stepper; `span.head` gives the passing guard, a positive length and the first element's
reference and load; `span.length_cons` is the passing guard alone and `span.length_nil` makes it
fail; `span.tail` gives `Slice(1)` and the checked suffix; `span.below` moves a checked span into
any memory that keeps the caller's, [`CheckedSpan.within`](../CIL/Safety/LoopCallerFacts.lean) into
the memory of a `LoopFrame` confined to no caller storage, and `span.tail_below` slices there while
keeping the suffix checked in caller memory. The loop tactics take these facts from a `CheckedSpan`
in context.

A loop that writes a span from the front needs authority over its elements, not their contents.
[`SpanWritable`](../CIL/Safety/SpanWrites.lean) `memory footprint view` is write access to every
element of `view` with its bytes inside an entry of `footprint`; `SpanWritable.own` builds it over
`view.footprint` from a `Writable` run, `SpanWritable.slice` keeps it for any slice and
`SpanWritable.within` carries it into every `LoopFrame` memory.
[`WritableSpan`](../CIL/Safety/SpanWrites.lean) `memory footprint view width count` adds the
view's validity, mode, width and length, and `WritableSuffix` is a loop state over it.
`span.length_nil` and `span.length_cons` decide the `Length != 0` guard, `span.tail` gives
`Slice(1)`, and `frame.write_span_head wellFormed span x` stores `x` into the first element in the
frame's memory, returning the element's address `view.reference = .address item`, the write and
the frame after it. The loop tactics take the guard and validity facts from a `WritableSpan` in
context. An invariant states the written prefix from the span's original base as
`Filled state.memory base width (List.replicate done x) state.values.remaining` and extends it
with `Filled.push`. A loop that passes the span to a callee lends it: `span.lend wellFormed frame`
is a `WritableSpan` in the frame's memory over the view's own bytes, a callee's precondition,
and `span.covered` and `span.below wellFormed` place those bytes in the frame's footprint and
below the caller's watermark, which `cil_loop_call` takes for the frame after the call.
`span.write_head x` is the store a callee writing `target[0]` makes, confined to the view's
bytes; after the call the invariant moves the prefix with `Filled.after_confined` and extends it
with `Filled.extend`.
Callee frames allocate locals above the caller's memory. For well-formed caller memory,
`SpanView.validate_below`, `SpanView.slice_below` and `SpanContents.after_below` transport validity,
successful slices and contents to any memory related by `MemoryBelow memory.nextIdentity`, such as
the memory after frame entry and local stores.

A method with locals cannot promise `final = memory`: its expired frame allocations stay in the
final memory, so it ends with `MemoryBelow memory.nextIdentity memory final`, as `SpanSum` does,
and its callers should expect that instead of equality. Two such calls compose with
[`MemoryBelow.compose_invoke`](../CIL/Safety/ExecutionLifetime.lean) `called first second`, which
takes the watermark growth from the first call's successful `invoke`;
[`MemoryBelow.compose`](../CIL/Safety/MemoryBelow.lean) takes it as a premise. Without that growth
the two facts do not compose. The `_below` lemmas then carry the caller's validity and contents
from `memory` to the final memory. Contents a callee leaves in caller storage hold in the callee's
result memory, which the caller's frame exit relates only by its entry watermark.
[`SpanContents.after_below_valid`](../CIL/Safety/SpanContents.lean) and
[`SpanView.validate_eq_below`](../CIL/Safety/SpanContents.lean) transport them, given the view is
valid in the caller's well-formed entry memory. `Contents.after_below` does the same for a
`Contents` fact once `SpanView.allocation_below` bounds its allocation.

The [AllZero span loop](../Examples/Proofs/SpanAllZero.lean) decides whether every element of an
arbitrary-length `ReadOnlySpan<uint>` is zero, with the invariant `remaining.all (· == 0) = result`
and exact memory preservation. The [Sum span fold](../Examples/Proofs/SpanSum.lean) returns the
wrapping sum of a `ReadOnlySpan<ulong>` with the invariant `total + remaining.sum = values.sum`; its
running total lives in a frame home, so its state keeps the `CheckedSpan` suffix in caller memory,
which the loop tactics move to the current frame memory with `span.within`. Its entry comes from
`bind_entry ... allocating wellFormed`, and its `FrameState` carries the returned `LoopFrame`
across each store with `frame.store` and each slice with `set_local`; see [loop verification
conditions](PROOFS-STEPPING.md#loop-verification-conditions). Both measure the remaining length,
prove the loop inside the public theorem through `invoke_loop_returns` or `invoke_loop_results`, and
cover null empty spans.

## Read a supplied array

An array argument `.array values` is an `ArrayView` whose bytes are the span `values.storage`, so
its elements are stated as `SpanContents memory values.storage width elements`, beside
`values.validate memory = .ok ()` and its `elementType`. A null array has no elements, so an
index below `elements.length` is in bounds of a non-null array.
[`contents.array_load valid scalar bound`](../CIL/Safety/ArrayContents.lean) gives the element's
address `arrayElement memory values index width = .ok item` and its load, the element's value.
`step_arrayLoad_of_element` steps `ldelem` from those two facts and `step_arrayAddress_of_element`
steps `ldelema` from the address; `arrayElement_formed` forms that address, so a helper may return
it. An index outside the array throws, which a precondition bounding the index rules out.

A loop indexing the array reads it the way a span loop does, through the storage span: the caller's
`CheckedSpan initial values.storage width true elements` carries into each iteration's frame by
`CheckedSpan.within`, and `array_load` of its contents names the element. A loop storing into the
array holds `SpanWritable` authority over `values.storage` instead; with the array addressed at
`base`, `arrayElement_of_access` turns write authority over `base.element width index` and the
bound into the element `arrayElement` returns, and `step_arrayStore_of_write` steps `stelem` to the
written memory. The bound test compares the index with `values.Length` as signed words;
`SpanView.length_bounded` of the storage span keeps the length below `2 ^ 31`, and
`toInt_ofNat_of_lt`, which `cil_loop_obligation` applies, reads that comparison as unsigned.

Converting the whole array to a span, as `ReadOnlySpan<T> rest = values` does, pushes
`values.span writable`, the storage extent under the conversion's access mode;
`step_arraySpan_whole` steps it from the array's validity and element type, and a null array
converts to an empty span. `CheckedSpan.of_array` checks that span to hold the storage span's
elements, and `WritableSpan.of_array` gives a writable one the storage span's authority, so a loop
slicing the span is proved as one slicing a span argument.

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
the invariant of a compiled loop. The [proof regressions](VALIDATION-PROOFS.md#proof-automation)
list the neighbouring-byte, sibling-slice and rejected claims these lemmas are checked against.

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

Single-reference and pointer span constructors, empty getters and in-place local resets use the
same views; the [coverage reference](VALIDATION-COVERAGE.md) lists the runtime comparisons for each.
`memoryInstruction_emptySpan` proves that every supported element width and capability produces
a null, zero-length view without changing memory. `SpanConstructor.empty` uses that same operation
when `initializeSpanLocal` replaces a local's previous view.
An `in` or `ref readonly` span parameter is passed as the referenced `.bufferSpan` view, so a
contract states the same view argument as a by-value span and reuses `SpanView.validate`,
`Contents` and the span element lemmas, whether the caller passes a span local or a temporary.
`MemoryMarshal.GetReference` of a readonly view steps by `step_memory_spanReference_readOnlyView_eq`
to a `.readOnlyReference`; loads, field loads and `ldflda` accept it, so the first-element load
is proved with the same lemmas.
Element and byte offsets of a readonly reference step by the `step_memory_add_readOnly_*`
equations to a `.readOnlyReference` with the writable form's address, so `add_element` applies
unchanged, including for `Unsafe.Add(..., 1)`. Integer byte-order transfers and view observations
without byte authority follow the same rules. Supplied aggregate/vector arrays reuse the same
checked snapshot loads/stores, indexed references and span conversions; no backing storage is
allocated. `ArrayView.null_valid` requires a valid element width, and
`InitializerFits` includes that condition for array locals, even when initialized to null.

Closed generic-owner helpers, including nested owners and mixed owner/method arguments, use the
ordinary specialized managed-call proof interface. Closed sequential generic structs
use the existing checked layout, field and construction rules after substituting the owner
arguments. Prove calls against the specialized closed body; no separate generic runtime or
heap representation is introduced. Constrained interface calls on these closed owners, with
implicit or explicit mutating implementations, use the same direct-call proof interface after the
certificate resolves and binds the exact implementation.

For supplied native dispatch tables, provide an immutable allocation binding and exact catalog
target identities in `MethodTable.backing`. Checked byte offsets and `ldind.i` preserve
authenticated callable provenance; numeric address bytes alone are insufficient. These tables
require a unique supported managed indirect-call signature in each body; handler
signatures cannot carry native table pointers. Ordinary call and tail-call lifetime and fuel
obligations still apply.

Managed indirect calls admit aggregate and integer-vector values and references through the ordinary
checked argument/return storage, for normal and tail transfers alike; unspecified lanes are
rejected. Pointer overloads of `Unsafe` block helpers use the same block operations and proof rules
as their managed-reference overloads. The [coverage reference](VALIDATION-COVERAGE.md) lists the
suites that check each of these interfaces.

## View struct fields

Import `CIL.Safety.AggregateFields` to reason about a struct home field by field instead of byte by
byte. `AggregateLayout.values layout bytes` decodes each field's unsigned little-endian number and
`FieldLayout.setIn bytes number` encodes one store; both are defined over the byte semantics.
`AggregateLayout.Disjoint` is a decidable check that no two fields share a byte. Under it and
`Valid`, `values_setIn` replaces one field's value and keeps every other, and `numberIn_setIn_apart`
keeps any field apart from the written one. An explicit layout with overlapping fields fails the
check, so these laws do not apply to it and its proofs stay at the byte level.

A struct local is tracked in the same `LocalSnapshots` set as numeric locals, remembered as its
bytes. `LocalSnapshots.zero_aggregate` returns the step equation for `initobj` through the local's
address. `store_field` and `load_field` cover int, word and 16- or 32-byte vector fields,
`load_signed_field` sign extends a 1- or 2-byte field as `signedOfWidth`, and
`store_aggregate_field` and `load_aggregate_field` cover a nested struct field, whose value is the
number of its bytes. Zeroing and stores also return the updated snapshots, well-formedness,
`MemoryBelow` for the step, continued write access, the address's `form` fact for the next step
and the write equation; a store also returns the decoded field values, which the next store or
load takes. Every other local's snapshot is kept. A frame from `bind_entry ... allocating`
supplies its `LoopFrame`, whose `homes` and `snapshots` start the chain, and
`MemoryBelow.frame_round_trip` composes the per-step facts on return.
[Struct](../Examples/Proofs/Struct.lean) shows the frame-entry and remembered-local forms; the
[proof regressions](VALIDATION-PROOFS.md#proof-automation) list the rejected overlapping layouts.

## Carry frame facts through a loop

Import `CIL.Safety.LoopFrames` to keep the frame facts of a loop out of its invariant.
`LoopFrame footprint caller current kinds slots known` bundles `Confined footprint caller current`,
well-formedness, `WritableHomes` for the frame's locals and their `LocalSnapshots`, with
`knownLocals values` naming the remembered values. `kinds`, `slots` and `values` follow the
frame's local indices: `slots` is the frame's `locals`, a span, reference or other local without a
byte home is a skipped `WritableHomes` slot and a `none` value, and so the lemmas stated over
`frame.locals`, such as `LocalSnapshots.store`, apply to the loop frame directly. `FrameState`
pairs the loop's values with a memory and its `LoopFrame`, with the slots and remembered values as
functions of the loop's values, so an invariant over a `FrameState` states only the property.
`bind_entry ... allocating` proves the frame of the entered locals and parameter homes for any
footprint, with each home remembered as its initializer and every other local as `none`; a
default span or object local holds the null span or null and allocates nothing.
`LoopFrame.ofEntry`, `WritableHomes.entry` and `skip`, and `LocalSnapshots.entry` and `skip` are
the lemmas it composes. `set_local` keeps the frame when a local without a byte home is assigned,
as the span fold slices its span and a list walk moves its object local to the next node; it
rejects a home and a remembered local.

Each lemma proves the frame after one step. `load` and `store` read and write a remembered local;
`write` and `write_element` keep the frame across a write inside the footprint; `after_confined`
keeps it across a call whose footprint entries lie inside it; `form` and `leave` give the caller
reference's `form` fact and the confined, `MemoryBelow` result on return, from the entry's
`setup` and, optionally, the frame the loop returns from. A frame confined to no
caller storage, `LoopFrame []`, has `kept` all of it and `leave_kept` gives the exit's
`MemoryBelow` fact from the entry's `setup`. A local whose address is
taken can change through that reference, so `write` and `after_confined` require every written
allocation to be older than the frame (`allocation < caller.nextIdentity`); a write or callee that
reaches a home does not elaborate and the snapshot stays the author's obligation.
`add_int_element`, `int_lt` and `toNat_succ` step a signed `int` index below `2^31` to an element
offset and its compare. The [buffer fill proof](../Examples/Proofs/FillWords.lean) uses them with
an invariant of only `Filled` and `k <= n`. [Countdown](../Examples/Proofs/Countdown.lean) needs
no invariant beyond the frame, and [CountCalls](../Examples/Proofs/CountCalls.lean) and
[CountUntil](../Examples/Proofs/CountUntil.lean) keep two locals across a helper call with
`after_confined`. The [proof regressions](VALIDATION-PROOFS.md#proof-automation) list the
rejected writes, including one through the second home of a generated two-local frame.

### Caller facts in frame memory

`CIL.Safety.LoopCallerFacts`, which `CIL.Safety.LoopScaffold` imports, carries facts about the
caller's memory into every frame memory, whatever the footprint. Facts that read only allocations
always carry; a span's contents carry when it lies apart from each footprint entry:

```lean excerpt CIL/Safety/LoopCallerFacts.lean
def SpanApart (view : SpanView) (entry : Reference × Nat) : Prop :=
  ∀ base, view.reference = .address base → Apart base (view.width * view.length) entry
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem LoopFrame.caller_form (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {base : Reference}
    (valid : CIL.Safety.form caller base = .ok base) :
    CIL.Safety.form current base = .ok base :=
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem LoopFrame.caller_add (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {base result : Reference} {width : Nat}
    {offset : BitVec 64} (added : add caller base width offset = .ok result) :
    add current base width offset = .ok result := by
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem LoopFrame.caller_valid (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view : SpanView} (valid : view.validate caller = .ok ()) :
    view.validate current = .ok () :=
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem LoopFrame.caller_element (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view : SpanView} {index : Nat} {item : Reference}
    (found : view.element caller index = .ok item) : view.element current index = .ok item := by
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem LoopFrame.caller_slice (frame : LoopFrame footprint caller current kinds slots known)
    (wellFormed : caller.WellFormed) {view sliced : SpanView} {start length : Nat}
    (cut : view.slice caller start length = .ok sliced) :
    view.slice current start length = .ok sliced := by
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem CheckedSpan.within {view : SpanView} {width : Nat} {writable : Bool}
    {values : List (BitVec (8 * width))} (span : CheckedSpan caller view width writable values)
    (wellFormed : caller.WellFormed) (frame : LoopFrame footprint caller current kinds slots known)
    (apart : ∀ entry ∈ footprint, SpanApart view entry := by cil_span_apart) :
    CheckedSpan current view width writable values := by
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem SpanApart.slice {view sliced : SpanView} {entry : Reference × Nat} {memory : Memory}
    {start length : Nat} (apart : SpanApart view entry)
    (cut : view.slice memory start length = .ok sliced) : SpanApart sliced entry := by
```

```lean excerpt CIL/Safety/LoopCallerFacts.lean
theorem Writable.add_int {memory : Memory} {base : Reference} {width start count : Nat}
    (writable : Writable memory base width start count) (wellFormed : memory.WellFormed)
    (valid : CIL.Safety.form memory base = .ok base) {index : CIL.W32}
    (small : index.toNat < 2 ^ 31) (low : start ≤ index.toNat)
    (high : index.toNat < start + count) :
    add memory base width (BitVec.ofInt 64 index.toInt) = .ok (base.element width index.toNat) :=
```

Each `caller_*` lemma also takes the caller's `WellFormed`. The loop tactics apply them, and
`CheckedSpan.valid_within`, at the frame memories they reach, so a proof states each fact once,
at the caller's memory: `(span.within wellFormed frame).head` reads a caller span's first element
in frame memory, with `cil_span_apart` finding each entry's `SpanApart` in context, and
`writable.add_int wellFormed formed` gives an `int` index's `Unsafe.Add` address for every frame.
[CopyUntilZero](../Examples/Proofs/CopyUntilZero.lean) states only these.
`Filled.element_writable` and `Writable.element_writable` give write authority over one element
of a run, and `cil_loop_obligation [defs]` proves an element write's authority, index bound and
footprint membership from the hypotheses with `defs` unfolded, failing at the write when they do
not imply it.

A caller buffer is written word by word through these lemmas of
[BufferContents](../CIL/Safety/BufferContents.lean):

```lean excerpt CIL/Safety/BufferContents.lean
theorem Writable.sub {start count : Nat} (writable : Writable m base width start count)
    {index length : Nat} (low : start ≤ index) (high : index + length ≤ start + count) :
    Writable m (base.element width index) width 0 length := fun i bound => by
```

```lean excerpt CIL/Safety/BufferContents.lean
theorem Writable.write_one (writable : Writable m base width 0 1) (x : BitVec (8 * width)) :
    ∃ after, write m base (numberBytes x.toNat width) 1 = .ok after ∧
      form m base = .ok base ∧ Confined [(base, width)] m after ∧
      Contents after base width [x] := by
```

```lean excerpt CIL/Safety/BufferContents.lean
theorem Filled.extend {xs : List (BitVec (8 * width))} {room index : Nat}
    {x : BitVec (8 * width)} (filled : Filled m base width xs (room + 1))
    (slot : Contents m (base.element width index) width [x]) (next : index = xs.length) :
    Filled m base width (xs ++ [x]) room := by
```

`Writable.write_one` with `step_storeScalar_of_write` (1-, 2- or 4-byte `int` stores) or
`step_storeScalar_i64_of_write` ([LoopFrames](../CIL/Safety/LoopFrames.lean)) proves a one-word
store helper's contract, as `Stamp`'s in CopyUntilZero.

## Track a struct local by its fields in a loop

`CIL.Safety.LoopFrameFields`, which `CIL.Safety.LoopScaffold` imports, remembers a struct local
in a `LoopFrame` as `.aggregate (layout.encode fields)`: `AggregateLayout.encode` writes each
field's value at its offset in zeroed bytes, so a state names the fields rather than the bytes.
`AggregateLayout.zeros layout` is the value each field loads from zeroed bytes: `.i32 0` for a 1-, 2-
or 4-byte field, `.i64 0` for a word, the vector zero for a 16- or 32-byte field and
`.aggregate (List.replicate width 0)` for a nested struct. `encode_zeros` proves the encoded
zeros are the struct's zero bytes. `LoopFrame.zero_aggregate frame index layout fields` steps
`initobj` through the home's address to a frame remembering `fields`; its `valid`, `sized` and
`zeroed` arguments check by `decide` and `rfl` that the layout is valid, fills the local and that
`fields` is `layout.zeros`, so a wrong zero claim does not elaborate. `store_field frame index
valid fieldIndex value` steps `stfld` to a frame remembering `fields.set fieldIndex value`, and
`load_field` steps `ldfld` through the address to the field's value. Each returns the step
equation, the frame after it and `MemoryBelow`; the slot, the field and its width are checked by
`rfl` and `decide`, so a field outside the layout or a value of another width does not elaborate.
A by-value read, `ldloc` then `ldfld`, loads the struct and reads the field with
`step_fieldAt_encode`. A 1- or 2-byte field holds an `.i32` and reads back truncated to its width
and zero or sign extended, as `narrowLoad width signed bits`: `step_fieldAt_encode_narrow` reads
it by value and `load_narrow_field` through the address.

The loop tactics gather the field reads and the home's `form` from each frame in scope, and
`cil_loop_recurse`, `cil_loop_advance` and `cil_loop_finish` take the zeroing, the stores and
numeric local stores themselves, so a proof names neither. A zeroed struct's layout is one its loop head remembers.
A field reads back as the value stored, such as `.i32 (count + 1)`, with no `toNat` round trip
through bytes, and a narrow field as its `narrowLoad`, which the tactics compute for a literal.
[TallyTwice](../Examples/Proofs/TallyTwice.lean) counts and sums in a
struct across a helper call this way, naming no frame lemma, memory or step.
