# Binding and transporting compiled proofs

## Generate loop entry and cutpoint scaffolding

Import `CIL.Safety.LoopScaffold` to derive a concrete checked entry and a uniquely identified
instruction from an extracted method:

```lean extracted
bind_entry entry := Extracted.method0 with [] from CIL.Safety.Memory.empty
bind_cutpoint cutpoint := Extracted.method0 matching (· matches .brnonzero _) with entry.frame
```

`entry.frame`, `entry.memory` and `entry.home0` (and subsequent numeric homes) come from
`enterFrame`. `entry.checked` proves the allocator returned exactly that frame and memory. Inputs
must reduce to successful allocation, or the command must receive a proof of success. An invalid
entry is rejected.

For reducible span, reference and object slots, `entry.slotN` names the exact initial slot, while
`entry.loadN` and `entry.storeN` specialize shared home lemmas to its storage kind. Span facts
require a valid view with the exact element width and writable mode; store facts accept a
replacement view and preserve memory. Reference and object facts require the replacement
reference to form, null included for an object.
These facts do not make an uninitialized slot readable or grant backing-memory authority.

Binders parameterize the generated declarations, including memory stores for symbolic arguments:

```lean
import CIL.Safety.LoopScaffold

/-- Returns its 32-bit argument. -/
def body : CIL.Method := { code := [.arg 0, .ret], locals := [], returnsValue := true }

bind_entry entry (value : CIL.W32) := body
  with [.scalar (.i32 value)] from CIL.Safety.Memory.empty
```

For symbolic initial memory or reference and span arguments, append `using success`, where
`success` proves `(enterFrame body args memory).toOption.isSome = true`. The reusable
`enterFrame_isSome` theorem supplies this from `Memory.WellFormed`, `ValuesValid` and
`FrameSetupFits` premises. The generated frame and memory are exact projections of that checked
allocation, with no default state or unchecked adapter. Numeric `homeN` declarations require the
frame's local list to reduce, as do typed slot and home facts; this form leaves that layout opaque.
The command does not infer allocation premises or generate invariant-preservation verification
conditions.

When the success premises are available as rewrite facts, use `simplifying [facts]` instead of
`using`. This derives an explicit frame and memory expression and checks the resulting entry
equation, allowing stepping to inspect the local slots:

```lean excerpt Examples/Proofs/SpanDrain.lean
bind_entry entry (memory : Memory) (view : SpanView)
    (valid : view.validate memory = .ok ()) (width : view.width = 4)
    (readOnly : view.writable = false) := Extracted.method0
  with [.bufferSpan view] from memory
  simplifying [valid, width, readOnly]
```

Facts must suffice to derive a successful entry; unresolved allocation is an error. This uses the
checked allocator and does not assume a frame layout. The normalized `entry.frame` takes only the
binders its layout mentions, here `entry.frame memory view`, while `entry.memory`, `entry.result`
and `entry.checked` take them all. Frame setup is normalized once: the proof
that computes the frame also proves `entry.checked`, which the kernel checks against the
generated definitions. For an applied body such as `(body width mode)`,
include its defining name in `simplifying [body, facts]`.
The [span loop](../Examples/Proofs/SpanDrain.lean)
proves method invocation, repeated slicing and parameter reassignment, termination and exact caller
memory preservation for any valid readonly integer span. Empty spans are included. It requires no
read authority or initialization because the method only observes length and constructs subviews.
Its stepping uses generated home facts and `cil_checked`, the shared simplification set for
successful checked values and typed home operations. The set preserves unresolved validity checks
and does not unfold instruction dispatchers. Buffer-span length, indexing and slicing have direct
step equations retaining their memory, bounds and capability checks.

A method whose numeric locals allocate homes in symbolic memory adds `allocating wellFormed`,
where `wellFormed` proves `memory.WellFormed`; `simplifying [facts]` stays optional:

```lean excerpt Examples/Proofs/SpanSum.lean
bind_entry entry (memory : Memory) (view : SpanView) (wellFormed : memory.WellFormed)
    (valid : view.validate memory = .ok ()) (width : view.width = 8)
    (readOnly : view.writable = false) := Extracted.method0
  with [.bufferSpan view] from memory allocating wellFormed
  simplifying [valid, width, readOnly]
```

Each home is an opaque reference, so `entry.frame` takes the binders its layout mentions followed by
one `homeN : Reference` per numeric local, here `entry.frame memory view home0`. `entry.checked`
proves there exist homes and an entered memory with their `entry.Checked` evidence, a structure
whose facts a proof selects by field:

- `setup`: `enterFrame` returns exactly that frame and memory;
- `numericN`, one per home:
  [`NumericEntryHome`](../CIL/Safety/NumericLocals.lean) `memory entered kind number home`
  (allocated at or above `memory.nextIdentity` and below `entered.nextIdentity`, holding its
  initializer's bytes, writable);
- `entryMemory`: [`EntryMemory`](../CIL/Safety/NumericLocals.lean) `memory entered` (caller memory
  kept below its watermark, identities grown, well formed);
- `frame`: for every footprint the entered memory starts a
  [`LoopFrame`](../CIL/Safety/LoopFrames.lean) over the frame's locals, each home remembered as its
  initializer and every other local as `none`.

A proof opens it with `obtain ⟨home0, entered, enter⟩ := entry.checked ...` and reads
`enter.setup`, `enter.frame` and the other fields by name; the loop tactics read the fields of an
`entry.Checked` hypothesis as they read hypotheses. This form generates no
`entry.result`, `entry.memory` or `homeN` abbreviations, while span, root and object slots still
get `slotN`, `loadN` and `storeN`. `entry.setup` is the setup equation given each home's allocation
equation `madeN` and `kept`; it is the proof that derived the frame, so `entry.checked` reuses it
instead of normalizing frame setup again. Homes are threaded through
[`make_numeric_entry_local`](../CIL/Safety/NumericLocals.lean), and a fact `valid : view.validate
memory = .ok ()` is also supplied in the memory after the homes through
[`SpanView.validate_below`](../CIL/Safety/FrameMemoryBelow.lean), so an assigned span parameter
stores without restating its validity. Every other local must allocate nothing: a numeric local
without a checked initializer, a vector argument home or a numeric parameter home is rejected.
[SpanSum](../Examples/Proofs/SpanSum.lean), [FillWords](../Examples/Proofs/FillWords.lean),
[Struct](../Examples/Proofs/Struct.lean), [Countdown](../Examples/Proofs/Countdown.lean),
[CountCalls](../Examples/Proofs/CountCalls.lean) and [CountUntil](../Examples/Proofs/CountUntil.lean)
enter this way, the last three from `Memory.empty` with `Memory.empty_wellFormed`. The body may
be a `bind_method` name: setup unfolds each definition that only names another constant, down to
the extracted method.

`bind_entry` gives `entry.frame` and, for the `simplifying` form, `entry.result` and
`entry.memory` the `cil_loop_unfold` simp attribute in the current scope, and `bind_cutpoint` gives
it the generated state, so the loop tactics unfold them without naming them; see [loop
verification conditions](PROOFS-STEPPING.md#loop-verification-conditions). The slot facts
`entry.loadN` and `entry.storeN` instantiate `cil_checked` lemmas that stepping already uses, so
loop proofs need not pass them.

`cutpoint stack memory` constructs the loop state; binders before `:=`, such as the home
references of an allocating entry's frame, come first. `cutpoint.checked` proves the selected
instruction satisfies the predicate and is its unique match. Missing or ambiguous matches are
errors. The predicate locates an instruction; it does not prove that it is a loop header or that
execution reaches it. The loop proof establishes those properties.

For repeated instruction shapes, `bind_cutpoint name := body at location matching predicate
with frame` checks that particular instruction rather than requiring a unique predicate match.
`location` is an emitted instruction index, not a raw CIL byte offset. Reuse `bind_loop` from
`CIL.StructuralLabels` to select nested or sequential loops:

```lean extracted
bind_loop outer := Extracted.method0 [0]
bind_loop inner := Extracted.method0 [1]
bind_cutpoint cutpoint (frame : Frame) := Extracted.method0 at inner.latch matching
  (· matches .brnonzero _) with frame
```

Structural loop occurrences are ordered by head index. Out-of-range locations and wrong instruction
shapes are rejected. Both forms accept binders for symbolic frames, and
`with frame, stack, memory` fixes the stack and memory too, so the generated state is the loop
head itself, such as the guard stack `[.scalar (.i32 (BitVec.ofNat 32 state.view.length))]` of a
span loop, with no separate header definition.

[Countdown](../Examples/Proofs/Countdown.lean) uses these commands without literal frame layouts,
allocation identifiers or instruction offsets. The author still supplies the invariant, measure,
specification and preservation proof using the existing checked loop tactics. Only requesting proofs
elaborate the scaffold; ordinary extraction certificates do not grow.

`CIL.Safety.LoopVC` supplies bounded verification-condition generation for explicit loop paths.
`cil_store_vc updated stored loaded writable := kind value using ready` derives numeric-store
progress, readback and retained write authority, then exposes the post-state proof obligation.
`cil_loop_continue next [facts]` checks the path with `cil_loop_steps`, whose facts include those
gathered from the context, infers its cost, and leaves
invariant-preservation and strict-measure-decrease goals. The [loop entry
rules](PROOFS-STEPPING.md#loop-verification-conditions) compose frame entry, the first path and
these obligations into the method's own theorem. Failed encoding, access, path, invariant or
decrease obligations cannot produce a successful proof. The author supplies branch cases, next
states, invariants, measures and any remaining arithmetic. This is not an invariant discovery
engine.

[FillWords](../Examples/Proofs/FillWords.lean) is a larger result: its contract describes an
arbitrary-length buffer fill, termination and preservation outside the writable region. See [buffer
contracts](PROOFS-BUFFERS.md) for its memory preconditions.

## Move a run that starts inside a region

Embedding relates whole bodies. When only a suffix is shared, `CIL.Safety.RegionRun` cuts the rest
away first. `RegionClosed program region` says fallthroughs, targets and callee entries of region
instructions stay in the region; `regionClosedCheck` decides it for a region listed as `(method,
lower)` suffixes (`inStarts`). `AgreesOn program other region` says `other` has the same methods and
metadata and the same instruction at every region pc; `AgreesOn.set` and `code_agrees_of_drop` build
it for one replaced body. Then `run_congr_region` gives equal runs from any region pc, faults
included. Masking the code outside the region with `.unsupported` makes it dead for `Embeds`, so
`run_refines` carries the suffix run on to a body with a different prefix, for example a suffix
after inline code to the same suffix after a helper call, one pc earlier.

For a long suffix, import `CIL.Safety.Embedding.Suffix` and use
`CIL.Embedding.BodyRefines.of_relocated_suffix`. It uses one list equality: `actual.code.drop start
= (expected.code.drop lower).map (Op.relabel (fun pc => pc - lower + start))`. The expected prefix
must contain only dead instructions. All branch targets in the suffix must be at least `lower`. The
constructor also requires equal method metadata, equal static descriptor lists, and equal static
lookups at each moved pc. If `lower = 0`, `start` must also be zero to preserve method entry.

The resulting map, `suffixRename lower start`, sends prefix pcs to zero and suffix pcs to `pc -
lower + start`. Pass the proof to `ProgramRefines.set_body` and then `run_refines`. This avoids
evaluating `sites` and `pick` for each instruction, so a suffix of a hundred instructions with
conditional, switch and native branch targets checks within the default heartbeat limit.

## Bind bodies to the extraction

Reusable execution and contract theorems are stated over a generic program and bound to each
extraction by a method-body equality. Prove those equalities with `cil_body` (from
`CIL.MethodBinding`, also imported by `CIL`) instead of `rfl`:

```lean
import CIL.MethodBinding

/-- The body a proof expects at index 1 of the program. -/
def double : CIL.Method :=
  { code := [.arg 0, .arg 0, .add, .ret], locals := [], returnsValue := true }

def program : CIL.Program := [{ code := [.ret], locals := [], returnsValue := false }, double]

-- Against an extraction the goal reads `Extracted.program[1]? = some double`.
theorem found : program[1]? = some double := by cil_body
```

`cil_body` runs `rfl`, so the proof is the same kernel-checked `Eq.refl`. Only when `rfl` fails does
it evaluate both closed sides and report, for each differing `Method` field, the first differing
index, both elements and both lengths, instead of only `rfl`'s type mismatch:

```text
cil_body: rfl could not prove the method-body binding
method index 1
field code: first difference at index 1 (left length 6, right length 6)
  left:  CIL.Op.brzero 10
  right: CIL.Op.brzero 4
```

The left side is the extraction's body. An index past the end of the program is reported with the
program's length. The diagnostic is computed after the failure through compiled evaluation and is
never proof evidence; it also works for `Method = Method` goals.

### Methods by signature

Extraction numbers methods by the reachable call graph, so adding or reordering a callee renumbers
unrelated methods and breaks every literal index. Name them by their exact emitted signature
(`Extracted.signatures`) instead, with `import CIL.MethodIdentity`:

```lean excerpt Examples/Proofs/CountCalls.lean
bind_method countCalls countBody := "System.UInt32 Examples.Loops::CountCalls(System.UInt32)"
bind_callee decrement decrementBody :=
  "System.UInt32 Examples.Loops::Decrement(System.UInt32)" from countBody
bind_call decrementSite := decrement from countBody

def decrementContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x - 1

theorem decrement_holds : decrementContract.Holds Extracted.program decrement := by
  rintro x m -
  refine MethodContract.Holds.intro m _ ?_ (Confined.refl _ m) rfl
  cil_checked_steps
```

`bind_method` defines `countCalls` (the index), `countBody` (the extracted body) and the `rfl`
theorems `countCalls.signature` and `countCalls.found` (`@[cil_code]`). `bind_callee` also requires
the parent to call that method and adds `decrement.call`, the instruction at its call site
(`from countBody [k]` selects one of several); expected bodies take the index as a parameter, so
`.call decrement 1` survives renumbering. A statement about the callee alone runs it by that index,
as in `invoke Extracted.program 8 decrement [.scalar (.i32 x)] memory`, which returns
`.ok (memory, [.scalar (.i32 (x - 1))])`. [CountCalls](../Examples/Proofs/CountCalls.lean) proves
the contract above and the loop that calls the helper through it.
`method_named "sig"` is the bare index as a term. A missing signature lists the methods with the
same name, or every method; a duplicate lists each index; a parent that does not call the method
lists what it does call:

```text
no extracted method has signature
  System.UInt64 Examples.Overloads::Pick(System.Int64)
methods named Pick:
  [3] System.UInt64 Examples.Overloads::Pick(System.UInt64)
  [4] System.UInt32 Examples.Overloads::Pick(System.UInt32)
```

When a helper's name is not stable, bind it by call shape instead: `bind_callee left leftBody :=
call 2 from rootBody [1]` binds the second call in `rootBody` with two arguments, and emits the same
theorems with the signature read from the table. Without `[k]` there must be exactly one such call;
otherwise the error lists each site's pc and callee.

The signature is the Cecil full name, matched exactly. Resolution only locates an index; the body is
still bound by the kernel and the extraction certificate. `bind_import` reports a missing import
signature the same way, listing imports with the same name or every import, and says when the
extraction has no imports.

### Loop heads and call sites

Inside a method, name positions by structure instead of by pc, so a statement inserted elsewhere
moves the label with the code (`CIL.StructuralLabels`):

```lean extracted
import CIL.StructuralLabels

bind_loop reduce := rootBody [1]     -- the second loop head in pc order
bind_call after := step from rootBody [1]

theorem body : (rootBody.code.drop reduce).take 4 = [.local 0, .const32 3, .sub, .setLocal 0] := rfl
```

A loop head is the target of a branch at the same or a later pc. `bind_loop` defines `reduce` and
`reduce.latch`, the last pc branching back to it, and `reduce.backEdge` checks both. `bind_call`
names a `.call` to a bound method and adds `after.call`. The `[k]` is needed only when there are
several; without it every candidate is listed rather than the first one taken:

```text
rootBody has 2 loops; select one with [i]:
  [0] head pc 3, back edge from pc 5
  [1] head pc 6, back edge from pc 7
```

Labels read the compiled layout, so a compiler that rotates a loop moves its head; a cutpoint that
must survive that, such as `Examples/Proofs/Countdown.lean`, keeps a unique-instruction predicate.

### PDB local names and source locations

When a portable PDB matches the assembly (next to it, or embedded), extraction also writes
`Symbols.lean`, the module `ExtractedSymbols`; `Extracted.lean` is byte-identical either way. A
proof that imports it can name locals by their C# names, resolved in the scope that contains a pc:

```lean extracted
import ExtractedSymbols

theorem stores :
    sumBody.code[atWide + 1]? = some (.setLocal (local_named sum "carry" at (atWide + 1))) := rfl
```

A name used for one slot needs no `at`; a name the PDB gives two slots, such as `carry` declared in
two sibling blocks, is an error listing each slot and range until `at pc` picks the innermost scope
containing it. Compiler temporaries and values the compiler keeps on the stack have no name and keep
their index; a missing name lists the method's named locals. Importing `ExtractedSymbols` without a
matching PDB fails verification with that reason, naming the assembly and method. Consumer packages
import it like `Extracted`, directly or through their own modules, in `leancil verify --proof-root`
and `leancil verify-batch`. Only proofs whose imports reach it compile it, replay it and bind its
hash into their cache key, so a PDB-only change rechecks them and no symbol-free proof.

With the module imported, `cil_body` and `cil_embed` failures end with the nearest sequence point of
the actual pc they report:

```text
source of actual pc 23: Names.cs:12:9
```

Extraction errors for an unsupported instruction add `Source: Names.cs:16:21` after the method
whenever the PDB is present, imported or not. Source paths are relative to the directory the method
documents share. Without a PDB every message is unchanged.

### Bodies modulo dead code

A profile can make the extractor emit dead `.unsupported` blocks that shift every later branch
target, which breaks a `cil_body` equality even though reachable behaviour is unchanged. `cil_embed`
(from `CIL.Embedding.Tactic`) proves the weaker `MethodEmbeds` relation instead: every live
instruction of the literal body appears in the extracted method at a mapped pc, with its code
targets mapped the same way and its fallthrough kept adjacent. Keep the proof over the literal body
and transport it with the lemmas in `CIL.Safety.Embedding.Simulation`:

```lean
import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Simulation
import CIL.SymbolicExecution

open CIL.Safety
open CIL (Method MethodEmbeds)

/-- Returns argument 1 on both paths; pc 4 is reached only by the branch. -/
@[cil_code] def body : Method := {
  code := [.arg 0, .brzero 4, .arg 1, .ret, .arg 1, .ret]
  locals := [], returnsValue := true }

/-- `body` as a profile-specific extraction emits it, with a dead block before the branch target. -/
def extracted : Method := {
  code := [.arg 0, .brzero 6, .arg 1, .ret,
    .unsupported "Unreachable under selected profile", .const32 9, .arg 1, .ret]
  locals := [], returnsValue := true }

theorem bound : MethodEmbeds [extracted] 0 body := by cil_embed

-- A run proved over the literal body holds for the extraction with the same fuel.
example {fuel : Nat} {args : List Value} {memory : Memory} {result : Memory × List Value}
    (run : invoke ([extracted].set 0 body) fuel 0 args memory = .ok result) :
    invoke [extracted] fuel 0 args memory = .ok result := bound.invoke run
```

An expected body can be a shared template with local flag and callee parameters. Use `cil_embed
[sse, avx, called]` when those hypotheses equate the parameters to the extraction's concrete flags
and callee indices. The tactic rewrites only the supplied facts before alignment and unfolds local
definitions; it does not infer flag equalities from the extracted code. Relevant parameters that
remain open are rejected. The rewrite proof and the complete instruction map are kernel checked,
including branch targets and callee indices. The no-argument form still handles closed bodies
directly.

One template and one open theorem about it thus bind to every valid profile, including shifted
branch targets, without restating the body for each profile. An irrelevant open argument may be
removed by supplying the definition that ignores it in the fact list; this is justified by
reduction, not an assumption about that argument's value.

`bound.certificate` transports an `InvocationCertificate` and `bound.descriptors` the program's
static descriptor list; `ProgramRefines.set` composes several bound methods. Named exceptions
transfer too: `bound.raises` transports `Raises`, `bound.holds` an `OutcomeContract.Holds` with both
clauses (from `CIL.Safety.Embedding.Outcomes`), and `Embeds.invoke_raise` states the actual fault,
whose pc is the one the map assigns in the throwing method. Other faults, including fuel exhaustion
and `.unsupported`, do not transfer. The pc map is computed outside the kernel and then checked by
it, so a wrong map is rejected, not trusted. A changed reachable instruction or an inserted live one
is reported by expected and actual pc:

```text
cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Op.brzero 4
  renamed:  CIL.Op.brzero 6
  actual:   CIL.Op.brzero 4
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 4; actual pc 4 (CIL.Op.const32 0x00000009#32) is not the image of any live expected pc
```

The kernel check takes about 0.12 s for a 202-instruction body and 1.3 s for 1,414 instructions. See
[method-body embedding](SOUNDNESS-EXECUTION.md#method-body-embedding) for the exact conditions and
limits.

An extraction can also declare locals the literal body never uses. Exact-memory embedding covers
dead locals that trail the body's own locals and are references or spans initialized to their empty
value or left unmodeled. These cover byref, pointer, `Span<T>` and `ReadOnlySpan<T>` locals; spans
require an element width greater than zero and less than `2^64` bytes. For those, `cil_embed` proves
`MethodEmbedsDeadLocals` instead, and the same proof covers extractions with and without them (from
`CIL.Safety.Embedding.DeadLocals`):

```lean
import CIL.Embedding.Tactic
import CIL.Safety.Embedding.DeadLocals

open CIL

/-- Reads its one local, a null reference, then returns argument 0. -/
@[cil_code] def stored : Method := {
  code := [.local 0, .pop, .arg 0, .ret]
  locals := [.nullRef], localKinds := [.reference], returnsValue := true }

/-- `stored` with two unused reference locals after its own, as a profile can extract it. -/
def storedDead : Method := {
  stored with
  locals := [.nullRef, .nullRef, .unmodeled]
  localKinds := [.reference, .reference, .reference] }

theorem stored_invocation (memory : Safety.Memory) (value : W32) :
    Safety.invoke [stored] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps

theorem stored_dead_embeds : MethodEmbedsDeadLocals [storedDead] 0 stored := by cil_embed

theorem stored_dead_returns (memory : Safety.Memory) (value : W32) :
    Safety.invoke [storedDead] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) :=
  stored_dead_embeds.invoke (stored_invocation memory value)
#print axioms stored_dead_returns
```

`.raises`, `.method_holds` and `.holds` transfer as for `MethodEmbeds`. A numeric dead local, such
as a flag only one architecture's path reads, requires the allocation refinement below: its home
shifts later allocation identities. A dead local before a kept one also changes the kept local's
operand. Span slots retain their width, mutability and empty or unmodeled state; padding does not
create or change any allocation.

For numeric or interspersed dead locals, keep the extracted declarations and original local indices
in the expected body and use ordinary `MethodEmbeds`. Unreachable code can still be omitted or
marked `.unsupported`; declaring an unused numeric local continues to allocate its home. This
preserves the identities of later parent and callee allocations and allows exact-memory contract
transport. The four-limb multiply fixture follows this route: its scalar body retains all 22 word64 and
four vector256 homes used across its architecture-specific paths. This route retains exact final
memory and remains useful when a postcondition names fresh references.

To omit numeric or interspersed declarations from the proof body, import
`CIL.Safety.AllocationRefinement` explicitly; `import CIL` leaves this optional proof library
unloaded. Its dependencies still undergo the normal build and kernel replay when a consumer uses
them. `LocalIndexMap.keep`, `.skip` and `.nil` describe the retained declarations in order.
`LocalDeclarations` checks matching retained kinds and initializers and requires each inserted
initializer to satisfy `InitializerFits` for its kind. `LocalDeclarations.skip` takes the kind,
initializer and this proof before the remaining declarations. It admits valid scalar, vector and
aggregate values, and null managed slots; unmodeled values remain supported. Private initialized
homes are written outside the entire mapped allocation image, preserving caller bytes and
permissions. `MethodRenaming` checks the target code's relocated local operands; method indices,
call targets, profiles, return metadata and static sites stay exact. `ProgramRenaming` supplies this
correspondence for every source method. The target is the extraction with the additional dead
declarations.

This entry route requires `OrdinaryFrame` on both sides: `opaqueVectorLocals`, `vectorArgs` and
`parameterHomes` are empty. Retained initializers stay exact, including initialized numeric helpers;
their successful setup is derived from the actual source execution. Local widths must fit the native
range; span element widths must be positive and less than `2^64`. These are explicit, checked
metadata conditions, not assumed target frame-entry success. The audited four-limb Multiply body across
all fourteen profiles has 22 word64 and four vector256 unmodeled locals. Its reachable helper
method4 has an initialized word64 zero local in every profile. The full extracted programs have no
opaque, vector-argument or parameter homes; the relation preserves that helper initializer rather
than treating it as unmodeled.

Starting from the same well-formed memory with bounded static bindings,
`ProgramRenaming.invoke_scalars` transfers a successful checked invocation with the same fuel and
exact scalar results. Its final memories satisfy `BytesBelow` at the initial allocation counter:
the caller's allocations, bytes and authority agree exactly. They satisfy `SlotsAgreeBelow` too:
a caller field holds the same reference in both wherever the source holds null or a caller
reference, while a field holding a fresh object may name another identity in the target.
`invoke_confined` carries a `MemoryBelow` preservation claim, field references included, from the
initial memory to the target's final memory. `ProgramRenaming.raises` transfers a named exception
and additionally requires valid initial arguments. These theorems use the proved complete
dispatcher internally. The allocation relation extends through local setup, nested calls,
constructors, static allocation and `stackAlloc`; frame ownership and expiry remain checked.

`MethodContract.Holds.of_allocationRenaming` transfers the original complete contract, including its
precondition and footprint. Supply proofs that the precondition establishes well-formed memory,
bounded static bindings and bounded string literals (`Memory.LiteralsBounded`), that every output its postcondition admits encodes as scalars, and that
its postcondition is preserved by `BytesBelow` and `SlotsAgreeBelow` on the initial caller prefix,
given that the target's final memory has allocated past that prefix. The adapter derives
confinement from the actual paired executions; it does not replace the contract with a weaker one.
A contract whose precondition names only fields and objects does not establish memory readiness;
`MethodContract.fromReadyMemory` adds it to the precondition, and `Holds.fromReadyMemory` proves
the result from the contract's own proof, so the transfer states the contract for every initial
memory a caller can hold ([LinkedNodes](../Examples/Proofs/LinkedNodes.lean)).

This is not exact-memory transport: extra homes change counters and fresh references. Arbitrary
reference results and postconditions naming fresh allocations need a statement modulo the allocation
relation. The existing `MethodEmbedsDeadLocals` tactic continues to handle its exact-memory subset.

### Generated profile templates

Create ordinary extractions for the profiles your proof supports, then combine them:

```sh
leancil extract Dispatch.dll 'Dispatch::Choose(uint,uint)' scalar scalar
leancil extract Dispatch.dll 'Dispatch::Choose(uint,uint)' sse42 x64-sse42
leancil extract Dispatch.dll 'Dispatch::Choose(uint,uint)' v3 x64-v3
leancil templates shared scalar sse42 v3
```

The command reruns exact extraction checking for every input and requires the same assembly bytes.
`shared/Templates.lean` defines each method once, with a profile parameter, parameters for the
feature flags it reads, and managed callee indices keyed by full method identity. Every original IL
instruction keeps its pc. Conditional instructions and excluded paths become `if` expressions and
unsupported padding; `cil_instruction_equations` generates kernel-checked equations for every pc.

`TemplateBindings0.lean`, `TemplateBindings1.lean`, and so on each import `Extracted` and
`Templates`. Each binding proves `Extracted.program[i]? = some (Templates.methodN ...)` by `rfl`,
including all metadata and callee indices. Compile a binding only against its corresponding
extraction, recorded in `templates.json`. Add the shared module and selected binding module to your
proof package, import that binding from the consumer proof, and use ordinary `leancil verify` with
that extraction and proof package. The templates command generates proof source; it does not replace
Lean checking or verification of the extraction.

Only the input profiles receive extraction bindings. Unselected combinations of observed flags
produce unsupported instructions, and no correctness claim about another extraction follows from
generating a template. The full profile remains an explicit parameter; a behavioral proof must
relate its feature fields to the flag arguments it uses. Profiles that produce different metadata,
different instruction counts, or different instructions under identical observed flags are rejected.
Static-site metadata, imported callee slots and the model's `newVector256` constructor form are
currently unsupported in template generation.


### Instruction equations for parametric bodies

A body written once for every profile takes its feature flags and callee indices as parameters and
keeps each feature-dependent instruction as an `if`, padding the other profile's side with
`.unsupported` so every profile has the same pcs. `cil_instruction_equations` (from
`CIL.InstructionEquations`) states one `@[cil_code ↓]` equation per pc for such a body, the same
`code[pc]? = some op` equations it states for each method of an extraction, so a lookup rewrites by
one equation instead of unfolding the body:

```lean
import CIL.InstructionEquations
import CIL.Safety.SymbolicExecution

abbrev unreachable : CIL.Op := .unsupported "Unreachable under selected profile"

def body (sse42 avx2 : Bool) (callee : Nat) : CIL.Method :=
  { profile := { sse42, avx2 }, returnsValue := true, locals := [], code := [
    .feature .avx2, .brzero 4,
    if avx2 then .call callee 0 else unreachable,
    if avx2 then .ret else unreachable,
    if avx2 then unreachable else .ret] }

cil_instruction_equations body

-- body_instruction2 (sse42 avx2 : Bool) (callee : Nat) :
--   (body sse42 avx2 callee).code[2]? = some (if avx2 = true then .call callee 0 else unreachable)
-- cil_lookup fetches through the equation and decides the `if` from the fact.
example (sse42 avx2 : Bool) (callee : Nat) (wide : avx2 = true) :
    ∃ op, (body sse42 avx2 callee).code[2]? = some op ∧ op = .call callee 0 :=
  ⟨_, by cil_lookup [wide], by with_reducible rfl⟩
```

A body whose code length depends on a parameter, such as an `if` around a whole block, is rejected
with the first pc that is not determined. Only the kernel checks the equations. The command also
declares `body_suffix{start}`, the code from every 16th pc on, and `body_suffix{start}_placed`, and
proves each equation from the suffix that starts its block, so the equations cost time linear in
the body's length: about 6,400 heartbeats each from 250 to 4,000 instructions, as
[instruction lookups](performance/InstructionLookups.md) records.
