# Method contracts and exceptional outcomes

This page describes how to state a method's interface as a `MethodContract` or `OutcomeContract`,
prove it, and use it at call sites, across class instances, struct construction, exceptions,
forwarders and separately extracted libraries. Read this page when a proof crosses a call or
publishes a guarantee for callers. [Stepping](PROOFS-STEPPING.md) covers the instruction-level
tactics these sections use.

## Compose calls through contracts

State a callee's interface as a `MethodContract` (`CIL.Safety.MethodContract`) and prove the caller
against it, so the caller's proof survives a reimplementation of the callee:

```lean
import CIL

open CIL.Safety
open CIL (W64)

/-- Three 8-byte cells: two inputs read as words and one output. -/
structure AddInput where
  a : Reference
  b : Reference
  res : Reference
  x : W64
  y : W64

def addContract : MethodContract AddInput where
  args input := [.reference (.address input.a), .reference (.address input.b),
    .reference (.address input.res)]
  pre input m := read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()
  footprint input := [(input.res, 8)]
  post input _ final values :=
    values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)
```

The caller's theorem takes the callee's contract as a hypothesis:

```lean extracted
theorem root_holds (add : addContract.Holds Extracted.program addTo) :
    rootContract.Holds Extracted.program root
```

[CountCalls](../Examples/Proofs/CountCalls.lean) proves a loop this way;
`decrementContract.Holds Extracted.program decrement` is its only assumption about the helper.

| Field | States |
| --- | --- |
| `args` | The argument values the input encodes |
| `pre` | Formation, authority and the permitted aliasing; the example lets `res` overlap either input |
| `footprint` | The `(reference, width)` intervals the method may change; entries may overlap |
| `results` | With a typed output, the returned values the output encodes ([typed results](#type-the-result)) |
| `post` | The meaning of the result and the memory guarantees |

`Holds` is `Ensures` with the footprint added to the postcondition (`Holds.ensures`). Fuel stays
existential, so a caller never depends on a callee's step count. The program fixes the profile
and the contract fixes none ([profiles](#carry-a-contract-across-profiles)).

### Footprints and confinement

`Confined footprint before after` is the memory guarantee of `Holds`: earlier allocations and write
authority are unchanged, and bytes and read authority change only inside the footprint (a write
grants read access to what it wrote).

| Need | Use |
| --- | --- |
| Compose two confined changes under one footprint | `Confined.trans` |
| Widen to a footprint that contains every entry | `Confined.widen` |
| Confine a checked write whose interval is an entry | `Confined.write` |
| Keep write access to memory that existed before the call | `Confined.access_write` |
| Keep a read of older memory that lies wholly outside the footprint | `Confined.read_eq` |
| Widen to a footprint whose entries enclose this one | `Confined.widen_within` |
| Confine a write that lies inside one entry | `Confined.write_within` |
| Keep a checked read of older memory apart from every entry | `Confined.read_apart` |
| Keep every byte of an allocation no entry names | `Confined.cells_apart` |
| Keep remembered words | `WordSnapshots.after_confined` (`CIL.Safety.ConfinedSnapshots`) |

`Within inner outer` states that an interval lies inside another of the same allocation, so four
limb writes satisfy a contract that declares one 32-byte output. `Apart r width entry` states that
two intervals share no byte, in different allocations or at disjoint offsets of one;
`Confined.read_apart` takes the allocation's age from `WellFormed`. `Outside.nil` and
`Outside.cons` are simp rules, so `simpa using ⟨hr, hq⟩` closes a word footprint from per-word
`OutsideWord` facts; `Outside.word` builds it as a term.

A store through an argument reference needs only write access: `store_word64 word writable` gives
the `write`, the `storeValue` step fact and the readback of its encoding, so `Confined.write` and
the stepping tactics use the same equation.

A callee with locals writes its own frame too. List those slots in the footprint while executing,
then drop them with `Confined.forget_fresh` and cover frame entry with `Confined.then_below`.
`framed.after_leaveFrame owned` covers teardown, given that every identity the frame owns is at
least the caller's `nextIdentity`. A method with locals that changes no caller memory ends with
`MemoryBelow memory.nextIdentity memory final` instead of `final = memory`;
`MemoryBelow.compose_invoke`
composes consecutive such calls ([span contents](PROOFS-BUFFERS.md#describe-span-contents)).

### Remember numeric locals

`LocalSnapshots memory slots known` (`CIL.Safety.LocalSnapshots`) remembers the values of locals
of every numeric kind, vectors and int32s included; `known index` is the value a load of that
local pushes, or `none`.

| Need | Use |
| --- | --- |
| Step a `.local` load | `snapshots.load value specified`, a step fact the stepping tactics take |
| Step a numeric store and get the updated snapshots | `LocalSnapshots.store` |
| Keep snapshots across a call confined apart from the homes | `LocalSnapshots.after_confined` |
| Keep snapshots across a write, or memory that keeps old allocations | `after_write_apart`, `after_below` |
| The typed read of a remembered local whose slot is known | `snapshots.read_at specified slot` |
| That read for a vector | `read_vector128`, `read_vector256`, `read_vector512` |

The vector reads are stated as `read memory home 16 1 = .ok (numberBytes bits.toNat 16)` and its
wider forms. A snapshot that overlaps a callee's footprint is not kept: restate it from the
callee's postcondition.

Stores need each local's writable byte home:

| Evidence | Source |
| --- | --- |
| `CompleteWritableHomes` | `unknown_frame_setup`, for numeric locals with unknown initial contents |
| `NumericHomes` | An initialized numeric frame |
| `WritableHomes` | The `writable` projection of either bundle |

- `CompleteWritableHomes` gives every declared local a typed writable home (`home_at`). It does
  not claim the home is readable or initialized.
- `NumericHomes` gives the same through `NumericHomes.complete`.
- `WritableHomes` may skip slots, so `home_at` needs separate evidence that the requested slot
  has a byte home.

Pass the `writable` projection to the general snapshot lemmas.

### Walk local stores and loads with snapshots

The snapshot forms of the stepping tactics (`CIL.Safety.LocalSnapshotSteps`, part of `import CIL`)
take numeric local stores and loads through a `LocalSnapshots` hypothesis and pass the updated
snapshots to each later step. A load pushes the latest remembered value; a store replaces it.

#### Tactic forms

`snapshots` proves `LocalSnapshots memory frame.locals known` at the goal's current memory. The
fact list is required; write `[]` when it is empty.

| Goal | Tactic | The walk ends |
| --- | --- | --- |
| A checked `run` equality, or `∃ after, run ... = .ok (after, result)` | `cil_checked_steps (snapshots := snapshots) [facts]` | At the first unsupported step or unproved premise |
| `WP`, or an existential successful execution | `cil_contract_steps (snapshots := snapshots) [facts]` | At the first step that fails |
| The same | `cil_contract_steps (snapshots := snapshots) [facts] until continuation` | When `continuation` closes the goal, or at the first step that fails |
| The same | `cil_contract_steps (snapshots := snapshots) n [facts]` | After at most `n` steps |

The two forms differ:

| | Checked form | Contract form |
| --- | --- | --- |
| Local instructions taken from the snapshots | `.local`, `.setLocal` | `.local`, `.setLocal`, `.vectorLocal`, `.setVectorLocal` |
| Other instructions | Ordinary checked steps and the return | Ordinary contract steps: supplied step facts, calls and returns |
| Finds each store's home | From the premises in context | From a homes hypothesis ([required context](#required-context)) |
| Restates context facts after a store | `access` equations only; byte-value facts stay at the old memory | `access` equations and the [caller facts](#facts-the-contract-form-carries) |
| Prepares step facts again after a store | No | Yes |
| Follows a supplied store | No | Yes |
| When it takes no step | Fails with `Snapshot stepping took no step; justify the local premises` | Fails with `Snapshot contract stepping took no step`; the counted form succeeds without stepping |

In `facts`, pass the step facts the path needs and, for loads, the named definitions of the
snapshot map or equations selecting an index of it. Lookup simplifies these and natural-number
offsets without unfolding unrelated arithmetic definitions. In the contract form a snapshot load
or store leaves a numeral program counter.

#### Required context

For a store of `value` into local `index` at memory `memory`, the checked form proves these
premises from hypotheses and `facts`:

- `WritableHomes` for the frame's locals, also as a `CompleteWritableHomes` or `NumericHomes`
  hypothesis;
- `memory.WellFormed`;
- the home lookup `frame.locals[index]? = some (.bytes kind home)`;
- write access, `access memory home (localWidth kind) 1 true = .ok ()`.

The contract form finds the home itself:

| Homes in context | How the home is found |
| --- | --- |
| `CompleteWritableHomes` or `NumericHomes` at the current memory, over the frame's locals | Directly; the slot list may be opaque |
| The same at an earlier memory `entered`, such as the frame's entry memory | Through a link from `entered` to the current memory |
| Homes for the locals after leading slots without a byte home | At the shifted index (`WritableHomes.after_skipped`) |
| An explicit `WritableHomes` bundle | From the individual slot and access facts, as for the checked form |

Each case has further requirements:

- Homes at the current memory need the current memory's `WellFormed`.
- Homes at an earlier memory need `entered.WellFormed`, the current memory's `WellFormed`,
  `entered.nextIdentity ≤ watermark` and a link: `AccessBelow watermark entered current` or
  `MemoryBelow watermark entered current`. The link carries each home's write access to the
  current memory (`CompleteWritableHomes.home_retained`). Without the link the tactic stops at
  the store.
- Homes after leading slots, as in `layout : frame.locals = .root value :: slots` with
  `NumericHomes entered boundary specs slots`, need each leading slot to be a constructor other
  than `.bytes` or to have a hypothesis `∀ kind reference, slot ≠ .bytes kind reference`.

A kind lookup that does not compute needs a supplied fact:

- For opaque `specs` in `NumericHomes entered boundary specs slots`, supply
  `specs[4]? = some spec` (`numericKinds_getElem?`) or `(numericKinds specs)[4]? = some kind`.
  The index is the local's index among the homes: its index less the leading slots skipped.
- For a local index that is not a numeral, such as the `base + 3` of a block stated at a symbolic
  local base, supply `kinds[base + 3]? = some kind` at exactly that index term. The homes must
  cover the frame's locals from the first slot; with leading slots skipped the index must be a
  numeral.

#### Names each store introduces

Each store the tactic generates, in either form, introduces:

| Name | Statement |
| --- | --- |
| `storedLocal` | The memory the store produced |
| `storingLocal` | The store's step equation |
| `localSnapshots` | The snapshots at `storedLocal`; the remembered value is stated as the value a load pushes |
| `localFormed` | `storedLocal.WellFormed` |
| `localBelow` | `MemoryBelow boundary memory storedLocal` |
| `localAccess` | `AccessBelow memory.nextIdentity memory storedLocal` |
| `localWrite` | `write memory home bytes 1 = .ok storedLocal` |

All seven take the suffix `_1`, `_2` once a name is taken, so the second store of a walk gives
`storedLocal_1` and `localSnapshots_1`.

A store whose step a supplied fact proves keeps the memory that fact chose. When the store's
premises hold, the contract form's snapshots follow it to that memory (`LocalSnapshots.store_at`)
and the store names `localSnapshots`, `localFormed`, `localBelow`, `localAccess` and `localWrite`
about it, so the loads after it continue in the same call. Otherwise the loads after it need
supplied step facts or snapshots about that memory.

#### Facts the contract form carries

After each store it generates or follows, the contract form restates the context's facts about
the memory written to at the new memory, each under the name it already has:

| Fact | Condition |
| --- | --- |
| `ValidCall`, `CompleteWritableHomes`, `AccessBelow` | None |
| `MemoryBelow` | Same watermark as the store's |
| `Contents`, `Filled`, `Writable`, `LiveObject` and the `Readable`, `Owned` and `Holds` predicates of word and reference fields | The context shows the allocation below the homes' boundary, as `reference.allocation < boundary` |
| `read memory reference width alignment = .ok bytes`, `form memory reference = .ok formed` | The same |
| A read or formed reference supplied in `facts` as a term, such as `state.loaded` | The same; it is restated at `storedLocal` (`MemoryBelow.read`, `MemoryBelow.form`) |

A fact whose condition is not shown stays at the old memory.

The contract form then prepares its step facts again at `storedLocal`. The carried `ValidCall`
forms the by-reference arguments and reads their fields there, and the restated reads supply their loads, so
`.arg`, `.fieldAt` and memory loads of caller data continue in the same call. After a store, a
word load through a `ValidCall` is stated at that store's memory, as `view.word storedLocal
offset`. `ArgumentView.word_below localBelow view old` restates a word at the memory the store
wrote to, and `ArgumentView.bytes_below` the whole range.

#### Stop a walk

`until continuation` and a step count `n` stop a snapshot walk as they stop
[plain contract stepping](#step-a-caller-through-its-callees). The counted form stops without an
error, and a call counts as one step. The count and `until` cannot be combined.

To apply a helper lemma stated over `CodeAt body start segment`, count the steps up to the program
counter where it applies, apply the lemma there, and continue with a second walk from the last
`localSnapshots`.

After a contract-form walk, a hypothesis introduced before it as `have preserved :=
MemoryBelow.refl boundary memory` states `MemoryBelow boundary memory final`. Rebuild a caller's
own state predicate once, from the restated facts and the last `localSnapshots`.

#### Facts the walk does not carry

- Neither form infers authority, initialization, or preservation across calls and unrelated
  writes.
- A call does not preserve local snapshots. Derive the snapshots after it from the callee's
  effect with the snapshot frame lemmas, such as `LocalSnapshots.after_confined`.
- A caller-specific wrapper predicate needs its own transport proof.

### Carry a contract across profiles

`MethodContract.Holds.reprofile` (`CIL.Safety.ProfileContract`) carries a contract proved for a
program whose methods all use profile `p` to `CIL.reprofile program q`, for any `q` that agrees
with `p` on the program. It has `OutcomeContract` and `HoldsCLR` forms, and `_statics` forms of
the `MethodContract` and `OutcomeContract` lemmas for a contract indexed by
`programStaticDescriptors`.

`CIL.Program.ProfileAgreement.of_flags` reduces agreement to the flags in `program.profileReads`,
which `decide` checks for concrete profiles, so one proof covers every profile in a family. For a
program with no profile reads, `empty : program.profileReads = []` discharges the premise with
`by simp [empty]`. A separate per-profile extraction is covered once it is shown equal to the
reprofiled program, by `rfl` when only the profiles differ.

`leancil export-contracts` accepts one manifest entry for such a family:

```json
{
  "method": "Library::Supported()",
  "contract": "Public.supported",
  "theorem": "Proof.family",
  "program": "Reference.program",
  "referenceProfile": "x64-sse2",
  "profiles": [
    { "profile": "x64-sse2", "artifact": "extractions/sse2" },
    { "profile": "x64-sse42", "artifact": "extractions/sse42" },
    { "profile": "x64-v3", "artifact": "extractions/v3" }
  ]
}
```

The surrounding manifest provides `schema`, `assembly`, `proofRoot` and `interface`. Each
artifact's `verification.json` selects the shared proof source under `proofRoot`. The family
theorem has the shape
`∀ q : FeatureProfile, Predicate q → contract.Holds (reprofile Reference.program q) 0`, where the
concrete predicate is decidable. Method and outcome contracts are both supported. The family
theorem concludes a reprofiled program, so it needs no second transport or handwritten
per-profile proof file.

A family entry must meet these requirements:

- The selected artifacts include `referenceProfile`, and the reference program uses it uniformly.
- Profiles are distinct built-in names and match their artifacts. A family entry cannot also
  specify `artifact`.
- Every profile proves by `rfl` that the named reference program equals the fixed reference
  program; a definition that changes with the current extraction cannot substitute another body.
- Every selected profile agrees with the reference on each profile flag the reference program
  reads, intrinsic prerequisites included. A separate checked `ProfileAgreement.of_flags`
  obligation rejects a profile that disagrees and reports the flag's name.
- The extraction is closed: family transport does not support imported-contract slots.
- Explicit type-initialization premises remain bound to each exported profile. Static-value
  assumptions are not supported. Full source-bundle verification rejects initialization premises,
  as for single-profile exports.

The export runs these checks:

- The reference extraction is checked against the same DLL, copied into a reserved generated
  module and compiled separately from author macros. Its compiled artifacts are frozen before
  author code runs and checked again afterward.
- Each profile gets its own extraction check, layout check, theorem audit and kernel replay.
  Generated proofs instantiate the predicate with `by decide +kernel` and prove the exact program
  equality with `rfl`.
- The equality and agreement statements are audited independently, so proof-source macros cannot
  replace these checks.
- Nothing is published unless all selected profiles pass. Published source bundles retain every
  selected extraction.
- Full verification extracts the selected profile and its fixed reference afresh from the pinned
  implementation DLL, then repeats the family checks before composing the caller theorem.
  Identical fixed-reference modules can reuse authenticated, source-bound compilation across
  profile workspaces; their compiled artifacts are fixed before producer proof code runs and
  checked afterward, and every selected profile retains its extraction replay and exact audit.

This manifest form covers same-flag transport only. For families whose observed branches differ,
use [profile templates](PROOFS-BINDING.md#generated-profile-templates). A family is also rejected
when extraction pruning, method numbering, instructions or metadata make a profile's program
differ from the reprofiled reference.

### Type the result

`MethodContract Input Output` adds `results : Output → List Value`, and `post` speaks of the
`Output`. `Returns` requires the returned values to equal `results out` for some `out` satisfying
`post`. Without `Output`, `results` is the identity and `post` sees the values:

```lean
import CIL

open CIL.Safety

def mixContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post input _ _ v := v = input.1 * 3 + input.2
```

### Step a caller through its callees

`cil_contract_steps [facts]` steps an existential-fuel goal through ordinary instructions and
calls. At a call it applies:

- a proved `MethodContract.Holds` theorem marked `@[cil_contract]`, or one whose proof is in
  `facts`. Contracts merely present in the local context are not selected. The theorem's program
  and method binding must match the actual call; required binding premises are checked;
- a supplied successful child invocation, with fixed or existential fuel, or an
  `InvocationCertificate`, without unfolding the helper body.

Input fields, each component of a tuple input included, are inferred from the encoded arguments;
an input that is one word or one reference is the argument as the caller wrote it. The
precondition is proved from `facts` when possible; otherwise it remains a goal before the
continuation. Without matching evidence the tactic stops at the call.

Each composed call leaves three names in the context, each with the suffix `_1`, `_2` once a name
is taken:

| Name | Holds |
| --- | --- |
| `called` | The callee's final memory |
| `output` | Its typed output |
| `call` | Its [`CallResult`](../CIL/Safety/MethodContract.lean): `call.invoked` (the invocation), `call.framed` (`Confined` to the footprint) and `call.post` (the postcondition of `output`) |

Select the fields by name; do not destructure a `CallResult` positionally.
`cil_contract_steps [facts] with memory result evidence` gives the first call it composes those
three names instead, and fails when it composes no call:

```lean excerpt Examples/Proofs/DepositBoth.lean
cil_contract_steps [holds, depositContract, firstOwned]
  with middle values firstCall
obtain ⟨rfl, firstHeld⟩ := firstCall.post
have firstFramed := firstCall.framed
```

The stepping tactics state the goal with the `args`, `results`, `pre`, `footprint` and `post` of
each defined contract unfolded, at entry and in each call's continuation, so the stack holds the
encoded output. A fact read from `call.post` keeps the contract folded until
`dsimp only [mixContract] at` it.

The tactic has these variants:

| Form | Behaviour |
| --- | --- |
| `cil_contract_steps n [facts]` | Takes at most `n` instruction steps and leaves the remaining goal. With `n = 0` no instruction is executed |
| `cil_contract_steps [facts] until continuation` | Tries `continuation` before each step, the initial goal included; stops when it closes the goal or no instruction can be stepped |
| `cil_contract_steps (snapshots := snapshots) [facts]` | Also takes numeric local stores and loads ([snapshot walks](#walk-local-stores-and-loads-with-snapshots)) |

Fixed-fuel `cil_checked_steps` can reuse a matching invocation or certificate at its actual child
budget; a proof at a larger budget does not justify a smaller one. Contract and existential-child
composition use `cil_contract_steps`, whose fuel remains existential.

Prove a contract with these lemmas:

- `MethodContract.Holds.intro final output invoked framed post` builds the conclusion of `Holds`
  by name; `invoked` may leave its fuel to `cil_checked_steps`.
- A proof that steps to its return with `cil_contract_steps` is left the footprint and `Returns`
  of the values returned, which `MethodContract.Holds.returns framed post` closes by name. The
  returned values name the output; `(output := ())` gives it for a method that returns nothing.
- `holds.result input permitted` gives a caller the final memory, output and `CallResult` of a
  proved contract outside the stepping tactics.

### Apply a contract at one call

These tactics apply a contract at the fetched call, or with `at site` at a `bind_call` site. Each
leaves the listed goals and then a continuation. For `cil_contract_call` the continuation is over
the callee's final memory, typed output and `CallResult`: introduce the three binders and read
the call's facts by field. The other tactics add the binders listed.

| Tactic | Goals before the continuation | Continuation also receives |
| --- | --- | --- |
| `cil_contract_call holds input at site [facts]` | The precondition | |
| `cil_formed_call holds input at site [facts]` (`run_call_of_contract_formed`) | The precondition and the caller memory's `WellFormed` | The call's `FrameInvariants` from the caller's memory to the callee's final memory |
| `cil_certified_call certified input [facts]` (`run_call_of_certified`) | The precondition | The callee's `InvocationCertificate` |
| `cil_contract_certified_call holds input [facts]` (`run_call_of_contract_certified`) | The precondition, the caller memory's `WellFormed` and its static world | The callee's fuel and `InvocationCertificate` |

The precondition is tagged `precondition.<callee>`, so `case precondition =>` selects it; the
other goals carry their [obligation tags](PROOFS-STEPPING.md#obligation-tags), and the
continuation keeps the call goal's tag. With `cil_formed_call`, a contract need not restate
well-formedness, static-world preservation or class catalog agreement;
`cil_formed_outcome_call` does the same for `cil_outcome_call`. `run_call_of_contract` is the
lemma that drops the certificate.

`FrameInvariants program before after` holds `after.WellFormed`,
`StaticWorldPreserved program before after` and `ClassesPreserved program before after` in its
fields `formed`, `staticWorld` and `classes`. `left.trans right` composes all three across calls,
or either preservation alone. `ClassesPreserved` says objects that agree with a catalog keep
agreeing when the program's object sites do (see [class
instances](SOUNDNESS-RUNTIME.md#class-instances)). `call_frame_invariants` and
`construct_frame_invariants` return the structure, and a formed continuation takes it whole. The
two preservation names are abbreviations, so a function proves either directly.

For a helper specified by an arbitrary `WP` postcondition, use `WP.call_framed` with its checked
call instruction and the caller's well-formed memory. Its continuation receives the helper
postcondition, `FrameInvariants` and `AllocationExtension`; select `next` and `lookup` from the
allocation evidence. These facts come from the successful invocation and need not be repeated in
the helper's contract. Confinement, access permissions and content snapshots require their own
proved effects; a cell-only footprint does not imply `Confined`.

`WP.load_call_store` composes a placed `loadCallStoreCode` segment with any proved scalar helper
contract. Both input words are loaded before the call and the output write, so the argument ranges
may overlap. The continuation receives the helper's `CallResult` and the actual checked write, and
retains the helper's full postcondition and footprint without unfolding the helper body.

### Keep certificates through a contract

A contract whose precondition implies well-formed memory and a valid static world can keep the
`InvocationCertificate` of each call:

| Name | Use |
| --- | --- |
| `MethodContract.Holds.certified` | Turns `Holds` into `MethodContract.Certified`, whose clause adds the certificate with its visited-state and returned-state invariants |
| `Certified.holds` | Recovers `Holds` |
| `Certified.weaken` | Keeps the certificate through a `Refines` |
| `InvocationCertificate.of_invoke` | Certifies any successful `invoke` from those two premises |
| `InvocationCertificate.of_run` | Certifies a run of the frame that checked arguments enter |

### Pass byref arguments with ValidCall

`ValidCall memory inputs outputs` states that memory is well formed, every input buffer is
readable and every output buffer writable. Read its facts by field: `call.wellFormed`,
`call.readable` and `call.writable`. Inputs may overlap each other and the outputs arbitrarily.
Outputs need write access but need not be initialized.

With `CIL.Safety.CallingFields`, the stepping tactics derive formed references and eight-byte
field reads from this evidence, including fields indexed by a finite bound of at most 64.
`input_snapshot` records current bytes; `output_slice` supplies write access to an in-range
slice.

`CIL.Safety.CallingTransport` carries a `ValidCall` to later memory, so a caller can pass the same
buffers again:

| After | Lemma |
| --- | --- |
| Any checked write | `ValidCall.after_write` |
| Frame entry | `after_enterFrame` |
| Memory that keeps old allocations' access (`AccessBelow`, or `MemoryBelow.accessBelow`) | `after_below` |
| A call whose footprint the inputs lie `Apart` from | `after_confined` |

`mono` drops buffers, and `input_bound` and `output_bound` give the identity bound those
relations take. `after_write` preserves call validity, but not old input contents when the write
overlaps them: read all needed input fields before an overlapping write, or prove the required
contents separately.

For a word store through a named output, `cil_contract_steps` first uses supplied checked
operation facts. If none establishes the store, it derives a successful write from the current
`ValidCall` and the output bounds. This covers `store64`, eight-byte `storeScalar` and eight-byte
`setFieldAt`. The continuation names:

| Name | Holds |
| --- | --- |
| `stored` | The new memory |
| `addressed`, `written` | The address and byte write equations |
| `readback` | The initialized bytes |
| `storedCall` | The retained call requirements |

Names take numeric suffixes when they are taken. Later argument loads use facts about the new
memory. Earlier input snapshots remain facts about their original memory; no separation or
initial output contents are inferred. `ValidCall.store_word` exposes the same write and readback
evidence for explicit composition.

Use `MethodContract` for a byref wrapper, with `ValidCall memory inputs outputs` in `pre`:

| Wrapper result | `results` encoding | Calling requirements |
| --- | --- | --- |
| Read-only scalar | `[.scalar (.i64 word)]` | Readable input views, no output views; empty footprint |
| Reporting flag | `[.scalar (.i32 (if flag then 1 else 0))]` | Readable inputs and any writable output views |
| Aggregate value | `[.scalar (.aggregate bytes)]` | Readable inputs and any writable output views |

A wrapper that allocates a private output, calls a helper and loads that output before returning
is not an exact-result [forwarder](#inherit-a-callees-contract-in-a-forwarder): write permission
alone proves neither initialized bytes nor their value. Compose its checked call, local load and
return from the preservation and readback evidence the helper's contract guarantees.

### Supply facts to the stepping tactics

Store facts may name their values in source form, such as
`write m r (numberBytes (a + b + c).toNat 8) 1 = .ok m'`. `cil_checked_steps`,
`cil_contract_steps` and `cil_raise_steps` prepare the local facts once at entry and reuse the
copies at every later step, nested checked calls included:

- Each checked step simplifies the goal with the default simp set, its interpreter definitions
  and the facts.
- Preparation adds each local fact normalised by the default simp set and the supplied non-local
  facts, so both sides have the same form. Supply any definition the computed value is stated
  through, such as a carry or borrow word, among the facts.
- The original hypotheses stay in the proof context and in the simp set. A fact that differs
  after normalisation stops the steps at its instruction, with the hypothesis shown as stated.
- A local fact that starts with `∀ index : Fin n` is instantiated at every index for a concrete
  `n` up to 64, so one four-limb field-load fact rewrites offsets 0, 8, 16 and 24. Larger or
  symbolic domains keep the quantified fact without enumeration. Later binders, such as a stack
  suffix `rest`, stay quantified.
- Preparation and stepping normalise `Fin` constructor indices and the projection of the literal
  `3`, so a fact `words 1 = 0` applies to a value read as `words ⟨1, proof⟩`.

Hand-written stepping can use the same simplification, with an optional simp configuration, as
`cil_fact_simp (config := ...) [definitions] [facts]`. `trace.CIL.factNormalize` emits one event
per supplied local proposition when it is prepared; the count measures how often normalisation
runs and does not measure elapsed time.

### Read missing-fact diagnostics

Missing-fact diagnostics distinguish `authority`, `contentSnapshot` and `helperPrecondition`.
Their suggestions identify the unresolved checked operation and its memory, local or region;
[failure records](PROOFS-STEPPING.md#observer-linter) retain the obligation tag and
source position. A missing proof is not a proved violation. Access evidence alone does not
identify initialized contents: after an overlapping write use its updated snapshot, or prove the
disjointness needed to preserve an old snapshot. A snapshot may retain unknown bytes; a
successful snapshot copy does not establish initialization.

### Refute a contract

| Lemma | Use |
| --- | --- |
| `invoke_ok_unique` | Ties a computed run to the contract's existential one |
| `invoke_ok_observation_unique` | The same for one observation of the run, such as the returned values, so the refutation never compares memories |
| `MethodContract.not_holds_of_fault` | Refutes a contract from a checked located fault on an input meeting its precondition. It uses fuel monotonicity to rule out success at every budget; the witness must be a semantic fault; fuel exhaustion is not a witness |

## Frame class instances

A contract for a method taking [class instances](SOUNDNESS-RUNTIME.md#class-instances) names
fields instead of offsets. For every field of an admitted class that its methods load or store, an
extraction emits a descriptor under `Extracted.Classes`, such as `Account.Balance :
WordField 8`, `Node.Next : ReferenceField` or `Samples.Values : ArrayField .signed32`, carrying
the class and the model offset the extractor validated. Each comes with a theorem, checked by
`decide`, that the descriptor matches the operands of an instruction it names
(`Account.Balance_accessed`). A field name is a label; only the class, offset and width or
element are relied on.

`CIL.Safety.ObjectFields` gives each descriptor its predicates and lemmas:

| Name | Meaning |
| --- | --- |
| `field.of memory object` | The value or reference the field holds, decoded from memory |
| `field.Readable memory object` | `object` is a live instance whose field loads |
| `field.Owned memory object` | `Readable` and writable, so the field also stores |
| `field.Holds memory object value` | `Owned` and holding `value` |
| `field.Forms memory object` | The reference a reference field holds forms: null or any live object |
| `LiveObject memory object` | `object` forms as an object reference older than later allocations |
| `field.entry object` | The footprint entry of a call that may change the field |

Step a field access with:

| Access | Evidence |
| --- | --- |
| Load of a scalar field | `readable.facts`, which the stepping tactics read from a `Readable`, `Owned` or `Holds` hypothesis in the context, as they read `live.formed` from a `LiveObject` (see [composing instructions](PROOFS-STEPPING.md#compose-instructions)) |
| Load of a reference field | `readable.facts held targetLive` |
| Load of a signed narrow field | `readable.signedFacts`, which pushes the value sign-extended |
| Load of a field holding a class outside the model | `readable.load_forms forms`, from `Forms`; the field is never read through |
| Store of a value | `owned.store value`, which gives the write, its `Confined` footprint and the `Holds` after it |
| Store of a live object into a reference field | `owned.store live` |
| Store of any reference that forms, null included | `owned.store_formed formed` |

Keep field facts across calls with:

| Need | Use |
| --- | --- |
| Keep a field and its value across a call confined to a footprint apart from it | `frame` |
| Keep each predicate across a confined call | `after_confined` |
| Keep each predicate across memory that keeps old allocations | `after_below` |
| Decide aliasing after a call confined to the field of `written` | `Owned.across`; `Readable.across` for a field the caller only reads |
| `Apart` for two fields of one object | `apart_of_offsets` |
| `Apart` for fields of two different objects | `apart_of_objects` |
| Keep a held caller reference under `BytesBelow` and `SlotsAgreeBelow`, the premise `MethodContract.Holds.of_allocationRenaming` needs | `ReferenceField.Holds.of_agree`, `ArrayField.Holds.of_agree` |

`Owned.across` covers word, reference and value-array fields: the same field of `object` holds
the written value when `object` and `written` are the same object, and its old value otherwise.

The loop tactics carry `LiveObject` and every field predicate across the frame's stores and
across a confined call whose footprint is apart from the field, as they carry caller buffers.
Restate a fact the call may change from the contract's postcondition.

A method that creates an instance uses these lemmas:

- `WordField.fresh_owned`, `ReferenceField.fresh_holds_null` and `ArrayField.fresh_holds_null`
  give each field of the fresh instance before its constructor runs.
- `enterFrame_heapBudget` shows the caller's heap budget reaches the `newobj` unchanged by frame
  entry.
- No frame owns an instance, so `leaveFrame_memoryAt` gives `MemoryAt` for it when the method
  returns, and the `after_kept` lemmas carry its field predicates there. `cil_checked_steps`
  returns it given that its allocation is not the frame's home.
- Fields of two unrelated classes are apart under the
  [class catalog](SOUNDNESS-RUNTIME.md#class-instances) premise, through
  `Memory.ClassesConsistent.allocation_ne`. State the premise once at entry: `decide` proves
  `ObjectSitesConsistent` for the extraction, and `invoke_preserves_classes` keeps the premise
  across any invocation, including the instances it creates.

[PoolRent](../Examples/Proofs/PoolRent.lean) uses each of these lemmas.

A list linked through a reference field, such as a free list, is described by
`ReferenceField.Segment field memory start stop nodes`: following `field` from `start` visits the
readable instances `nodes` and arrives at `stop`. A segment is a finite path, so one to null
shows no cycle is reachable from `start`, and `nodes.length` is the measure of a loop that walks
it. `Segment.next` gives the head's readable field and the one-shorter rest, `Segment.formed` the
reference the loop loads and compares, and `Segment.after_below` carries the segment into the
entered frame. The segment is a precondition the caller proves of its memory; a program can link
a cycle, and then no segment to null exists.
[PoolIdle](../Examples/Proofs/PoolIdle.lean) proves a search of the pool's free list this way.

| Example | Shows |
| --- | --- |
| [DepositBoth](../Examples/Proofs/DepositBoth.lean) | Two `callvirt` calls of `Account.Deposit` composed through `depositContract`, whose precondition is `Account.Balance.Owned` and whose postcondition is `Account.Balance.Holds final account (Account.Balance.of initial account + amount)`; the null receiver's fault at the caller's pc |
| [BumpBoth](../Examples/Proofs/BumpBoth.lean) | The static analogue, in the distinct and the aliased case; the null receiver's `NullReferenceException` as an `OutcomeContract` |
| [DepositTimes](../Examples/Proofs/DepositTimes.lean) | The same call inside a loop with `cil_loop_call`; its invariant is an `Account.Balance.Holds` fact the loop tactics carry across the counter's store |
| [LinkedNodes](../Examples/Proofs/LinkedNodes.lean) | `Link` and `SecondValue` composed through `Node.Next` and `Node.Value`: keeps the linked node's `Value` across the one slot `Link` writes, proves both null faults of `SecondValue` at their pcs, and transfers `Link`'s contract to any program that renames its fresh allocations |

The predicates are built on `CIL.Safety.ObjectFraming`, which states the same facts about the
references `objectFieldAddress` locates. Use it directly for a field no extraction names:

| Need | Use |
| --- | --- |
| Keep a formed reference and a located field across a confined call, given well-formed memory before the call | `formObject_of_confined`, `objectFieldAddress_of_confined` |
| `Apart` for fields of two different objects | `objectField_apart_of_ne` |
| Keep a field of one object across a call confined to a field of another, given that the read field's allocation is older than the call | `Confined.objectField_read_of_ne` |
| The aliased case: equal references locate the same field, so the case follows by substitution | `objectFieldAddress_same` |
| The formation fact the stepping tactics need for an argument whose field is located | `formObject_of_objectFieldAddress` |

A class-typed field keeps its reference in the field's slot instead of in bytes. One footprint
entry starting at the field covers both, so a contract's footprint names the fields whose bytes
or references it may change.

| Need | Use |
| --- | --- |
| Confine a store to that entry | `Confined.setSlot`, `Confined.storeSlot` |
| Keep the reference a field of a different, older object holds | `Confined.objectSlot_of_ne` |
| Step the field accesses | `step_objectReferenceField_eq`, `step_setObjectReferenceField_eq` |
| Reduce them, given the slot's access check, to the held reference and to `setSlot` | `loadSlot_of_access`, `storeSlot_of_access` |
| Read `setSlot` back | `setSlot_slots_same`, `setSlot_slots_of_ne` |
| `setSlot` leaves bytes, authority and field locations unchanged | `read_setSlot`, `access_setSlot`, `objectFieldAddress_setSlot` |

An instance call compiled as `callvirt` steps like a call once its receiver forms as a live
object (`step_callInstance_eq`, `receiverCall_address`), so `cil_contract_steps` composes it
through the callee's contract. A null receiver steps to `NullReferenceException` at the
`callvirt` itself (`receiverCall_null`).

A virtual call steps the same way once the receiver's runtime type is known. Pass a fact
`runtimeTypeOf memory receiver = .ok type`, with the definitions of `type` and its assembly
scope; stepping looks the class up in the call's table (`step_callVirtual_eq`,
`virtualCall_address`) and enters the listed body
([AnimalLegs](../Examples/Proofs/AnimalLegs.lean)). For an instance the method constructs, the
fact is `objectMemory_runtimeTypeOf` ([FreshDogLegs](../Examples/Proofs/FreshDogLegs.lean)).
A class the table omits steps to the model fault `outsideDispatchTable` (`virtualCall_outside`).

`castclass` and `isinst` step on the same fact (`step_objectTest_eq`): with
`RuntimeType.lineage` and the definitions of the type, its bases and their scope, stepping
decides whether the tested class is in the lineage, so the reference passes, becomes null or
throws `InvalidCastException` ([DogTest](../Examples/Proofs/DogTest.lean),
[DogCast](../Examples/Proofs/DogCast.lean)).

An `ldstr` steps to the object the caller bound to its text: given `bound`, that
`memory.literals.lookup text = some literal`, and the literal's formation fact, pass
`literalObject_of_lookup bound` and that fact to `cil_checked_steps`. With the text unbound,
`literalObject` reduces to the `unsupported` fault. No call rebinds a literal
(`invoke_literals`), so the same `bound` steps an `ldstr` after a call; the literal's formation
fact crosses the call like any other object's
([StringLiterals](../Examples/Proofs/StringLiterals.lean),
[StringDefault](../Examples/Proofs/StringDefault.lean)).

A framework argument guard steps to its named exception or past itself. `ThrowIfNull` steps on
the argument's null test directly. An integer guard reduces through `zeroGuardOutcome` or
`comparisonGuardOutcome`; pass those with `CIL.guardOperand`, `CIL.ZeroGuard.throws` or
`CIL.ComparisonGuard.throws` and the case hypothesis that decides the test, and bind the
parameter-name literal as for `ldstr`
([GuardCount](../Examples/Proofs/GuardCount.lean),
[GuardIndex](../Examples/Proofs/GuardIndex.lean)).

A method that constructs an instance steps its `newobj` with `allocateObject_ok`, given
well-formed memory and a `Memory.heapBudget` covering the instance, or with
`allocateObject_insufficient` for the `allocationFailure` fault when the budget does not cover
it. `objectMemory_formObject`, `objectMemory_field` and `objectMemory_access` give the fresh
instance's formation, field addresses and access, and `allocateObject_effect` its `MemoryBelow`
frame for the caller. `objectMemory_field` takes the field's declaring class as a member of the
instance's `RuntimeType.lineage`, so it covers fields of a base class too.

[FreshObject](../Examples/Proofs/FreshObject.lean) proves both outcomes, stepping the
constructor's call in place, and [DerivedObject](../Examples/Proofs/DerivedObject.lean) steps a
derived class's constructor through its base's.

An [array of class references](SOUNDNESS-RUNTIME.md#arrays-of-class-references) names an
element by its array and index. `CIL.Safety.ReferenceArrayElements` mirrors the field
predicates in the `ReferenceArray` namespace:

| Name | Meaning |
| --- | --- |
| `ReferenceArray.Live memory array element length` | `array` is a live `element[]` of `length` |
| `ReferenceArray.of memory array index` | The reference element `index` holds |
| `ReferenceArray.Readable memory array element length index` | `Live`, `index` inside, readable |
| `ReferenceArray.Owned memory array element length index` | `Readable` and writable |
| `ReferenceArray.Holds memory array element length index value` | `Owned` and holding `value` |
| `ReferenceArray.Reads memory array element length index value` | `Readable` and holding `value` |
| `ReferenceArray.entry array index` | The footprint entry of a call that may change the element |
| `ReferenceArray.Forms memory array index` | The reference element `index` holds forms: null or any live object |

| Need | Use |
| --- | --- |
| Step `ldelem.ref` | `readable.facts held targetLive`, `readable.facts_null held` |
| Step `ldelem.ref` whatever the element holds, never reading through it | `readable.facts_forms forms` |
| Step `stelem.ref`, with its `Confined` footprint and the `Holds` after it | `owned.store targetLive storable`, `owned.store_null`; `owned.store_formed formed storable` for any reference that forms, such as a string |
| Decide the covariance check for an instance whose class derives from the element class | `storableIn_of_lineage` |
| The `ArrayTypeMismatchException` of one whose class does not | `storableIn_mismatch` |
| The `IndexOutOfRangeException` of an index past the length | `live.slot_outside` |
| Keep and decide elements across a confined call, as for fields | `frame`, `Holds.after_confined`, `Owned.across` |
| Keep an element across a store into another index of its array | `Holds.across_ne`, `Reads.across_ne` |
| Separate an array from every object with a located field, so `apart_single` frames elements and fields across each other's stores | `Live.field_ne` |
| Step a load of what an earlier store wrote | `reads.facts formed` |
| Carry a covariance check across later stores | `storableIn_after_confined`, `storableIn_of_allocations` |
| Carry a formation across later stores | `formObject_of_allocations` with `allocations_of_setSlot` |
| Carry a covariance check across an allocation from well-formed memory | `storableIn_of_confined` |
| Let `Confined.forget_fresh` drop the elements of an array the method allocated | `entries_young` |
| A fresh array from `newReferenceArray_ok`, live with every element owned and null | `ReferenceArray.fresh` |
| Step the three instructions | `step_referenceArrayLength_eq`, `step_referenceArrayLoad_eq`, `step_referenceArrayStore_eq` |

| Example | Shows |
| --- | --- |
| [NodePair](../Examples/Proofs/NodePair.lean) | Fills a fresh array and reads it back, with its `allocationFailure` without budget |
| [ArrayElement](../Examples/Proofs/ArrayElement.lean), [ArrayLength](../Examples/Proofs/ArrayLength.lean) | Read an element and the length, with the bounds and null faults |
| [ArrayCovariance](../Examples/Proofs/ArrayCovariance.lean) | Stores into a `Circle[]` passed as a `Shape[]`, proving the `ArrayTypeMismatchException` of a `Square` |
| [BucketItems](../Examples/Proofs/BucketItems.lean) | Reads an element through a field holding such an array, with its null and bounds faults. The field is a `ReferenceField` whose held reference is the array |
| [BucketRefill](../Examples/Proofs/BucketRefill.lean) | Replaces the array such a field holds |
| [TagStore](../Examples/Proofs/TagStore.lean) | Stores a string a field holds into an array of `string`, which holds opaque references, deciding covariance by the string's own class |
| [TagLoad](../Examples/Proofs/TagLoad.lean) | Loads a string from such an array into a field, as `ReferenceField.Forms` and `Owned.store_formed` take it |

A field holding a single-dimensional array of a value type (an integer, Boolean, char, enum,
struct or integer vector) is an `ArrayField element` whose slot keeps the whole array's origin;
`field.elementType` names its element in a statement. `WholeArray memory element array length`
says `array` starts a live heap array of exactly `length` elements, allocated before any later
one, whose view validates.

| Need | Use |
| --- | --- |
| Load the array a readable field holds | `readable.facts held whole`, or `load_whole` |
| Load the null array from a field holding null | `load_null` |
| Store into an owned field, confined to its slot | `owned.store_whole whole`, `owned.store_null` |
| The rest of the field lemmas above | `frame`, `after_confined`, `after_below`, `after_kept`, `across`, `Holds.of_agree`, `fresh_holds_null` |
| Keep an array whole across the same changes, whatever its elements then hold | `WholeArray.after_confined`, `after_below`, `after_kept` |
| Pass a whole array as a call argument, from its view's `valid` | `checkedValue_array` |
| Move it through a local, from its view's `valid` | `storeLocal_array`, `loadLocal_array` |
| Step `ldfld` and `stfld` | `step_arrayField_eq`, `step_setArrayField_eq` |
| Step `ldlen` of the loaded array to its length, once its view validates (`whole.valid`) | `step_memory_arrayLength_address_eq` |
| Step `ldlen` of the null array to its throw | `step_memory_arrayLength_null_eq` |

| Example | Shows |
| --- | --- |
| [SampleValues](../Examples/Proofs/SampleValues.lean) | Returns the array a field holds, and the null array for a null field |
| [SampleCount](../Examples/Proofs/SampleCount.lean) | Returns its length |
| [SampleRefill](../Examples/Proofs/SampleRefill.lean) | Replaces it under a contract whose footprint is the field's slot |
| [TilePairs](../Examples/Proofs/TilePairs.lean), [TilePairCount](../Examples/Proofs/TilePairCount.lean) | The same for an array of 16-byte structs |
| [TileRelane](../Examples/Proofs/TileRelane.lean) | Stores an array of vectors |
| [SampleCountAfterRefill](../Examples/Proofs/SampleCountAfterRefill.lean) | Counts the array a field holds after a call that may replace it, deciding the aliasing with `Readable.across` |
| [TileHold](../Examples/Proofs/TileHold.lean) | Constructs a `Tiles` and stores an array into each of its fields, starting from `fresh_holds_null` |

## Construct structs through contracts

A `newobj` of a reference-free struct allocates caller-owned storage, writes zero to every byte,
then runs the constructor with that storage as `this`. The constructor's interface is an ordinary
`MethodContract` whose first argument is `this`; `MethodContract.Constructs c size this value` adds
that it returns no values and that `post` reads back all `size` bytes at `this` as `value`:

```lean
import CIL

open CIL.Safety
open CIL (W64)

/-- A 16-byte struct of two words, constructed at `this`. -/
structure PairInput where
  this : Reference
  low : W64
  high : W64

def pairBytes (input : PairInput) : List (BitVec 8) :=
  numberBytes input.low.toNat 8 ++ numberBytes input.high.toNat 8

def pairContract : MethodContract PairInput Unit where
  args input := [.reference (.address input.this), .scalar (.i64 input.low),
    .scalar (.i64 input.high)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 16 1 true = .ok ()
  footprint input := [(input.this, 16)]
  post input _ final _ := read final input.this 16 1 = .ok (pairBytes input)

theorem pair_constructs :
    pairContract.Constructs 16 PairInput.this fun input _ => pairBytes input :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩
```

The storage does not exist before the step, so a caller names the contract input as a function of
it. `cil_contract_construct holds constructs input [facts]` applies `run_newAggregate_of_contract`
at the fetched `newobj` and leaves:

- the caller memory's `WellFormed`;
- the precondition over the fresh storage;
- a continuation that resumes at `pc + 1` with the read-back value on the stack.

Both obligations receive `ConstructStorage memory updated this size`: the storage reads back as
`size` zero bytes, is writable at full width, is allocated at `memory.nextIdentity`, and the step
kept all older memory. The continuation also gets the constructor's invocation, the final
memory's `WellFormed`, static-world preservation, catalog agreement, `Confined` and `post`. No
invocation, step or `loadLocal` equation is stated. `ConstructStorage.confined` moves `Confined`
back to the memory before `newobj`; `Confined.forget_fresh` then drops the storage, which the
caller's frame owns and expires on return.

Because `newobj` zeroes the storage, a field the constructor leaves unassigned reads back as
zero instead of as an uninitialized read, so the readback is still full width. A contract may
take that zero readback as a precondition. `run_construct_of_contract` and
`run_construct_of_contract_formed` take the construct step equation instead, like
`run_call_of_contract`; they cover aggregate storage only. `read_append` joins adjacent field
reads into the full readback, and `Confined.write_within` confines a field write to the whole
struct.

## Name exceptional outcomes

An `OutcomeContract` (`CIL.Safety.OutcomeContract`) adds `raises : Input → Memory → Option String`
to a `MethodContract`: where it is `some exception` the method must end in exactly `.thrown
exception` (`Raises`), and elsewhere the normal clause applies. Fuel exhaustion, unsupported
instructions and memory faults never satisfy `Raises`, so a contract cannot be met by getting stuck.
Memory after a throw is not observable to the caller, so `Raises` states none; runtime exceptions
count only where the semantics models them as `.thrown`.

```lean
import CIL

open CIL.Safety

def percentContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"
```

| Name | Use |
| --- | --- |
| `cil_raise_steps [facts]` | Steps a `Raises` goal to its `.throw` |
| `cil_outcome_call holds input at site [facts]` | Continues after a call the callee's contract says returns, whether the caller then returns or raises |
| `cil_outcome_raise holds input at site [facts]` | Closes a `Raises` goal by propagating the exception the callee's contract names |
| `MethodContract.Holds.outcomes` | Lifts a normal-only contract |
| `invoke_unique` | Ties a computed fault to the contract's existential one |

[CountUntil](../Examples/Proofs/CountUntil.lean) proves `bumpContract`, which raises
`System.InvalidOperationException` when its two arguments are equal, with `cil_raise_steps` and
`cil_checked_steps`, then proves its loop returns or propagates that exception through the contract
alone.

Import `CIL.Safety.RuntimeExceptions` to name modeled arithmetic failures with `RaisesCLR` and
`OutcomeContract.HoldsCLR`. This contract mode uses the contract's arguments, preconditions,
normal-return clause, footprint and `raises` field unchanged. Its fixed
`ExecutionFault.clrException` mapping is:

| Fault | Named CLR exception |
| --- | --- |
| `.thrown exception` | `exception` |
| `.arithmetic .overflow` | `System.OverflowException` |
| `.arithmetic .divideByZero` | `System.DivideByZeroException` |
| Every other fault | None |

Checked add, subtract, multiply and integer conversions report overflow through this mapping.
Integer division and remainder by zero report divide-by-zero. The admitted runtime model reports
overflow for signed minimum divided by negative one, including its remainder instruction. Invalid
arithmetic operands, invalid bounds, memory faults, unsupported instructions, invalid state and fuel
exhaustion have no name in this mode. The mode does not change `Raises` or `.thrown`.
`OutcomeContract.Holds.clr` lifts a thrown-outcome proof (`Holds`) to `HoldsCLR`.

For a wide-integer `Divide` or `Mod` contract, select `some "System.DivideByZeroException"` in
`raises` when its divisor is zero and prove `HoldsCLR`. Both an explicit throw and the mapped
arithmetic failure can establish this exact outcome. The proof must reach that fault through the
actual extracted program. `run_fault_raisesCLR`, `run_next_raisesCLR` and `raisesCLR_of_run`
compose that execution; `run_call_raisesCLR_of_contract` propagates a callee contract's named
outcome. `RaisesCLR.not_of_invoke` refutes a wrong name from a settled checked invocation.

## Derive public contracts

When a method's proved contract is more detailed than its callers need, export a smaller
interface by proving that the internal contract refines it, without unfolding or executing the
method again:

```lean
import CIL

open CIL.Safety
open CIL (W64)

/-- The proved contract: the result is the argument plus one. -/
def increment : MethodContract W64 W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v + 1

/-- The published contract: the result differs from the argument. -/
def changes : MethodContract W64 W64 := { increment with post := fun v _ _ out => out ≠ v }

theorem increment_refines : increment.Refines changes where
  args _ := rfl
  results _ := rfl
  pre _ _ permitted := permitted
  footprint _ _ _ _ member := nomatch member
  post v _ _ out _ _ incremented := by
    show out ≠ v
    rw [incremented]
    bv_omega

/-- Any method proved against `increment` satisfies `changes`, without running it again. -/
theorem changes_holds {program : CIL.Program} {method : Nat}
    (proved : increment.Holds program method) : changes.Holds program method :=
  proved.weaken increment_refines
#print axioms changes_holds
```

`MethodContract.Refines internal exported` requires:

- the same `args` and `results` encodings;
- the exported precondition to imply the internal one;
- every internal footprint entry to lie `Within` an exported entry under the exported
  precondition (so `Confined.widen_within` applies);
- the internal postcondition to imply the exported one under the exported precondition and the
  internal footprint's `Confined`. That premise lets the exported post state a frame fact, such
  as a read apart from the footprint surviving through `Confined.read_apart`.

`MethodContract.Holds.weaken` turns a proved `Holds` and a `Refines` into the exported `Holds`.

`OutcomeContract.Refines` adds that both contracts select the same outcome (`raises`) under the
exported precondition; the footprint and postcondition premises apply only where that outcome is
normal return. `OutcomeContract.Holds.weaken` derives the exported outcome contract, and
`OutcomeContract.Refines.of_method` builds a refinement from a normal one and the agreeing outcomes.
A stronger precondition can exclude every exception, after which `OutcomeContract.Holds.normal`
yields a normal-only contract. Both `Refines` are reflexive and transitive.

## Inherit a callee's contract in a forwarder

Overload forwarders and instance-to-static wrappers compile to `ldarg*; call k; ret`.
`MethodContract.Holds.forward` (`CIL.Safety.Forwarders`) gives such a method its callee's contract
with the forwarder's own argument encoding, `contract.withArgs forwarded`, without stepping either
body. Given `add_holds : addContract.Holds Extracted.program addTo`:

```lean extracted
theorem sum_forwards : sumContract.Holds Extracted.program sum :=
  add_holds.forward (loads := plainLoads [0, 1, 2]) (narrow := none) sum.found addTo.found
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ _ => plainLoads_unchanged _ _)
    (fun _ _ _ _ member => .inl member)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => trivial)
```

`Forwards body calleeBody loads callee narrow` fixes the body to `forwarderCode loads callee narrow`
with no locals, vector argument homes or parameter homes, so frame entry and exit leave memory
unchanged and the callee's precondition, footprint and postcondition carry over verbatim. The loads
are data: each is an argument index and the narrowing the extractor attaches to `bool`, `byte`,
`sbyte`, `short` and `ushort` parameters (`plainLoads` for wider ones). The lemma has these premises:

- The callee's arguments are the forwarder's at those indices, each kept by its load's narrowing
  (`LoadsUnchanged`).
- Every forwarder argument reaches the callee or is valid under the precondition, since the
  forwarder's own invocation checks them all.
- The call exposes no unspecified vector bits.
- A narrowed `ret (some kind)` does not change the callee's result (`ReturnsUnchanged`), which
  holds for a boolean.

Aggregate results retain their complete byte list. Use `Holds.weaken` afterwards to export a
different contract.

`MethodContract.Holds.forward_out` covers `ldarg*; ldloca 0; call k; ret`, which passes the address
of a fresh numeric local as a last out argument and drops it. References, spans, arrays, method
pointers and handler tables have no byte home; `ForwardsOut` excludes them with its `notSpan`,
`notArray`, `notPointer` and `notTable` premises. `make_fitting_local` and `make_unknown_local`
require the same exclusions. The local may hold any initializer that fits its kind; the extractor
emits `.unmodeled` without `InitLocals` and the kind's zero with it.

The callee runs in the memory after frame entry and the result is read after the local expires, so
the forwarder's contract `outer` is related to the callee's `inner` through `extend input home` and
premises over those memories:

- The callee's arguments are the forwarder's selected by the loads followed by the home, each kept
  by its load's narrowing and none with unspecified vector bits.
- `outer.pre` gives a well-formed memory in which every forwarder argument is valid (`checked`),
  since the forwarder checks them all.
- `inner.pre` follows from `outer.pre` with the home fresh, writable and holding its initializer
  (`LocalHolds`).
- The `inner` footprint names fresh storage or lies inside `outer.footprint`. The lemma checks
  the footprint (`Confined.across_frame`).
- The two contracts encode results alike, as scalars that survive the local's expiry and that a
  narrowed `ret` keeps.
- `outer.post` follows from `inner.post` once the frame has expired.

The home's alignment is not surfaced, so a callee whose precondition requires it cannot be
composed.

## Compose through imported contracts

A callee from another assembly has no body in the caller's extraction. Give it an import slot
(`CIL.Safety.Imports`): slot `j` is method index `importIndex base j = base.length + j`, past every
extracted method, so running the caller's program alone faults `invalidState` at the call
(`run_call_unlinked`, `importIndex_unlinked`). Do not put a stub body there: a stub's contract is
false, so a theorem assuming it proves nothing.

Prove the caller over every program that links its own, assuming only the import's contract:

```lean extracted
def importsAdd (linked : CIL.Program) : Prop :=
  addContract.Holds linked (importIndex Extracted.program 0)

theorem root_given :
    HoldsGiven Extracted.program importsAdd (fun linked => rootContract.Holds linked root)
```

`Links base linked` means `linked = base ++ rest`, so every extracted method keeps its index
(`Links.refl`, `Links.trans`, `Links.found`). `HoldsGiven base imports claim` is `∀ linked, Links
base linked → imports linked → claim linked`. Start the proof with `rintro linked ⟨rest, rfl⟩
addHolds`; the step and call tactics find methods in `Extracted.program ++ rest` unchanged. A helper
proved on the extracted program alone transfers with `MethodContract.Holds.extend` or
`OutcomeContract.Holds.extend`: `run_extend` shows a run that never faults `invalidState` gives the
same result in any linked program, and a raised exception is not `invalidState`.
`HoldsGiven.discharge` instantiates the claim for a concrete linked program whose import meets its
contract, and `HoldsGiven.closed` states a claim that needs no import.

In an extraction, `bind_import addTo := "System.Void Lib.Adder::AddTo(...)"` resolves the signature
through `Extracted.importSignatures` and defines `addTo` as `Extracted.program.length + j`, with
`addTo.slot`, `addTo.signature` and `addTo.unlinked` (`Extracted.program[addTo]? = none`) checked by
`rfl`; `bind_call` then names its call site. The certificate accepts a call there only when
`Extracted.imports` has a slot with the site's identity and arity (see [SOUNDNESS](SOUNDNESS.md));
an extraction made without `--import` has no slots, so its `Extracted.imports` and
`Extracted.importSignatures` are empty. The [interface guide](CONTRACT-INTERFACES.md) describes
extracting against an imported interface.

The identity checks that bind a slot to a certified library implementation are not part of this
rule; the next section describes relocating a library into the slot.

## Link separately extracted libraries

A library extracted on its own calls its helpers by its own method indices. `CIL.Safety.Linking`
relocates it into a linked program:

- `Instruction.relocate f` renames only the method index of `.call`, `.newVector256` and
  `.newAggregate` (`Instruction.callees`); pcs, locals, profiles and static sites are unchanged.
- `Closed lib` says every callee index in `lib` is one of its methods (`Closed.of_check` decides
  it).
- `RelocatesInto lib linked f` says method `i` sits at `f i` relocated by `f`.
- `run_relocate` and `invoke_relocate` then give exactly the same result: the same memory and
  values on return, and on a fault the same pc and fault with only its method index renamed to
  `f method`.
- A raise is still the same `.thrown`, so `MethodContract.Holds.relocate` and
  `OutcomeContract.Holds.relocate` move a contract proved on the library alone to its relocated
  index.

A `Library` is its exported entry and its private helpers. `link app libs` puts library `j`'s entry
at import slot `importIndex app j` and all helpers after the entries, library by library
(`linkSlot`). `link_links` and `link_relocates` hold by construction, so `composed` discharges a
caller's `HoldsGiven` for the concrete linked program from contracts proved on each library alone:

```lean extracted
theorem root_composed : rootContract.Holds (link Extracted.program [addLib]) root :=
  composed (specs := [addContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    closed proved
```

Here `closed` and `proved` are each library's `Closed` and `Holds` facts. `Imports app specs` names
one `Relocatable` property per slot, so libraries may export contracts of different types. Each
library exports only its index-0 method. Static identities are not renamed: two linked libraries
that use the same identity for different bytes fault `invalidState` at the second static access, so
a collision can make a proof fail and cannot prove a false statement.

## Reuse framework contracts

When extending generic safety proofs, reuse the facts established by the shared dispatch or
traversal proof. Names in this table are in `CIL.Safety`, except the base relabeling helpers in
`CIL.Embedding`.

| API | Reusable information | Source |
| --- | --- | --- |
| `RunTrace` | Successful execution through next, return, call and construction cases | [ExecutionTrace](../CIL/Safety/ExecutionTrace.lean) |
| `FrameSetup` | Fresh ownership, frame allocations, preservation below the allocation boundary, static bindings and conditional validity | [FrameSetupLemmas](../CIL/Safety/FrameSetupLemmas.lean) |
| `InstructionContract` | Memory effects and conditional output-value validity from one instruction analysis | [InstructionMemoryLemmas](../CIL/Safety/InstructionMemoryLemmas.lean) |
| `StaticInstructionContract` | Corresponding contract for static-memory instructions | [StaticMemoryLemmas](../CIL/Safety/StaticMemoryLemmas.lean) |
| `StepContract` | Memory/frame effects and conditional live-value validity for a checked action | [ExecutionInvariants](../CIL/Safety/ExecutionInvariants.lean) |
| `Fallthrough`, `Branching` | Shared relabeling proofs for base instruction families | [BaseStep](../CIL/Embedding/BaseStep.lean) |

These contracts retain their hypotheses: `InstructionContract.values` requires well-formed input
memory and valid input values, while its memory-effect field does not. `RunTrace` describes
successful execution; fault-preservation proofs need the appropriate equivalence lemmas.
