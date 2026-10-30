# Method contracts and exceptional outcomes

## Compose calls through contracts

A caller proof that steps into its callee breaks whenever the callee is reimplemented. State the
callee's interface as a `MethodContract` instead (`CIL.Safety.MethodContract`) and prove the caller
against it:

```lean
def addContract : MethodContract AddInput where
  args input := [.reference (.address input.a), .reference (.address input.b), .reference (.address input.res)]
  pre input m := read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()
  footprint input := [(input.res, 8)]
  post input _ final values := values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)

theorem root_holds (add : addContract.Holds Extracted.program addTo) : rootContract.Holds Extracted.program root
```

`pre` holds formation, authority and the permitted aliasing; the example lets `res` overlap either
input. `Holds` is `Ensures` with the footprint added to the postcondition (`Holds.ensures`), and
fuel stays existential so callers never depend on a callee's step count. `Confined footprint before
after` is the memory guarantee: earlier allocations and write authority are unchanged, and bytes and
read authority change only inside the footprint (a write grants read access to what it wrote).
`Confined.trans`, `Confined.widen`, `Confined.write`, `Confined.read_eq` and `Confined.access_write`
compose and consume it. A callee with locals writes its own frame too: list those slots in the
footprint while executing, then drop them with `Confined.forget_fresh` and cover frame entry with
`Confined.then_below`. `framed.after_leaveFrame owned` covers teardown, given that every identity
the frame owns is at least the caller's `nextIdentity`. A method with locals that changes no
caller memory ends with `MemoryBelow memory.nextIdentity memory final`, not `final = memory`;
`MemoryBelow.compose_invoke` composes consecutive such calls
([span contents](PROOFS-BUFFERS.md#describe-span-contents)). A store through an argument reference
needs only write access: `store_word64 word writable` gives the `write`, the `storeValue` step
fact and the readback of its encoding, so `Confined.write` and the stepping tactics consume the
same equation. `Outside.nil` and `Outside.cons` are simp rules, so `simpa
using ⟨hr, hq⟩` closes a word footprint from per-word `OutsideWord` facts; `Outside.word` builds it
as a term. `Within inner outer` states that an interval lies inside another of the same allocation:
`Confined.widen_within` widens a footprint to one whose entries enclose it, and
`Confined.write_within` confines a write that lies inside one entry, so four limb writes satisfy a
contract that declares one 32-byte output. Entries may overlap. `Apart r width entry` states that
two intervals share no byte, in different allocations or at disjoint offsets of one.
`Confined.read_apart` keeps a checked read of older memory apart from every entry, taking the
allocation's age from `WellFormed`; `Confined.cells_apart` keeps every byte of an allocation no
entry names, and `WordSnapshots.after_confined` (`CIL.Safety.ConfinedSnapshots`) keeps remembered
words. `LocalSnapshots` (`CIL.Safety.LocalSnapshots`) remembers locals of every numeric kind, such
as vectors and int32s; `LocalSnapshots.after_confined` keeps them across such a call, and
`after_write_apart`, `after_below` and `store` across writes, frame changes and local stores.
`snapshots.load value specified` is a step fact for `.local`, so stepping tactics take it.

Import `CIL.Safety.LocalSnapshotSteps` to step through numeric local stores and reloads with
`cil_checked_steps (snapshots := snapshots) [facts]`. Use it on a checked `run` equality or an
existential result such as `∃ after, run ... = .ok (after, result)`. The local context must justify
`WritableHomes`, memory well-formedness, each home lookup and write access. The tactic introduces
each store's new memory, updated snapshots and preserved access facts, so later stores need no
manually split execution segments. Loads use the latest remembered value; overwrites replace it. It
stops at an unsupported step or an unproved obligation, and fails if it takes no step. It does not
infer authority, initialization, or preservation across calls and unrelated writes. Ordinary
`cil_checked_steps [facts]` is unchanged.
[Tests/LocalSnapshotSteps](../Tests/LocalSnapshotSteps.lean) contains complete vector/int32
store-and-reload examples and rejection tests.

A snapshot overlapping the footprint needs a postcondition instead. The contract fixes no profile:
the program does. `MethodContract.Holds.reprofile` (`CIL.Safety.ProfileContract`, with
`OutcomeContract` and `HoldsCLR` forms, and `_statics` forms of the first two for a contract indexed
by `programStaticDescriptors`) carries a contract proved for a program whose methods all use profile
`p` to `CIL.reprofile program q` for any `q` that agrees with `p` on the program.
`CIL.Program.ProfileAgreement.of_flags` reduces agreement to the flags in `program.profileReads`,
which `decide` checks for concrete profiles, so one proof covers every profile in a family. A
separate per-profile extraction is covered once it is shown equal to the reprofiled program, by
`rfl` when only the profiles differ.

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

The surrounding manifest still provides `schema`, `assembly`, `proofRoot` and `interface`. Each
artifact's `verification.json` selects the shared proof source under `proofRoot`. The family theorem
has shape `∀ q : FeatureProfile, Predicate q → contract.Holds (reprofile Reference.program q) 0`,
where the concrete predicate is decidable. Both method and outcome contracts are supported. The
selected artifacts must include `referenceProfile`. Its extraction is checked against the same DLL,
copied into a reserved generated module, and compiled separately from author macros. Its compiled
artifacts are frozen before author code runs and checked again afterward. Every profile must prove
by `rfl` that the named reference program equals this fixed program; a definition that changes with
the current extraction cannot substitute a different body. The reference program must use
`referenceProfile` uniformly. Each profile receives its own ordinary extraction check, layout check,
theorem audit and kernel replay; generated proofs instantiate the predicate with `by decide +kernel`
and establish the exact program equality with `rfl`. Because the family theorem already concludes a
reprofiled program, no second transport or handwritten per-profile proof file is needed.

This manifest form covers same-flag transport: a separate checked `ProfileAgreement.of_flags`
obligation rejects any selected profile that disagrees on a reference program read flag, including
intrinsic prerequisites, and reports the flag's name. It deliberately does not accept general
families whose observed branches differ. Use profile templates for those proofs. Even an otherwise
valid family is rejected when extraction pruning, method numbering, instructions or metadata make
its program differ from the reprofiled reference. The exact equality and agreement statements are
independently audited, so proof-source macros cannot replace these checks. Nothing is published
unless all selected profiles pass. Published source bundles retain every selected extraction; full
verification freshly extracts both the selected profile and its fixed reference from the pinned
implementation DLL, then repeats the family checks before composing the caller theorem. Identical
fixed-reference modules can reuse authenticated, source-bound compilation across profile workspaces.
Their compiled artifacts are still fixed before producer proof code runs and checked afterward;
every selected profile retains its extraction replay and exact audit.

Profiles must be distinct built-in names and match their artifacts. A family entry cannot also
specify `artifact`; ordinary single-profile entries are unchanged. Family transport currently
requires a closed extraction without imported-contract slots. Explicit type-initialization premises
remain bound to each exported profile; static-value assumptions remain unsupported. Full
source-bundle verification rejects initialization premises, as for single-profile exports.

For a program with no profile reads, use the same `ProfileAgreement.of_flags` rule: an equality
`empty : program.profileReads = []` discharges its premise with `by simp [empty]`. This replaces
`profileIndependentCheck` and `profile_independent_agreement`; no separate profile-independent
checker is needed.

A contract may also type its result: `MethodContract Input Output` adds `results : Output → List
Value`, and `post` speaks of the `Output`. `Returns` requires the returned values to equal `results
out` for some `out` satisfying `post`. Without `Output`, `results` is the identity and `post` sees
the values:

```lean
def mixContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post input _ _ v := v = input.1 * 3 + input.2
```

In the caller, `cil_contract_steps [facts]` steps an existential-fuel goal through ordinary
instructions and calls with supplied evidence. Mark a proved `MethodContract.Holds` theorem
`@[cil_contract]`, or include its proof in `facts`, to apply it at a matching callee. The theorem's
program and method binding must match the actual call; required binding premises are checked. Input
fields are inferred from the encoded arguments. The precondition is proved from facts when possible,
otherwise it remains a goal before the continuation. The continuation receives the result, footprint
and postcondition. Contracts merely present in the local context are not automatically selected.

A supplied successful child invocation, with fixed or existential fuel, or an
`InvocationCertificate`, also composes without unfolding the helper body. Fixed-fuel
`cil_checked_steps` can reuse a matching invocation or certificate at its actual child budget; a
proof at a larger budget does not justify a smaller one. Contract and existential-child composition
use `cil_contract_steps`, whose fuel remains existential.

Without matching evidence, the contract stepper stops at the call. `cil_contract_call holds input at
site [facts]` explicitly applies the contract at a `bind_call` site (or the fetched call without
`at`), leaving the precondition and then a continuation over the callee's final memory, values,
invocation, frame and `Returns`. Destructure `Returns` as `⟨out, rfl, post⟩` and unfold the contract
(`dsimp only [mixContract]`) so the stack holds the encoded output. Use `cil_contract_steps n
[facts]` to take at most `n` instruction steps and leave the remaining goal for a continuation. With
`n = 0`, no instruction is executed. `cil_contract_steps [facts] until continuation` tries the
continuation before each step, including at the initial goal. It stops when the continuation closes
the goal or no instruction can be stepped. `cil_formed_call` (`run_call_of_contract_formed`) also
takes the caller memory's `WellFormed` and hands the continuation the callee's `final.WellFormed`
and static-world preservation, so contracts need not restate either; `cil_formed_outcome_call` does
the same for `cil_outcome_call`.

`StaticWorldPreserved program before after` names static-world preservation. Use `left.trans right`
to compose it across calls. `FrameInvariants program before after` bundles `after.WellFormed` with
that preservation. Its `formed` and `staticWorld` projections give each fact, and `left.trans right`
composes both invariants. `call_frame_invariants` and `construct_frame_invariants` return this
bundle. Both names are abbreviations, so existing conjunction proofs and formed-call continuations
keep their proof structure and argument order.

Store facts may name their values in source form, such as `write m r (numberBytes (a + b + c).toNat
8) 1 = .ok m'`. Each checked step simplifies the goal with the default simp set, its interpreter
definitions and the facts. Fact preparation also adds each local fact normalised by the default simp
set and the supplied non-local facts, so both sides meet in the same form. Supply any definition the
computed value is stated through, such as a carry or borrow word, among the facts. The original
hypotheses stay in the proof context and in the simp set; a fact that still differs stops the steps
at its instruction, with the hypothesis shown as stated. Hand-written stepping can use the same
simplification, with an optional simp configuration, as `cil_fact_simp (config := ...) [definitions]
[facts]`. `cil_checked_steps`, `cil_contract_steps`, and `cil_raise_steps` prepare local facts once
at entry. All later steps reuse these copies, including nested checked calls. The original
hypotheses stay in the local context.

When a local fact starts with `∀ index : Fin n`, preparation instantiates every index for a concrete
`n` up to 64. Larger or symbolic domains keep their original quantified fact without eager
enumeration. Any later binders, such as a stack suffix `rest`, stay quantified. This lets one
four-limb field-load fact rewrite offsets 0, 8, 16, and 24. Preparation and stepping also normalize
Fin constructor indices and the projection of the literal `3`. For example, a fact `words 1 = 0`
applies to a value read as `words ⟨1, proof⟩`.

Enable `trace.CIL.factNormalize` to see one event per supplied local proposition when it is
prepared. `Tests/StoreFacts.lean` counts exactly 12 such events for a 27-instruction run. This count
checks normalization frequency; it is not an elapsed-time measurement.

[`Tests/StoreFacts.lean`](../Tests/StoreFacts.lean) checks carry and borrow stores and rejects a
wrong value, address or memory state.

`Tests/MethodContract.lean` proves a caller from two contracts without unfolding either callee.
`Tests/MethodContract.cs` verifies that caller proof unedited against a build whose helpers are
reimplemented and renumbered, and refutes each contract with a concrete run on builds with an
arithmetic or an aliasing bug; `invoke_ok_unique` ties a computed run to the contract's existential
one, and `invoke_ok_observation_unique` does so for one observation of it, such as the returned
values, so the refutation never compares memories.

A contract whose precondition implies well-formed memory and a valid static world can also keep the
`InvocationCertificate` of each call: `MethodContract.Holds.certified` turns `Holds` into
`MethodContract.Certified`, whose clause adds the certificate with its visited-state and
returned-state invariants; `Certified.holds` recovers `Holds`, and `Certified.weaken` keeps the
certificate through a `Refines`. `InvocationCertificate.of_invoke` certifies any successful `invoke`
from those two premises, and `InvocationCertificate.of_run` certifies a run of the frame that
checked arguments enter. At a call site, `run_call_of_certified` (from a `Certified` callee) and
`run_call_of_contract_certified` (from `Holds`, a well-formed caller memory and a valid static
world) hand the continuation the callee's certificate, which `run_call_of_contract` drops. At a
fetched call, `cil_certified_call certified input [facts]` leaves the precondition and then the
continuation, and `cil_contract_certified_call holds input [facts]` leaves the precondition, the
caller memory's `WellFormed`, its static world and then the continuation. Both accept `at site` like
`cil_contract_call`. `Tests/InvocationCertificates.lean` uses each of them.

`ValidCall memory inputs outputs` states that memory is well formed, every input buffer is readable
and every output buffer writable. `CIL.Safety.CallingTransport` carries it to later memory so a
caller can pass the same buffers again: `ValidCall.after_write` after any checked write,
`after_enterFrame` after frame entry, `after_below` across memory that keeps old allocations' access
(`AccessBelow`, or `MemoryBelow.accessBelow`), and `after_confined` across a call whose footprint
the inputs lie `Apart` from. `mono` drops buffers, and `input_bound` / `output_bound` give the
identity bound those relations take.

## Construct structs through contracts

A `newobj` of a reference-free struct allocates caller-owned storage, writes zero to every byte,
then runs the constructor with that storage as `this`. The constructor's interface is an ordinary
`MethodContract` whose first argument is `this`; `MethodContract.Constructs c size this value` adds
that it returns no values and that `post` reads back all `size` bytes at `this` as `value`:

```lean
def pairContract : MethodContract PairInput Unit where
  args input := [.reference (.address input.this), .scalar (.i64 input.low), .scalar (.i64 input.high)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 16 1 true = .ok ()
  footprint input := [(input.this, 16)]
  post input _ final _ := read final input.this 16 1 = .ok (pairBytes input)

theorem pair_constructs : pairContract.Constructs 16 PairInput.this fun input _ => pairBytes input :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩
```

The storage does not exist before the step, so a caller names the contract input as a function of
it. `cil_contract_construct holds constructs input [facts]` applies `run_newAggregate_of_contract`
at the fetched `newobj` and leaves the caller memory's `WellFormed`, the precondition over the fresh
storage, and a continuation that resumes at `pc + 1` with the read-back value on the stack. Both
obligations receive `ConstructStorage memory updated this size`: the storage reads back as `size`
zero bytes, is writable at full width, is allocated at `memory.nextIdentity`, and the step kept all
older memory. The continuation also gets the constructor's invocation, the final memory's
`WellFormed`, static-world preservation, `Confined` and `post`. No invocation, step or `loadLocal`
equation is stated. `ConstructStorage.confined` moves `Confined` back to the memory before `newobj`;
`Confined.forget_fresh` then drops the storage, which the caller's frame owns and expires on return.

Because `newobj` zeroes the storage, a constructor that leaves a field unassigned still has a
full-width readback: the field reads back as zero, not as an uninitialized read. A contract may take
that zero readback as a precondition. `run_construct_of_contract` and
`run_construct_of_contract_formed` take the construct step equation instead, like
`run_call_of_contract`; they cover aggregate storage only. `read_append` joins adjacent field reads
into the full readback, and `Confined.write_within` confines a field write to the whole struct.

`Tests/ConstructContract.lean` proves a caller that constructs a 16-byte and a 32-byte (four-limb,
`UInt256`-shaped) struct and reads a field of each, from the constructors' contracts alone; a
constructor that assigns one of two fields; and rejections: a contract without write authority over
its storage, a constructor that writes outside its footprint, and an 8-byte readback at a 16-byte
site. `Tests/ConstructContract.cs` verifies that caller proof unedited against a build whose
constructors write their fields in the opposite order, and refutes the constructor's contract on a
build that stores a wrong field.

## Name exceptional outcomes

An `OutcomeContract` (`CIL.Safety.OutcomeContract`) adds `raises : Input → Memory → Option String`
to a `MethodContract`: where it is `some exception` the method must end in exactly `.thrown
exception` (`Raises`), and elsewhere the normal clause applies. Fuel exhaustion, unsupported
instructions and memory faults never satisfy `Raises`, so a contract cannot be met by getting stuck.
Memory after a throw is not observable to the caller, so `Raises` states none; runtime exceptions
count only where the semantics models them as `.thrown`.

```lean
def percentContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"
```

`cil_raise_steps [facts]` steps a `Raises` goal to its `.throw`; `cil_outcome_call holds input at
site [facts]` continues after a call the callee's contract says returns, whether the caller then
returns or raises, and `cil_outcome_raise holds input at site [facts]` closes a `Raises` goal by
propagating the exception the callee's contract names. `MethodContract.Holds.outcomes` lifts a
normal-only contract, and `invoke_unique` ties a computed fault to the contract's existential one.

`Tests/OutcomeContract.lean` proves every outcome of a two-level chain from the callees' contracts:
`Strict` propagates `Percent`'s exception, returns, or raises its own after `Percent` returns, and
`Root` reads all three off `Strict`'s contract. `Tests/OutcomeContract.cs` verifies those proofs
against the compiled build, and refutes the callee's contract with concrete runs on builds with an
off-by-one threshold or a different exception type.

Import `CIL.Safety.RuntimeExceptions` to name modeled arithmetic failures with `RaisesCLR` and
`OutcomeContract.HoldsCLR`. This contract mode uses the existing arguments, preconditions,
normal-return clause, footprint and `raises` field. Its fixed `ExecutionFault.clrException` mapping
is:

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
exhaustion have no name in this mode. `Raises` and `.thrown` keep their existing meaning.
`OutcomeContract.Holds.clr` lifts an existing thrown-outcome proof.

For a UInt256 `Divide` or `Mod` contract, select `some "System.DivideByZeroException"` in `raises`
when its divisor is zero and prove `HoldsCLR`. Both an explicit throw and the mapped arithmetic
failure can establish this exact outcome. The proof must still reach that fault through the actual
extracted program. `run_fault_raisesCLR`, `run_next_raisesCLR` and `raisesCLR_of_run` compose that
execution; `run_call_raisesCLR_of_contract` propagates a callee contract's named outcome.
`RaisesCLR.not_of_invoke` refutes a wrong name from a settled checked invocation.

`Tests/RuntimeExceptions.lean` proves all mapped cases and refutes wrong names. It also proves
unsigned division and remainder by zero for every dividend and caller memory.
`Tests/RuntimeExceptions.cs`, run by the outcomes suite, checks the CLR type and verifies each
positive contract and wrong-name refutation against its compiled C# method.

## Derive public contracts

A method's proved contract can be more detailed than its callers need. Export a smaller interface by
proving that the internal contract refines it, without unfolding or executing the method again:

```lean
theorem add_public : addPublic.Holds Extracted.program addTo := add_internal.weaken add_public_refines
```

`MethodContract.Refines internal exported` requires the same `args` and `results` encodings, the
exported precondition to imply the internal one, every internal footprint entry to lie `Within` an
exported entry under the exported precondition (so `Confined.widen_within` applies), and the
internal postcondition to imply the exported one under the exported precondition and the internal
footprint's `Confined`. That last premise lets the exported post state a frame fact, such as a read
apart from the footprint surviving through `Confined.read_apart`. `MethodContract.Holds.weaken`
turns a proved `Holds` and a `Refines` into the exported `Holds`.

`OutcomeContract.Refines` adds that both contracts select the same outcome (`raises`) under the
exported precondition; the footprint and postcondition premises apply only where that outcome is
normal return. `OutcomeContract.Holds.weaken` derives the exported outcome contract, and
`OutcomeContract.Refines.of_method` builds a refinement from a normal one and the agreeing outcomes.
A stronger precondition can exclude every exception, after which `OutcomeContract.Holds.normal`
yields a normal-only contract. Both `Refines` are reflexive and transitive.

`Tests/ContractConsequence.lean` derives a bounded `Percent` contract and a framed `AddTo` contract
over an enclosing region, and proves callers through the derived contracts at their call sites, in
both returning and raising outcomes. Its rejections are proved negations: an unjustified stronger
postcondition, a weaker precondition, a smaller footprint and a changed exception type each refute
the `Refines` premise and the derived `Holds` on a concrete input.

## Inherit a callee's contract in a forwarder

Overload forwarders and instance-to-static wrappers compile to `ldarg*; call k; ret`.
`MethodContract.Holds.forward` (`CIL.Safety.Forwarders`) gives such a method its callee's contract
with the forwarder's own argument encoding, `contract.withArgs forwarded`, without stepping either
body:

```lean
theorem sum_forwards : sumContract.Holds Extracted.program sum :=
  add_public.forward (loads := plainLoads [0, 1, 2]) (narrow := none) sum.found addTo.found
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ _ => plainLoads_unchanged _ _)
    (fun _ _ _ _ member => .inl member)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => trivial)
```

`Forwards body calleeBody loads callee narrow` fixes the body to `forwarderCode loads callee narrow`
with no locals, vector argument homes or parameter homes, so frame entry and exit leave memory
unchanged and the callee's precondition, footprint and postcondition carry over verbatim. The loads
are data: each is an argument index and the narrowing the extractor attaches to `bool`, `byte`,
`sbyte`, `short` and `ushort` parameters (`plainLoads` for wider ones). The callee's arguments must
be the forwarder's at those indices, each kept by its load's narrowing (`LoadsUnchanged`); every
forwarder argument must reach the callee or be valid under the precondition, since the forwarder's
own invocation checks them all; the call must expose no unspecified vector bits; and a narrowed `ret
(some kind)` must not change the callee's result (`ReturnsUnchanged`), which holds for a boolean.
Use `Holds.weaken` afterwards to export a different contract.

`MethodContract.Holds.forward_out` covers `ldarg*; ldloca 0; call k; ret`, which passes the address
of a fresh numeric local as a last out argument and drops it. References, spans, arrays, method
pointers and handler tables have no byte home; `ForwardsOut` excludes them with its `notSpan`,
`notArray`, `notPointer` and `notTable` premises. `make_fitting_local` and `make_unknown_local`
require the same exclusions. The local may hold any initializer that fits its kind; the extractor
emits `.unmodeled` without `InitLocals` and the kind's zero with it. The callee runs in the memory
after frame entry and the result is read after the local expires, so the forwarder's contract
`outer` is related to the callee's `inner` through `extend input home` and premises over those
memories. The callee's arguments must be the forwarder's selected by the loads followed by the home,
each kept by its load's narrowing and none with unspecified vector bits; `outer.pre` must give a
well-formed memory in which every forwarder argument is valid (`checked`), since the forwarder
checks them all; `inner.pre` must follow from `outer.pre` with the home fresh, writable and holding
its initializer (`LocalHolds`); the `inner` footprint must name fresh storage or lie inside
`outer.footprint`; the two contracts must encode results alike, as scalars that survive the local's
expiry and that a narrowed `ret` keeps; and `outer.post` must follow from `inner.post` once the
frame has expired. The footprint is checked by the lemma (`Confined.across_frame`). The home's
alignment is not surfaced, so a callee whose precondition requires it cannot be composed yet.

## Compose through imported contracts

A callee from another assembly has no body in the caller's extraction. Give it an import slot
(`CIL.Safety.Imports`): slot `j` is method index `importIndex base j = base.length + j`, past every
extracted method, so running the caller's program alone faults `invalidState` at the call
(`run_call_unlinked`, `importIndex_unlinked`). Do not put a stub body there: a stub's contract is
false, so a theorem assuming it proves nothing.

Prove the caller over every program that links its own, assuming only the import's contract:

```lean
def importsAdd (linked : CIL.Program) : Prop := addContract.Holds linked (importIndex Extracted.program 0)

theorem root_given : HoldsGiven Extracted.program importsAdd (fun linked => rootContract.Holds linked root)
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
the extractor does not resolve imports yet, so `Extracted.imports` and `Extracted.importSignatures`
are empty.

`Tests/Imports.lean` proves `Root` against an imported `AddTo` while reusing the closed `Mix` proof,
discharges it for one appended implementation, shows the unlinked program faults at the import's
call so its contract holds only vacuously, and composes an imported raising `Percent` through both
outcomes of `Strict` and `Root`. The identity checks that bind a slot to a certified library
implementation are not part of this rule; relocating a library into the slot is described next.

## Link separately extracted libraries

A library extracted on its own calls its helpers by its own method indices. `CIL.Safety.Linking`
relocates it into a linked program. `Op.relocate f` renames only the method index of `.call`,
`.newVector256` and `.newAggregate` (`Op.callees`); pcs, locals, profiles and static sites are
unchanged. `Closed lib` says every callee index in `lib` is one of its methods (`Closed.of_check`
decides it), and `RelocatesInto lib linked f` says method `i` sits at `f i` relocated by `f`. Then
`run_relocate` and `invoke_relocate` give exactly the same result: the same memory and values on
return, and on a fault the same pc and fault with only its method index renamed to `f method`. A
raise is still the same `.thrown`, so `MethodContract.Holds.relocate` and
`OutcomeContract.Holds.relocate` move a contract proved on the library alone to its relocated index.

A `Library` is its exported entry and its private helpers. `link app libs` puts library `j`'s entry
at import slot `importIndex app j` and all helpers after the entries, library by library
(`linkSlot`). `link_links` and `link_relocates` hold by construction, so `composed` discharges a
caller's `HoldsGiven` for the concrete linked program from contracts proved on each library alone:

```lean
theorem root_composed : rootContract.Holds (link Extracted.program [addLib]) root :=
  composed (specs := [addContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    closed proved
```

Here `closed` and `proved` are each library's `Closed` and `Holds` facts. `Imports app specs` names
one `Relocatable` property per slot, so libraries may export contracts of different types. Each
library exports only its index-0 method. Static identities are not renamed: two linked libraries
that use the same identity for different bytes fault `invalidState` at the second static access, so
a collision can only make a proof fail, never prove a false statement.

`Tests/Linking.lean` links an `AddTo` library whose entry calls its own `Sum` helper (renamed from
index 1 to 3) and proves the imported `Root` for the concrete linked program, then links a `Percent`
library whose helper raises and shows the exception reaches `Root` through two relocated calls.

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

These contracts retain their hypotheses. For example, `InstructionContract.values` requires
well-formed input memory and valid input values; its memory-effect field does not require those
additional hypotheses. `RunTrace` describes successful execution; fault-preservation proofs need the
appropriate equivalence lemmas.

