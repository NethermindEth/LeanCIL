# Writing checked proofs

Use `CIL.Safety.invoke` for specifications that include checked memory execution.
State the mathematical contract and its input/memory preconditions independently
of the implementation. The [soundness boundary](SOUNDNESS.md) describes what a
successful checked execution establishes.

## Compose instructions

Import `CIL.Safety.SymbolicExecution` and mark definitions used for instruction
lookup with `@[cil_code]`. This complete example executes eight instructions on
symbolic inputs and preserves arbitrary caller memory:

```lean
import CIL.Safety.SymbolicExecution

namespace ProofGuide

@[cil_code] def arithmeticMethod : CIL.Method := {
  code := [.arg 0, .arg 1, .const32 1, .shl, .add, .const32 0, .gtu, .ret]
  locals := [], returnsValue := true }

theorem checked_arithmetic (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [arithmeticMethod] 9 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if left + (right <<< 1) > 0 then 1 else 0))]) := by
  cil_checked_steps

end ProofGuide
```

The [automation regression](../Tests/Automation.lean) checks this pattern and
symbolic branch proofs. This handwritten body demonstrates the tactic; a proof
about an assembly must bind its body to the generated program, as described in
in [Bind bodies to the extraction](#bind-bodies-to-the-extraction), and pass verification.

`cil_checked_steps` composes `invoke_of_run`, `run_next`, `run_return` and
`run_call_of_invoke`. It checks method/instruction lookups and frame setup,
infers intermediate states, and checks the returned values. These lemmas are
also available directly from [StepComposition](../CIL/Safety/StepComposition.lean)
and [CallComposition](../CIL/Safety/CallComposition.lean) for manual proofs.

Its single-step helper, `cil_checked_step []`, first tries `rfl`. A concrete
opcode with symbolic operands can often reduce definitionally without an
expanded dispatcher in the proof term. If needed, it selects a local equation
for argument loads, returns or supported scalar conditional branches, then
uses simplification. Operations outside those equations retain the dispatcher
fallback.

For steps depending on hypotheses, use `cil_checked_steps [truth, stored]`
with the relevant proved facts. A nonempty fact list skips the initial `rfl`:
otherwise a symbolic branch can succeed by assigning an unresolved conditional
expression to the next program counter, leaving the following lookup stuck.
Both straight-line and loop-exit automation try return proofs only for fetched
`.ret` instructions, including narrow returns, so other opcodes do not incur
failed return-step simplification.

For loops, import [LoopAutomation](../CIL/Safety/LoopAutomation.lean).
`cil_loop_steps [facts]` composes an execution segment and `cil_loop_finish [facts]`
proves an exit path and its postcondition. Supply an invariant and decreasing
measure to the loop termination theorem; these tactics do not infer termination.
See the [countdown proof](../Examples/Proofs/Countdown.lean).

A loop body that calls a helper composes through the helper's `MethodContract`
([LoopContract](../CIL/Safety/LoopContract.lean)). `LoopSegment` fixes one cost for
every continuation budget, which a contract's existential fuel cannot supply, so
`loop_terminates_induction` asks each iteration for `LoopTerminates` at its own
state while assuming it at every invariant state of smaller measure. Step to the
call with `cil_loop_advance [facts]`, apply the contract with
`cil_loop_call holds input at site [facts]` (`loop_terminates_call`, or
`loop_terminates_call_formed` for `WellFormed` and the static world), re-establish
the invariant from `Returns` and `Confined` in the continuation, reach the next
head with `cil_loop_steps`, and close with `loop_reaches_terminates` and the
assumption. The [counted-loop proof](../Examples/Proofs/CountCalls.lean) never
unfolds the helper or names its fuel; the loop suite reuses it unedited for a
reimplemented helper and requires it to reject a discarded helper result and a
broken count. On the correct build, a nondecreasing measure and an invariant that
holds at entry and exit but is not preserved each fail at exactly that obligation.

A loop whose helper has an `OutcomeContract` composes both of its outcomes
([LoopOutcome](../CIL/Safety/LoopOutcome.lean)). `LoopOutcome post raises state`
is `LoopTerminates post state` when `raises` is `none` (`loop_outcome_none`) and
`RunRaises` of exactly that exception otherwise (`loop_outcome_some`), so the
proof fixes which outcome the loop reaches before stepping it, typically as a
function of the inputs that the invariant ties to each head state.
`loop_outcome_induction` mirrors `loop_terminates_induction`: only a continuing
iteration needs an invariant state of smaller measure. Step with
`cil_loop_outcome_advance [facts]` and continue past a callee whose contract
returns with `cil_loop_outcome_call holds input at site [facts]`
(`loop_outcome_call`, or `loop_outcome_call_formed`), which leaves the
precondition, the `raises` equation and the continuation in either outcome.
Once `raises` is rewritten to the callee's exception, exit with
`cil_loop_outcome_raise holds input at site [facts]` (`loop_outcome_call_raises`);
that exit has no invariant or measure obligation. `loop_outcome_throw` exits at
the loop's own `throw`, and `loop_outcome_next` and `loop_reaches_outcome`
compose paths in either outcome. `ensures_outcome_of_loop` lifts the head outcome
through frame setup to `EnsuresOutcome pre post raises`, which names the outcome
of every permitted input; with `raises` constantly `none` it is `Ensures`
(`ensures_outcome_none`). `loop_outcome_some_refuted` refutes an expected
exception from any settled run that does not throw it.

The [outcome loop proof](../Examples/Proofs/CountUntil.lean) propagates its
helper's exception after earlier successful calls. The loop suite reuses it
unedited for a reimplemented helper and rejects a helper that raises another
type; on the correct build, a nondecreasing measure, a non-inductive invariant
and a wrong specified exception each fail at that obligation.
`Tests/LoopOutcome.lean` derives the normal-only rules as the `none` instances
and proves that unsupported execution, invalid state and fuel exhaustion never
satisfy an expected loop exception.

## Compose calls through contracts

A caller proof that steps into its callee breaks whenever the callee is
reimplemented. State the callee's interface as a `MethodContract` instead
(`CIL.Safety.MethodContract`) and prove the caller against it:

```lean
def addContract : MethodContract AddInput where
  args input := [.reference (.address input.a), .reference (.address input.b), .reference (.address input.res)]
  pre input m := read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()
  footprint input := [(input.res, 8)]
  post input _ final values := values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)

theorem root_holds (add : addContract.Holds Extracted.program addTo) : rootContract.Holds Extracted.program root
```

`pre` holds formation, authority and the permitted aliasing; the example lets
`res` overlap either input. `Holds` is `Ensures` with the footprint added to the
postcondition (`Holds.ensures`), and fuel stays existential so callers never
depend on a callee's step count. `Confined footprint before after` is the memory
guarantee: earlier allocations and write authority are unchanged, and bytes and
read authority change only inside the footprint (a write grants read access to
what it wrote). `Confined.trans`, `Confined.widen`, `Confined.write`, `Confined.read_eq`
and `Confined.access_write` compose and consume it. A callee with locals writes its own
frame too: list those slots in the footprint while executing, then drop them with
`Confined.forget_fresh` and cover frame entry and teardown with `Confined.then_below`.
`Outside.nil` and `Outside.cons` are simp rules, so `simpa using ⟨hr, hq⟩` closes a
word footprint from per-word `OutsideWord` facts; `Outside.word` builds it as a term.
`Within inner outer` states that an interval lies inside another of the same allocation:
`Confined.widen_within` widens a footprint to one whose entries enclose it, and
`Confined.write_within` confines a write that lies inside one entry, so four limb writes
satisfy a contract that declares one 32-byte output. Entries may overlap.
`Apart r width entry` states that two intervals share no byte, in different allocations
or at disjoint offsets of one. `Confined.read_apart` keeps a checked read of older memory
apart from every entry, taking the allocation's age from `WellFormed`;
`Confined.cells_apart` keeps every byte of an allocation no entry names, and
`WordSnapshots.after_confined` (`CIL.Safety.ConfinedSnapshots`) keeps remembered words.
A snapshot overlapping the footprint needs a postcondition instead. The contract fixes no profile:
the program does, so a cross-profile contract is a theorem quantified over the
per-profile extractions.

A contract may also type its result: `MethodContract Input Output` adds
`results : Output → List Value`, and `post` speaks of the `Output`. `Returns`
requires the returned values to equal `results out` for some `out` satisfying
`post`. Without `Output`, `results` is the identity and `post` sees the values:

```lean
def mixContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post input _ _ v := v = input.1 * 3 + input.2
```

In the caller, `cil_contract_steps [facts]` steps a `∃ fuel, run ...` goal up
to each `.call` and return; `cil_contract_call holds input at site [facts]` applies
the contract at a `bind_call` site (or the fetched call without `at`), leaving the precondition and then a continuation over the
callee's final memory, values, invocation, frame and `Returns`. Destructure
`Returns` as `⟨out, rfl, post⟩` and unfold the contract (`dsimp only [mixContract]`)
so the stack holds the encoded output.
`cil_formed_call` (`run_call_of_contract_formed`) also takes the caller memory's
`WellFormed` and hands the continuation the callee's `final.WellFormed` and
static-world preservation, so contracts need not restate either; `cil_formed_outcome_call`
does the same for `cil_outcome_call`.

Store facts may name their values in source form, such as
`write m r (numberBytes (a + b + c).toNat 8) 1 = .ok m'`. Each checked step
simplifies the goal with the default simp set, its interpreter definitions and
the facts; it also adds every local fact normalised by the default simp set and
the supplied non-local facts, so both sides meet in the same form. Supply any
definition the computed value is stated through, such as a carry or borrow
word, among the facts. The original hypotheses stay in the proof context and in
the simp set; a fact that still differs stops the steps at its instruction, with
the hypothesis shown as stated. Hand-written stepping can use the same
simplification, with an optional simp configuration, as
`cil_fact_simp (config := ...) [definitions] [facts]`.
[`Tests/StoreFacts.lean`](../Tests/StoreFacts.lean) checks carry and borrow
stores and rejects a wrong value, address or memory state.

`Tests/MethodContract.lean` proves a caller from two contracts without unfolding
either callee. `Tests/MethodContract.cs` verifies that caller proof unedited
against a build whose helpers are reimplemented and renumbered, and refutes
each contract with a concrete run on builds with an arithmetic or an aliasing
bug; `invoke_ok_unique` ties a computed run to the contract's existential one.

## Describe buffer contents

`CIL.Safety.BufferContents` states what a contiguous run of integer elements
holds, over the checked memory model. `Contents m base width xs` says element `i`
of `xs : List (BitVec (8 * width))` reads back at `base.element width i` (offset
`base.offset + width * i`, same allocation) as `numberBytes x.toNat width`, with
the byte alignment scalar loads and stores use; `Contents.load_word` turns an
8-byte element into the `loadValue` result. Contents grant no write authority:
`Writable m base width start count` is write authority alone, and
`Filled m base width xs room` is an initialized prefix followed by `room`
writable elements that need not be readable. An empty `Contents` asserts
nothing. `Contents.read` joins the elements into one checked read only given that
read's `access`, so a zero-width read keeps its formation check and elements
separated by a reference slot do not join; `Contents.of_read` splits a checked
read through `read_slice_bytes`. `take`, `drop` and `append` move between
adjacent subranges. `Contents.write_element` and `Contents.write_run` update one
element or a run; `Contents.after_write_apart` and `Contents.after_confined` keep
contents `Apart` from a write or every footprint entry, including disjoint slices
of one allocation; `Filled.push` extends the prefix by one element write without
reading the room. `Filled.fill` and `Contents.transform` prove fill and in-place
map loops of any length (`writeElements`, `transformElements`) as sequence
properties confined to the buffer; `add_element` steps `Unsafe.Add` to an element, and the
[buffer fill proof](../Examples/Proofs/FillWords.lean) carries `Filled` as the invariant
of a compiled loop. `Tests/BufferContents.lean` checks unchanged
neighbouring bytes and sibling slices, and refutes uninitialized, past-end,
overlapping, unjoined and stale claims.

## Construct structs through contracts

A `newobj` of a reference-free struct allocates caller-owned storage, writes
zero to every byte, then runs the constructor with that storage as `this`. The
constructor's interface is an ordinary `MethodContract` whose first argument is
`this`; `MethodContract.Constructs c size this value` adds that it returns no
values and that `post` reads back all `size` bytes at `this` as `value`:

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

The storage does not exist before the step, so a caller names the contract
input as a function of it. `cil_contract_construct holds constructs input [facts]`
applies `run_newAggregate_of_contract` at the fetched `newobj` and leaves the
caller memory's `WellFormed`, the precondition over the fresh storage, and a
continuation that resumes at `pc + 1` with the read-back value on the stack.
Both obligations receive `ConstructStorage memory updated this size`: the
storage reads back as `size` zero bytes, is writable at full width, is
allocated at `memory.nextIdentity`, and the step kept all older memory. The
continuation also gets the constructor's invocation, the final memory's
`WellFormed`, static-world preservation, `Confined` and `post`. No invocation,
step or `loadLocal` equation is stated. `ConstructStorage.confined` moves
`Confined` back to the memory before `newobj`; `Confined.forget_fresh` then
drops the storage, which the caller's frame owns and expires on return.

Because `newobj` zeroes the storage, a constructor that leaves a field
unassigned still has a full-width readback: the field reads back as zero, not
as an uninitialized read. A contract may take that zero readback as a
precondition. `run_construct_of_contract` and `run_construct_of_contract_formed`
take the construct step equation instead, like `run_call_of_contract`; they
cover aggregate storage only. `read_append` joins adjacent field reads into the
full readback, and `Confined.write_within` confines a field write to the
whole struct.

`Tests/ConstructContract.lean` proves a caller that constructs a 16-byte and a
32-byte (four-limb, `UInt256`-shaped) struct and reads a field of each, from
the constructors' contracts alone; a constructor that assigns one of two fields;
and rejections: a contract without write authority over its storage, a
constructor that writes outside its footprint, and an 8-byte readback at a
16-byte site. `Tests/ConstructContract.cs` verifies that caller proof unedited
against a build whose constructors write their fields in the opposite order,
and refutes the constructor's contract on a build that stores a wrong field.

## Name exceptional outcomes

An `OutcomeContract` (`CIL.Safety.OutcomeContract`) adds
`raises : Input → Memory → Option String` to a `MethodContract`: where it is
`some exception` the method must end in exactly `.thrown exception` (`Raises`),
and elsewhere the normal clause applies. Fuel exhaustion, unsupported
instructions and memory faults never satisfy `Raises`, so a contract cannot
be met by getting stuck. Memory after a throw is not observable to the caller,
so `Raises` states none; runtime exceptions count only where the semantics
models them as `.thrown`.

```lean
def percentContract : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"
```

`cil_raise_steps [facts]` steps a `Raises` goal to its `.throw`;
`cil_outcome_call holds input at site [facts]` continues after a call the
callee's contract says returns, whether the caller then returns or raises, and
`cil_outcome_raise holds input at site [facts]` closes a `Raises` goal by
propagating the exception the callee's contract names.
`MethodContract.Holds.outcomes` lifts a normal-only contract, and
`invoke_unique` ties a computed fault to the contract's existential one.

`Tests/OutcomeContract.lean` proves every outcome of a two-level chain from the
callees' contracts: `Strict` propagates `Percent`'s exception, returns, or raises
its own after `Percent` returns, and `Root` reads all three off `Strict`'s contract. `Tests/OutcomeContract.cs` verifies those proofs against the compiled
build, and refutes the callee's contract with concrete runs on builds with an
off-by-one threshold or a different exception type.

Import `CIL.Safety.RuntimeExceptions` to name modeled arithmetic failures with
`RaisesCLR` and `OutcomeContract.HoldsCLR`. This contract mode uses the existing
arguments, preconditions, normal-return clause, footprint and `raises` field.
Its fixed `ExecutionFault.clrException` mapping is:

| Fault | Named CLR exception |
| --- | --- |
| `.thrown exception` | `exception` |
| `.arithmetic .overflow` | `System.OverflowException` |
| `.arithmetic .divideByZero` | `System.DivideByZeroException` |
| Every other fault | None |

Checked add, subtract, multiply and integer conversions report overflow through
this mapping. Integer division and remainder by zero report divide-by-zero.
The admitted runtime model reports overflow for signed minimum divided by
negative one, including its remainder instruction. Invalid arithmetic operands,
invalid bounds, memory faults, unsupported instructions, invalid state and fuel
exhaustion have no name in this mode. `Raises` and `.thrown` keep their existing
meaning. `OutcomeContract.Holds.clr` lifts an existing thrown-outcome proof.

For a UInt256 `Divide` or `Mod` contract, select
`some "System.DivideByZeroException"` in `raises` when its divisor is zero and
prove `HoldsCLR`. Both an explicit throw and the mapped arithmetic failure can
establish this exact outcome. The proof must still reach that fault through the
actual extracted program. `run_fault_raisesCLR`, `run_next_raisesCLR` and
`raisesCLR_of_run` compose that execution; `run_call_raisesCLR_of_contract`
propagates a callee contract's named outcome. `RaisesCLR.not_of_invoke` refutes a
wrong name from a settled checked invocation.

`Tests/RuntimeExceptions.lean` proves all mapped cases and refutes wrong names.
It also proves unsigned division and remainder by zero for every dividend and
caller memory. `Tests/RuntimeExceptions.cs`, run by the outcomes suite, checks
the CLR type and verifies each positive contract and wrong-name refutation
against its compiled C# method.

## Derive public contracts

A method's proved contract can be more detailed than its callers need. Export a
smaller interface by proving that the internal contract refines it, without
unfolding or executing the method again:

```lean
theorem add_public : addPublic.Holds Extracted.program addTo := add_internal.weaken add_public_refines
```

`MethodContract.Refines internal exported` requires the same `args` and `results`
encodings, the exported precondition to imply the internal one, every internal
footprint entry to lie `Within` an exported entry under the exported precondition
(so `Confined.widen_within` applies), and the internal postcondition to imply the
exported one under the exported precondition and the internal footprint's
`Confined`. That last premise lets the exported post state a frame fact, such as a
read apart from the footprint surviving through `Confined.read_apart`.
`MethodContract.Holds.weaken` turns a proved `Holds` and a `Refines` into the
exported `Holds`.

`OutcomeContract.Refines` adds that both contracts select the same outcome (`raises`)
under the exported precondition; the footprint and postcondition premises apply
only where that outcome is normal return. `OutcomeContract.Holds.weaken` derives
the exported outcome contract, and `OutcomeContract.Refines.of_method` builds a
refinement from a normal one and the agreeing outcomes. A stronger precondition
can exclude every exception, after which `OutcomeContract.Holds.normal` yields a
normal-only contract. Both `Refines` are reflexive and transitive.

`Tests/ContractConsequence.lean` derives a bounded `Percent` contract and a
framed `AddTo` contract over an enclosing region, and proves callers through the
derived contracts at their call sites, in both returning and raising outcomes.
Its rejections are proved negations: an unjustified stronger postcondition, a
weaker precondition, a smaller footprint and a changed exception type each
refute the `Refines` premise and the derived `Holds` on a concrete input.

## Compose through imported contracts

A callee from another assembly has no body in the caller's extraction. Give it
an import slot (`CIL.Safety.Imports`): slot `j` is method index
`importIndex base j = base.length + j`, past every extracted method, so running
the caller's program alone faults `invalidState` at the call (`run_call_unlinked`,
`importIndex_unlinked`). Do not put a stub body there: a stub's contract is false,
so a theorem assuming it proves nothing.

Prove the caller over every program that links its own, assuming only the
import's contract:

```lean
def importsAdd (linked : CIL.Program) : Prop := addContract.Holds linked (importIndex Extracted.program 0)

theorem root_given : HoldsGiven Extracted.program importsAdd (fun linked => rootContract.Holds linked root)
```

`Links base linked` means `linked = base ++ rest`, so every extracted method
keeps its index (`Links.refl`, `Links.trans`, `Links.found`). `HoldsGiven base
imports claim` is `∀ linked, Links base linked → imports linked → claim linked`.
Start the proof with `rintro linked ⟨rest, rfl⟩ addHolds`; the step and call
tactics find methods in `Extracted.program ++ rest` unchanged. A helper proved
on the extracted program alone transfers with `MethodContract.Holds.extend` or
`OutcomeContract.Holds.extend`: `run_extend` shows a run that never faults
`invalidState` gives the same result in any linked program, and a raised
exception is not `invalidState`. `HoldsGiven.discharge` instantiates the claim
for a concrete linked program whose import meets its contract, and
`HoldsGiven.closed` states a claim that needs no import.

In an extraction, `bind_import addTo := "System.Void Lib.Adder::AddTo(...)"` resolves
the signature through `Extracted.importSignatures` and defines `addTo` as
`Extracted.program.length + j`, with `addTo.slot`, `addTo.signature` and
`addTo.unlinked` (`Extracted.program[addTo]? = none`) checked by `rfl`; `bind_call`
then names its call site. The certificate accepts a call there only when
`Extracted.imports` has a slot with the site's identity and arity (see
[SOUNDNESS](SOUNDNESS.md)); the extractor does not resolve imports yet, so
`Extracted.imports` and `Extracted.importSignatures` are empty.

`Tests/Imports.lean` proves `Root` against an imported `AddTo` while reusing the
closed `Mix` proof, discharges it for one appended implementation, shows the
unlinked program faults at the import's call so its contract holds only
vacuously, and composes an imported raising `Percent` through both outcomes of
`Strict` and `Root`. The identity checks that bind a slot to a certified library
implementation are not part of this rule; relocating a library into the slot is
described next.

## Read control flow off one step

`CIL.Safety.StepFlow` says where a successful `step` can go without unfolding it.
`step_next_target`: an action that stays in the frame resumes at `pc + 1` of a
continuing instruction or at one of `op.targets`. `step_callee`: only `.call`,
`.newVector256` and `.newAggregate` enter a method, the one they name
(`Op.callees`). `step_call_action` and `step_newVector256_action` /
`step_newAggregate_action` separate a call from a construction. The module
imports only the step simulation, so a consumer reasoning about reachable pcs
does not compile the import and linking layers.

## Move a run that starts inside a region

Embedding relates whole bodies. When only a suffix is shared, `CIL.Safety.RegionRun`
cuts the rest away first. `RegionClosed program region` says fallthroughs, targets
and callee entries of region instructions stay in the region; `regionClosedCheck`
decides it for a region listed as `(method, lower)` suffixes (`inStarts`).
`AgreesOn program other region` says `other` has the same methods and metadata and
the same instruction at every region pc; `AgreesOn.set` and `code_agrees_of_drop`
build it for one replaced body. Then `run_congr_region` gives equal runs from any
region pc, faults included. Masking the code outside the region with `.unsupported`
makes it dead for `Embeds`, so `run_refines` carries the suffix run on to a body
with a different prefix; `Tests/RegionRun.lean` moves a suffix after inline code
to the same suffix after a helper call, one pc earlier.

## Link separately extracted libraries

A library extracted on its own calls its helpers by its own method indices.
`CIL.Safety.Linking` relocates it into a linked program. `Op.relocate f` renames
only the method index of `.call`, `.newVector256` and `.newAggregate`
(`Op.callees`); pcs, locals, profiles and static sites are unchanged.
`Closed lib` says every callee index in `lib` is one of its methods
(`Closed.of_check` decides it), and `RelocatesInto lib linked f` says method `i`
sits at `f i` relocated by `f`. Then `run_relocate` and `invoke_relocate` give
exactly the same result: the same memory and values on return, and on a fault
the same pc and fault with only its method index renamed to `f method`. A raise
is still the same `.thrown`, so `MethodContract.Holds.relocate` and
`OutcomeContract.Holds.relocate` move a contract proved on the library alone to
its relocated index.

A `Library` is its exported entry and its private helpers. `link app libs` puts
library `j`'s entry at import slot `importIndex app j` and all helpers after the
entries, library by library (`linkSlot`). `link_links` and `link_relocates`
hold by construction, so `composed` discharges a caller's `HoldsGiven` for the
concrete linked program from contracts proved on each library alone:

```lean
theorem root_composed : rootContract.Holds (link Extracted.program [addLib]) root :=
  composed (specs := [addContract.relocatable]) (root_given.mono fun _ met => met 0 (by decide)) rfl
    closed proved
```

Here `closed` and `proved` are each library's `Closed` and `Holds` facts.
`Imports app specs` names one `Relocatable` property per slot, so libraries may
export contracts of different types. Each library exports only its index-0
method. Static identities are not renamed: two linked libraries that use the
same identity for different bytes fault `invalidState` at the second static
access, so a collision can only make a proof fail, never prove a false statement.

`Tests/Linking.lean` links an `AddTo` library whose entry calls its own `Sum`
helper (renamed from index 1 to 3) and proves the imported `Root` for the
concrete linked program, then links a `Percent` library whose helper raises and
shows the exception reaches `Root` through two relocated calls.

## Reuse framework contracts

When extending generic safety proofs, reuse the facts established by the shared
dispatch or traversal proof. Names in this table are in `CIL.Safety`, except
the base relabeling helpers in `CIL.Embedding`.

| API | Reusable information | Source |
| --- | --- | --- |
| `RunTrace` | Successful execution through next, return, call and construction cases | [ExecutionTrace](../CIL/Safety/ExecutionTrace.lean) |
| `FrameSetup` | Fresh ownership, frame allocations, preservation below the allocation boundary, static bindings and conditional validity | [FrameSetupLemmas](../CIL/Safety/FrameSetupLemmas.lean) |
| `InstructionContract` | Memory effects and conditional output-value validity from one instruction analysis | [InstructionMemoryLemmas](../CIL/Safety/InstructionMemoryLemmas.lean) |
| `StaticInstructionContract` | Corresponding contract for static-memory instructions | [StaticMemoryLemmas](../CIL/Safety/StaticMemoryLemmas.lean) |
| `StepContract` | Memory/frame effects and conditional live-value validity for a checked action | [ExecutionInvariants](../CIL/Safety/ExecutionInvariants.lean) |
| `Fallthrough`, `Branching` | Shared relabeling proofs for base instruction families | [BaseStep](../CIL/Embedding/BaseStep.lean) |

These contracts retain their hypotheses. For example, `InstructionContract.values`
requires well-formed input memory and valid input values; its memory-effect field
does not require those additional hypotheses. `RunTrace` describes successful
execution; fault-preservation proofs need the appropriate equivalence lemmas.

## Keep proof work local

Prefer a small `change` or an instruction equation over repeatedly unfolding
`run`, `CIL.Safety.step` and `CIL.step`. For generic opcode proofs, split the
opcode and stack shape before splitting operand constructors, and close
definitionally equal cases early. Share the remaining family-level reasoning.
For concrete execution, compose steps first and simplify the resulting value
equation separately when needed.

Measure changes with fresh Lean processes and prebuilt dependencies on both
revisions. Alternate baseline and candidate runs serially on the same machine,
and include downstream consumers. Record elapsed time, CPU time, `.olean` bytes,
peak process memory and kernel replay separately. A smaller artifact can still
require expensive elaboration or cause callers to repeat work; peak memory also
includes imported environments. Keep kernel replay and the axiom audit enabled.

The [validation guide](VALIDATION.md#proof-automation) describes the regression
coverage and commands for checking the proof tactics.

## Bind bodies to the extraction

Reusable execution and contract theorems are stated over a generic program and
bound to each extraction by a method-body equality. Prove those equalities with
`cil_body` (from `CIL.MethodBinding`, also imported by `CIL`) instead of `rfl`:

```lean
import CIL.MethodBinding

have found : Extracted.program[2]? = some (Full.fullBody Extracted.profile 9 5 7) := by cil_body
```

`cil_body` runs `rfl`, so the proof is the same kernel-checked `Eq.refl`. Only
when `rfl` fails does it evaluate both closed sides and report, for each
differing `Method` field, the first differing index, both elements and both
lengths, instead of only `rfl`'s type mismatch:

```text
cil_body: rfl could not prove the method-body binding
method index 1
field code: first difference at index 1 (left length 6, right length 6)
  left:  CIL.Op.brzero 10
  right: CIL.Op.brzero 4
```

The left side is the extraction's body. An index past the end of the program is
reported with the program's length. The diagnostic is computed after the
failure through compiled evaluation and is never proof evidence; it also works
for `Method = Method` goals. `Tests/MethodBinding.lean` covers both outcomes.

### Methods by signature

Extraction numbers methods by the reachable call graph, so adding or reordering
a callee renumbers unrelated methods and breaks every literal index. Name them
by their exact emitted signature (`Extracted.signatures`) instead:

```lean
import CIL.MethodIdentity

bind_method root rootBody := "System.UInt64 Examples.Calls::Root(System.UInt64,System.UInt64)"
bind_callee left leftBody := "System.UInt64 Examples.Calls::Left(System.UInt64,System.UInt64)" from rootBody

theorem left_spec (x y : W64) (m : Memory) :
    invoke Extracted.program 4 left [.i64 x, .i64 y] m = some (m, [.i64 (x - y)]) := rfl
```

`bind_method` defines `root` (the index), `rootBody` (the extracted body) and
the `rfl` theorems `root.signature` and `root.found` (`@[cil_code]`).
`bind_callee` also requires the parent to call that method and adds
`left.call`, the instruction at its call site (`from rootBody [k]` selects one of
several); expected bodies take the index as a parameter, so `.call left 2`
survives renumbering. `method_named "sig"`
is the bare index as a term. A missing signature lists the methods with the
same name, or every method; a duplicate lists each index; a parent that does not
call the method lists what it does call:

```text
no extracted method has signature
  System.UInt64 Examples.Overloads::Pick(System.Int64)
methods named Pick:
  [3] System.UInt64 Examples.Overloads::Pick(System.UInt64)
  [4] System.UInt32 Examples.Overloads::Pick(System.UInt32)
```

When a helper's name is not stable, bind it by call shape instead:
`bind_callee left leftBody := call 2 from rootBody [1]` binds the second call in
`rootBody` with two arguments, and emits the same theorems with the signature read
from the table. Without `[k]` there must be exactly one such call; otherwise the
error lists each site's pc and callee.

The signature is the Cecil full name, matched exactly. Resolution only locates
an index; the body is still bound by the kernel and the extraction certificate.
`bind_import` reports a missing import signature the same way, listing imports
with the same name or every import, and says when the extraction has no imports.
`Tests/MethodIdentity.lean` covers the diagnostics, and `Tests/MethodIdentity.cs`
verifies one unedited proof against two builds with different numbering.

### Loop heads and call sites

Inside a method, name positions by structure instead of by pc, so a statement
inserted elsewhere moves the label with the code (`CIL.StructuralLabels`):

```lean
import CIL.StructuralLabels

bind_loop reduce := rootBody [1]     -- the second loop head in pc order
bind_call after := step from rootBody [1]

theorem body : (rootBody.code.drop reduce).take 4 = [.local 0, .const32 3, .sub, .setLocal 0] := rfl
```

A loop head is the target of a branch at the same or a later pc. `bind_loop`
defines `reduce` and `reduce.latch`, the last pc branching back to it, and
`reduce.backEdge` checks both. `bind_call` names a `.call` to a bound method
and adds `after.call`. The `[k]` is needed only when there are several; without
it every candidate is listed rather than the first one taken:

```text
rootBody has 2 loops; select one with [i]:
  [0] head pc 3, back edge from pc 5
  [1] head pc 6, back edge from pc 7
```

Labels read the compiled layout, so a compiler that rotates a loop moves its
head; a cutpoint that must survive that, such as `Examples/Proofs/Countdown.lean`,
keeps a unique-instruction predicate. `Tests/StructuralLabels.lean` covers the
diagnostics, and `Tests/StructuralLabels.cs` verifies one unedited proof against
a build with a statement inserted before both loops.

### PDB local names and source locations

When a portable PDB matches the assembly (next to it, or embedded), extraction
also writes `Symbols.lean`, the module `ExtractedSymbols`; `Extracted.lean` is
byte-identical either way. A proof that imports it can name locals by their C#
names, resolved in the scope that contains a pc:

```lean
import ExtractedSymbols

theorem stores : sumBody.code[atWide + 1]? = some (.setLocal (local_named sum "carry" at (atWide + 1))) := rfl
```

A name used for one slot needs no `at`; a name the PDB gives two slots, such as
`carry` declared in two sibling blocks, is an error listing each slot and range
until `at pc` picks the innermost scope containing it. Compiler temporaries and
values the compiler keeps on the stack have no name and keep their index; a
missing name lists the method's named locals. Importing `ExtractedSymbols`
without a matching PDB fails verification with that reason, naming the assembly
and method. Consumer packages import it like `Extracted`, directly or through
their own modules, in `leancil verify --proof-root` and `leancil verify-batch`.
Only proofs whose imports reach it compile it, replay it and bind its hash into
their cache key, so a PDB-only change rechecks them and no symbol-free proof.

With the module imported, `cil_body` and `cil_embed` failures end with the
nearest sequence point of the actual pc they report:

```text
source of actual pc 23: Names.cs:12:9
```

Extraction errors for an unsupported instruction add `Source: Names.cs:16:21`
after the method whenever the PDB is present, imported or not. Source paths are
relative to the directory the method documents share. Without a PDB every
message is unchanged. `Tests/DebugNames.lean` covers scoping and both
diagnostics, and `Tests/DebugNames.cs` checks byte-identical extraction, an
unedited proof across an inserted local, and each message with and without a PDB;
`Tests/ConsumerSymbols.cs` covers consumer packages, batches and PDB-only changes.

### Bodies modulo dead code

A profile can make the extractor emit dead `.unsupported` blocks that shift
every later branch target, which breaks a `cil_body` equality even though
reachable behaviour is unchanged. `cil_embed` (from `CIL.Embedding.Tactic`)
proves the weaker `MethodEmbeds` relation instead: every live instruction of the
literal body appears in the extracted method at a mapped pc, with its code
targets mapped the same way and its fallthrough kept adjacent. Keep the proof
over the literal body and transport it with the lemmas in
`CIL.Safety.Embedding.Simulation`:

```lean
import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Simulation

theorem bound : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile 9 5 7) := by cil_embed

-- A run proved over the literal body holds for the extraction with the same fuel.
example {fuel : Nat} {args : List CIL.Safety.Value} {m : CIL.Safety.Memory} {r : CIL.Safety.Memory × List CIL.Safety.Value}
    (h : CIL.Safety.invoke (Extracted.program.set 2 (Full.fullBody Extracted.profile 9 5 7)) fuel 2 args m = .ok r) :
    CIL.Safety.invoke Extracted.program fuel 2 args m = .ok r := bound.invoke h
```

`bound.certificate` transports an `InvocationCertificate` and
`bound.descriptors` the program's static descriptor list; `ProgramRefines.set`
composes several bound methods. Named exceptions transfer too:
`bound.raises` transports `Raises`, `bound.holds` an `OutcomeContract.Holds`
with both clauses (from `CIL.Safety.Embedding.Outcomes`), and
`Embeds.invoke_raise` states the actual fault, whose pc is the one the map
assigns in the throwing method. Other faults, including fuel exhaustion and
`.unsupported`, do not transfer. The pc map is computed outside the kernel and then checked by
it, so a wrong map is rejected, not trusted. A changed reachable instruction or
an inserted live one is reported by expected and actual pc:

```text
cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Op.brzero 4
  renamed:  CIL.Op.brzero 6
  actual:   CIL.Op.brzero 4
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 4; actual pc 4 (CIL.Op.const32 0x00000009#32) is not the image of any live expected pc
```

The kernel check takes about 0.12 s for a 202-instruction body and 1.3 s for
1,414 instructions. See [docs/SOUNDNESS.md](SOUNDNESS.md#method-body-embedding)
for the exact conditions and limits; `Tests/MethodEmbedding.lean` covers both
outcomes, and `Tests/OutcomeEmbedding.lean` transfers a raising helper and its
caller across an inserted dead block, with the relocated throw pc.
