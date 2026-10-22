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
`Confined.forget_fresh` and cover frame entry and teardown with `Confined.then_below`. The contract fixes no profile:
the program does, so a cross-profile contract is a theorem quantified over the
per-profile extractions.

In the caller, `cil_contract_steps [facts]` steps a `∃ fuel, run ...` goal up
to each `.call` and return; `cil_contract_call holds input at site [facts]` applies
the contract at a `bind_call` site (or the fetched call without `at`), leaving the precondition and then a continuation over the
callee's final memory, values, invocation, frame and postcondition.
`cil_formed_call` (`run_call_of_contract_formed`) also takes the caller memory's
`WellFormed` and hands the continuation the callee's `final.WellFormed` and
static-world preservation, so contracts need not restate either; `cil_formed_outcome_call`
does the same for `cil_outcome_call`. Stated
store facts must match the computed value syntactically: `generalize` a value
the simplifier would rewrite, or state the fact in the computed form.

`Tests/MethodContract.lean` proves a caller from two contracts without unfolding
either callee. `Tests/MethodContract.cs` verifies that caller proof unedited
against a build whose helpers are reimplemented and renumbered, and refutes
each contract with a concrete run on builds with an arithmetic or an aliasing
bug; `invoke_ok_unique` ties a computed run to the contract's existential one.

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
def percentContract : OutcomeContract CIL.W64 where
  args v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post v _ _ values := values = [.scalar (.i64 v)]
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
composes several bound methods. The transfer is for successful checked
execution only. The pc map is computed outside the kernel and then checked by
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
outcomes.
