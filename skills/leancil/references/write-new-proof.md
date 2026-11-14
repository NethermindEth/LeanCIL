# Write a new LeanCIL proof

Read this when the user has code and an informal requirement. Write the specification, generate
a starting proof, fill its holes from the goals `verify --goals` prints, then verify.

## 1. State the property

Write what the method must do as ordinary Lean, independent of the instructions it compiles to:
a model function, a postcondition, or both. Make every input quantifier, every precondition on
the inputs or the caller memory, and every permitted write explicit. When the user already has
such definitions with theorems, follow [bridge-model-proof.md](bridge-model-proof.md).

Agree the statement with the user before proving it. LeanCIL cannot detect a proof of the wrong
statement.

| Claim | Statement form |
| --- | --- |
| A scalar method returns a value, at fixed fuel | `(CIL.Safety.invoke Extracted.program fuel 0 args memory).map Prod.snd = .ok [result]`, as in [Add](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Add.lean) |
| A method terminates with a postcondition, for inputs meeting a precondition | `CIL.Safety.Ensures Extracted.program method pre post`, with `pre : args initial` and `post : args initial final values`, as in [Countdown](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Countdown.lean) |
| A method meets an interface that callers reuse, with the memory it may change | A `MethodContract` (`args`, `pre`, `footprint`, `results`, `post`) and `contract.Holds Extracted.program method` |
| A method returns or throws a named exception | An `OutcomeContract`, as in [CountUntil](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/CountUntil.lean) |
| A run from the current state reaches a postcondition, inside a larger proof | `WP (Execution (fun fuel => invoke ...)) post` ([WP](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#state-goals-with-wp)) |

The entry method is index `0`; name any other method with `bind_method` instead of a literal
index. Arguments are `CIL.Safety.Value`s such as `.scalar (.i32 x)` and `.scalar (.i64 x)`, with
`x : CIL.W32` (`BitVec 32`) or `CIL.W64` (`BitVec 64`). Fuel exhaustion, a fault and an
unsupported state are never successes, so `Ensures` and `Holds` state total correctness.

## 2. Generate a starting proof

```sh
leancil extract path/to/Lib.dll 'Type::Method(uint)' artifacts/Method
leancil new-proof artifacts/Method Proofs/Method.lean
```

`new-proof` prints, for example:

```text
Wrote Proofs/Method.lean: a starting proof of System.UInt32 Lib.Type::Method(System.UInt32)
  Holes: 8 obligations, 0 paths not outlined (each `sorry`; verify rejects the file until none remain)
  Next: leancil verify artifacts/Method --proof Proofs/Method.lean --goals prints the goal at each hole; fill them, then verify without --goals
```

The file states `ExampleProof.correctness` as an `Ensures` theorem over the method's parameters,
binds the entry, each loop and each callee, steps the paths it can, and leaves each decision as
a commented `sorry`:

- `Precondition` and `Postcondition` are definitions to replace with the specification.
- A loop gets `invariant` and `measure` definitions to replace, and a loop in a method that takes
  a reference gets a `footprint`: the caller memory the loop may write.
- A callee gets a `MethodContract` with `pre` and `post` to replace and a `Holds` theorem.
- A hole whose comment starts with `not outlined:` marks a path the outline could not step; the
  comment names the instruction it met and what that step needs.

`new-proof` never replaces a file. It refuses a shape it cannot state at the stage
`proof outline` and writes nothing; then write the proof by hand from the closest example below
([outline reference](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#start-a-proof)).

A proof written by hand starts with `import Extracted` and `import CIL`, plus
`import CIL.Safety.LoopScaffold` when it uses `bind_entry` or `bind_cutpoint`, and ends each
theorem with `#print axioms`.

## 3. Fill the holes

```sh
leancil verify artifacts/Method --proof Proofs/Method.lean --goals
```

The run exits with `1` and lists every open goal on stderr, for example:

```text
Invalid: 8 goals remain in Proofs/Method.lean.
  Stage: open goals
  Next: Prove each goal listed below in place of its `sorry` or failing tactic, then rerun.
  Goals (8):
    Proofs/Method.lean:17:41: sorry
      value : W32
      ⊢ Prop
```

Fill the definitions first, since every later goal mentions them, then one hole at a time,
rerunning after each. Where the next step is unclear, write `sorry` and read its goal. Finish
with `leancil verify artifacts/Method --proof Proofs/Method.lean`, which must print
`Verified: ExampleProof.correctness`. When a tactic stops, look its message up in
[failures.md](failures.md).

Two commands shorten the loop:

```sh
leancil workspace path/to/Lib.dll 'Type::Method(uint)' --profile scalar \
  --proof Proofs/Method.lean --theorem ExampleProof.correctness
leancil watch . --project path/to/Lib.csproj --goals
```

- `workspace` gives an editor live goals: it generates the modules `Extracted.KEY` and
  `ExtractedSymbols.KEY` into the proof's Lake package and prints the `import` line to use.
- `watch` rebuilds the C# after every save, refreshes the changed extractions, verifies the
  affected proofs and prints their goals; `--once` runs one cycle. It verifies the proofs
  `workspace` recorded with `--theorem`, so run `workspace` once per method first.

Only `leancil verify`, which `watch` runs, produces a certificate
([workspace](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md#proof-authoring-workspace)).

## 4. Choose the tactic

`[facts]` is a list of proved facts the steps depend on. `cil_checked_steps`, `cil_loop_recurse`,
`cil_loop_advance`, `cil_loop_call` and `cil_loop_finish` accept it omitted; the other tactics
and the snapshot forms need it, written `[]` when empty.

| Goal | Tactic |
| --- | --- |
| An `invoke` or `run` equality to a result or a located fault | `cil_checked_steps [facts]`; `cil_checked_steps n [facts]` takes exactly `n` steps and leaves the residual `run` equation |
| `WP`, or success at an existential fuel, crossing calls through contracts | `cil_contract_steps [facts]`; `cil_contract_steps n [facts]` takes at most `n` steps; `cil_contract_steps [facts] until continuation` stops when `continuation` closes the goal |
| The same, and the path stores or loads numeric locals over symbolic caller memory | `cil_contract_steps (snapshots := snapshots) [facts]` or `cil_checked_steps (snapshots := snapshots) [facts]`, with `snapshots : LocalSnapshots memory frame.locals known` ([snapshot walks](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots)) |
| One call, keeping its precondition as a goal | `cil_contract_call holds input at site [facts]` |
| A loop path to the next loop head | `cil_loop_recurse hypothesis values [facts]`, leaving `case invariant` and `case measure` |
| A loop path to a call, then the call | `cil_loop_advance [facts]`, then `cil_loop_call holds input at site [facts]` |
| A loop exit and its postcondition | `cil_loop_finish [facts]`, leaving `case postcondition` |
| An element write's authority, bound and footprint membership | `cil_loop_obligation [definitions]` |
| A `Raises` goal | `cil_raise_steps [facts]` |
| `Extracted.program[i]? = some body` | `cil_body`; write `body` as `Extracted.methodN.withCode [...]` so it carries the extraction's `declared` and `environment` |

In a counted form a call is one step. The complete tables are in
[writing proofs](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS.md#choose-a-tactic).

### Calls through contracts

Name methods by signature and call sites by structure, state the callee's `MethodContract`, and
prove `Holds` once:

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

The signature string is the form `leancil list` prints. In the caller, pass the proved `Holds`
theorem and the contract's definition in the fact list. `cil_contract_steps` applies it at the
call, leaves an unproved precondition as `case precondition`, and names the callee's final
memory, output and `CallResult`:

```lean excerpt Examples/Proofs/DepositBoth.lean
cil_contract_steps [holds, depositContract, firstOwned]
  with middle values firstCall
obtain ⟨rfl, firstHeld⟩ := firstCall.post
have firstFramed := firstCall.framed
```

Read `firstCall.post` (the postcondition), `firstCall.framed` (`Confined` to the footprint) and
`firstCall.invoked` by field name. A proof that steps to its return with `cil_contract_steps`
closes the remaining footprint and result goal with `MethodContract.Holds.returns framed post`
([contract stepping](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#step-a-caller-through-its-callees)).

### Loops

`bind_entry` proves the checked frame entry, `bind_loop` names a loop head and `bind_cutpoint`
states the loop-head state. The proof supplies an invariant and a natural-number measure, steps
from entry to the first head, then splits each iteration on its test:

```lean excerpt Examples/Proofs/Countdown.lean
refine invoke_loop_satisfies Extracted.lookup0 rfl enter.setup (header home) (fun _ => True)
  (fun s => s.values.toNat) (fun start => ?_) ?_
· cil_loop_recurse start x
  case invariant => trivial
rintro ⟨x, m, frame⟩ - recurse
by_cases zero : x = 0#32
· cil_loop_finish [zero]
· cil_loop_recurse recurse (x - 1)
  case invariant => trivial
```

Every continuing iteration must decrease the measure; a finite sample of runs does not prove
termination. Close the goals a loop or call tactic leaves by tag (`case invariant =>`,
`case measure =>`, `case precondition =>`, `case postcondition =>`), never by position
([obligation tags](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#obligation-tags),
[loop scaffolding](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding)).

### Facts

- Pass a fact for each step whose condition is not definitionally true: `v = 0` or `Not (v = 0)`
  for a branch on `v`, a successful read, write or formation equation for a memory operation
  ([step facts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#supply-step-facts)).
- Write bit-vector literals in hypotheses and definitions in the form `simp` leaves them:
  `0#32`, `1#64`, `0x80000000#32`.
- Keep the interpreter's own functions (`step`, `run`, `invoke`, `instruction` and the others
  the stepping reference lists) out of `simp` lists. Step with a tactic and pass a fact about the
  operation.
- Use a helper's contract at its call sites and leave its body folded, so caller proofs still
  check after a rewrite of the helper.

## 5. Examples by method shape

| Method shape | Example | Guide |
| --- | --- | --- |
| Straight-line arithmetic | [Add](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Add.lean) | [instruction composition](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#compose-instructions) |
| Calls a helper | [CountCalls](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/CountCalls.lean) | [contract composition](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#compose-calls-through-contracts) |
| Contains a loop | [Countdown](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Countdown.lean) | [loop cutpoints](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#loop-heads-and-call-sites) |
| Reads a span or array | [SpanSum](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/SpanSum.lean) | [span contents](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BUFFERS.md#describe-span-contents) |
| Writes a buffer or span | [FillWords](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/FillWords.lean) | [buffer predicates](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BUFFERS.md#describe-buffer-contents) |
| Reads or writes class fields | [DepositBoth](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/DepositBoth.lean) | [class instances](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#frame-class-instances) |
| Walks a linked list | [PoolIdle](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/PoolIdle.lean) | [class instances](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#frame-class-instances) |
| Holds an array in a class field | [SampleRefill](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/SampleRefill.lean) | [class instances](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#frame-class-instances) |
| Can throw | [CountUntil](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/CountUntil.lean) | [outcome contracts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#name-exceptional-outcomes) |

Copy the closest example's structure and change the statement first. More shapes are listed in
[writing proofs](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS.md#choose-a-proof-interface)
and the [examples index](https://github.com/NethermindEth/LeanCIL/blob/main/docs/EXAMPLES.md).

## 6. A property that does not hold

Report a property that does not hold as a result. Show the user the failing input, or prove the
counterexample as its own theorem:
[WrongAdd](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/WrongAdd.lean)
proves a counterexample to the addition contract for a subtracting implementation, and
`MethodContract.not_holds_of_fault` refutes a contract from a located fault on an input meeting
its precondition
([refutation](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#refute-a-contract)).
