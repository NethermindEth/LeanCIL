# Failures of leancil commands and proof steps

Read this when a `leancil` command exits with `1` or a proof step stops. It maps the stage, the
`failed.json` kind and the message the tool prints to its meaning and the next action.

## Diagnostic format

A failed command prints three lines on stderr, then any Lean errors under `Lean errors (N):`:

```text
Invalid: Lean could not prove the selected theorem.
  Stage: proof checking
  Next: Read the Lean diagnostic below and check the implementation against the stated contract, including its preconditions.
  Goals: add --goals to print the goal at each `sorry` and failing tactic.
```

`check`, `verify` and `audit-library` start the first line with `Invalid:`; every other command
starts it with `Error:`. Each Lean error cites `file:line:column` in the file you edit, with
1-based lines and 0-based columns.

## Stages

| `Stage:` | Meaning | Next action |
| --- | --- | --- |
| `arguments` | A missing, unknown or repeated option | Run `leancil --help` |
| `assembly loading` | The DLL is missing or unreadable | Fix the path; build the assembly |
| `metadata and CIL validation` | The selector matched no single method, or the method or something it reaches is outside the supported subset | Fix the selector from `leancil list`, or report the named item to the user as unsupported |
| `extraction integrity` | The artifacts do not match the assembly, the extractor or the recorded settings | Run `leancil extract` again, then repeat the command |
| `proof selection` | The proof file or theorem name is wrong, or the proof imports a module the tool does not ship | Fix `--proof` and `--theorem`, or the import |
| `Lean library build` | The framework library or the proof's dependencies did not build | Install Lean and Lake at the toolchain `leancil --version` prints; read the build error |
| `proof checking` | Lean reported an error in the proof | Read the first Lean error; rerun with `--goals` |
| `open goals` | A `--goals` run found a `sorry`, a failing tactic or an unsolved goal | Prove each listed goal in place, then rerun |
| `kernel replay`, `theorem audit` | The compiled proof failed kernel replay, or the theorem depends on `sorryAx` or an axiom other than `propext`, `Quot.sound` and `Classical.choice` | Remove every `sorry` and extra axiom; check that `--theorem` names a proved theorem |
| `compile check` | A proof did not elaborate under `verify-batch --check` or `gates --check` | Fix the elaboration errors |
| `proof outline` | `new-proof` cannot state a starting proof for this method's shape, or the proof path exists | Write the proof by hand from the closest example; choose a new path |

## failed.json

A failed `verify` writes `failed.json` in the artifact directory and removes `verified.json`;
`verify-batch` and `gates` write it into each failing request's output. Its `kind` classifies the
failure, `diagnostics` lists every Lean error with its location, `message` is the unmodified
output and `rerun` is the command that repeats the request
([failure reports](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#failure-reports)).

| `kind` | Meaning | Next action |
| --- | --- | --- |
| `stale-input` | The assembly, artifacts or proof inputs changed after extraction or during verification | Run `extract` again, then `verify` |
| `unsupported-extraction` | The method or something it calls is outside the supported subset | Report the named item to the user |
| `invalid-request` | The proof path, the theorem name or an import is wrong | Fix `--proof`, `--theorem` or the import |
| `elaboration-error` | A Lean error other than an unsolved goal or a resource limit: a failed tactic, a missing import, an unknown name | Read the error. A failed tactic can mean the code does not satisfy the theorem |
| `unsolved-goal` | A tactic block left goals open, or a `--goals` run stopped at the goals it found open | Rerun with `--goals`. The code may not satisfy the theorem |
| `resource-limit` | Heartbeats or recursion depth ran out; `resource` names which | Confirm the method and profile first, since a proof run on another method or of a false property also exhausts limits. Then split the proof or supply the missing fact |
| `replay-or-audit-rejected` | Kernel replay or the axiom audit rejected the proof | Remove `sorry` and extra axioms |
| `refutation` | The theorem verified, and it states `Not (contract.Holds ...)` | Report that the contract is refuted; `verified.json` certifies the refutation |
| `unclassified` | Anything else, such as a missing tool | Read `message` |

An unsolved goal or a failed tactic means the proof is incomplete or the property is false, and
the report does not say which. Only a verified theorem of the `refutation` form proves that the
code violates a contract.

## Goals, traces and JSON

| Command | Output |
| --- | --- |
| `leancil verify artifacts/Method --goals` | The goal at each `sorry`, before each failing tactic and left unsolved, in source order, each as `file:line:column: sorry`, `failing tactic` or `unsolved` followed by the hypotheses and target. The first line is `Invalid: N goals remain in <proof>.` |
| `leancil verify artifacts/Method --trace` | Under `Trace (N entries):`, each step the proof takes with its pc and instruction, the lemmas applied and what changed, then for each `cil_` tactic its step count and the obligation tags of the goals it left |
| `leancil verify artifacts/Method --format json` | One JSON report on stdout: `result` (`verified` or `failed`), `stage`, `messages`, `rerun` and `failures`, one record per Lean error with its `source`, the `tactic` that stopped, the `cil` pc, instruction and C# source line, the `state` reached and expected, the `missing` fact and `suggestions`. `goals` and `trace` are filled with `--goals` and `--trace` |
| `leancil watch --goals` | The open goals of every recorded proof after each save |

Write `sorry` where the next step is unclear and read its goal with `--goals`. A `sorry` anywhere
in the proof file is an open goal, whichever theorem is selected. Field details are in
[goals](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#goals-of-an-unfinished-proof),
[JSON output](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#machine-readable-verify-output)
and [traces](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#trace-the-proofs-steps).

## Messages

| Message | Meaning | Next action |
| --- | --- | --- |
| `No method matches selector` | The selector names no method | Copy the signature from `leancil list`; give the parameter list |
| `Ambiguous method selector ... Candidates:` | Several methods match | Copy one candidate, with its namespace or return type |
| `Unsupported static initialisation: T has a static constructor` | The method's type has a static constructor | Ask the user whether every caller runs it first; only then pass `--assume-initialized T` and report it as an assumption |
| `Unsupported ...` at `metadata and CIL validation` | The named instruction, call, type or signature is outside the supported subset | Report it; `leancil blockers` lists every blocker of a method at once |
| `Stale or mismatched verification artifact: assembly has changed since extraction.` | The DLL was rebuilt after `extract` | Run `extract` again. `verify` does this itself |
| `Stale or mismatched verification artifact: extractor has changed since extraction.` | The tool was updated after `extract` | Run `extract` again |
| `Stale or mismatched verification artifact: ... differs from regenerated CIL.` | `Extracted.lean` was edited or belongs to another build | Run `extract` again; never edit generated files |
| `Proof file not found:` | `--proof` or the saved setting names no file | Pass `--proof`; after moving files pass `--proof-root` again too |
| `... imports X, a LeanCIL repository module that the tool does not ship.` | The proof imports one of LeanCIL's example or test modules | Import `CIL` modules; `CIL.Safety.Memory.empty` is the empty caller memory |
| `Required command not found:` | .NET, Lean or Lake is not on `PATH` | Install it |
| `Consumer package must depend on leancil. Run lake update first.` | The `--proof-root` package has no resolved `leancil` dependency | Add the `[[require]]` block `leancil --version` prints, then `lake update` |
| `Consumer leancil sources differ from the verifier's bundled framework:` | The package pins another LeanCIL revision than the installed tool's | Set `rev` to the revision the message and `leancil --version` name, then `lake update` |
| `Consumer and verifier Lean toolchains differ.` | The package's `lean-toolchain` differs from the tool's | Copy the toolchain `leancil --version` prints |
| `Consumer dependencies must be git packages pinned by a full revision in lake-manifest.json.` | A dependency is a local path or unpinned | Pin it by Git revision |
| `Extracted.lean is reserved for the selected extraction artifact` | The package holds a generated `Extracted.lean` | Move the `extract` output directory outside the package |
| `Batch outputs must lie outside the consumer sources` | A batch `output` is inside the proof package | Put outputs under `artifacts/` |
| `--check accepts compilation requests, not rejection expectations.`, `--check cannot evaluate mutation rejection expectations.` | A selected request or variant expects `rejected` under `--check` | Drop `--check`, or select requests that expect success |
| `No gates match the requested selection.`, `No gates depend on the changed paths.` | `--method`, `--profile` or `--changed` selected nothing | Widen the selection |

## Tactic messages

| Lean error | Meaning | Next action |
| --- | --- | --- |
| `cannot step pc N (op) at memory M` | A loop tactic lacks a fact for that instruction; the message names its kind (a span's validity, an element's address, a `form` fact, a load's value, a store equation) | Prove that fact and pass it in the tactic's fact list |
| `pc N is a call (op); cross it with cil_loop_call` | `cil_loop_steps` or `cil_loop_finish` reached a call | Use `cil_loop_advance`, then `cil_loop_call holds input at site` |
| `target state not matched at pc N` | The path reached the target pc with another frame, stack or memory | State the fact or the target in the reached form the message shows |
| A stopped walk with `if c then target else next` as the pc, or `cil_lookup: undecided branch` | No fact decides the branch condition | Pass `c = 0` or its negation, or `split` and resume in each case |
| `Snapshot stepping took no step; justify the local premises` | The snapshot form found no home, write access or `WellFormed` fact for the first local store | Put those premises in context ([snapshot walks](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots)) |
| `cil_body: rfl could not prove the method-body binding` | The expected body differs from the extracted one; the message shows the first differing instruction | Update the expected body, or bind by signature with `bind_method` |
| `no extracted method has signature` | A `bind_method` or `bind_callee` signature is not in this extraction; the message lists the methods with that name | Copy the listed signature |
| `Case tag ... not found` | A `case` names no open goal; the message lists the open tags | Use a listed tag |
| ``Tactic `rfl` failed`` on an `invoke` equality | The stated result is not what the method computes for those arguments, or the fuel literal is smaller than the number of steps the run takes | Compare the statement with the C#; check the fuel |

`cil_checked_steps`, `cil_contract_steps` and `cil_raise_steps` stop at the first instruction
they cannot step and leave its goal, and fail when they cannot take a first step. Rerun with
`--format json` and read `failures[].missing`
for the kind of fact that step lacks
([stepping reference](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#supply-step-facts)).
