# Failures of leancil commands and proof steps

Read this when a `leancil` command exits with `1` or a proof step stops. It maps the stage, the
`failed.json` kind and the printed message to a meaning and the next action.

## Diagnostic format

A failed command prints three lines on stderr, then any internal errors under
`Internal errors (N):` and any Lean errors under `Lean errors (N):`:

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
| `arguments` | A missing, unknown or repeated option of `extract`, `check` or `verify` | Run `leancil --help` |
| `assembly loading` | The DLL is missing or unreadable | Fix the path; build the assembly |
| `metadata and CIL validation` | The selector matched no single method, or the assembly, the method or something it reaches is unsupported | Fix the selector from `leancil list`, or report the named item |
| `extraction integrity` | The artifacts do not match the assembly, the extractor or the recorded settings | Run `leancil extract` again, then repeat the command |
| `proof selection` | A wrong proof path, theorem name or import, or a wrong option or selection of `verify-batch` or `gates` | Fix the named input |
| `Lean library build` | The framework library or the proof's dependencies did not build | Install Lean and Lake at the toolchain `leancil --version` prints; read the build error |
| `proof checking` | Lean reported an error in the proof | Read the first Lean error; rerun with `--goals` |
| `open goals` | A `--goals` run found a `sorry`, a failing tactic or an unsolved goal | Prove each listed goal in place, then rerun |
| `kernel replay` | The compiled proof failed kernel replay | Read the kernel error |
| `theorem audit` | The selected theorem depends on an axiom other than `propext`, `Quot.sound` and `Classical.choice` | Remove the axioms `Unapproved proof axioms:` lists; check that `--theorem` names a proved theorem |
| `compile check` | A proof did not elaborate under `--check` | Fix the elaboration errors |
| `proof outline` | `new-proof` cannot state a starting proof for this method's shape, or the proof path exists | Write the proof by hand from the closest example; choose a new path |

`gates` also reports these stages for a variant:

| `stage` | Meaning | Next action |
| --- | --- | --- |
| `build` | `dotnet build` of the variant's project and properties failed, or wrote no assembly of the project's `assembly` name | Read the build output in `error`; fix the project or the properties |
| `extraction` | Extracting the variant's method failed | Read `error`; run `leancil extract` on the built assembly |
| `program comparison` | The variant's program does not relate to production's, or to its `programOf` variant's, as its `program` says | Fix the fixture case, or `program` if the change is intended |
| `refutation template`, `proof template` | The template is missing, or its placeholders and `values` differ | Add the missing values or placeholders |
| `statement identity` | The kernel did not accept the variant's theorem at production's statement, or its refutation at that statement's negation, or production did not verify | Read both statements in `error`; state the variant's theorem as production's, naming declarations from a module both proofs import |

## failed.json

`verify` writes `failed.json` into the artifact directory; `verify-batch` and `gates` write it
into each failing request's output. Its `kind` classifies the failure, `diagnostics` lists every
internal error and Lean error with its location, `message` is the unmodified output and `rerun` is the command that
repeats the request
([failure reports](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#failure-reports)).

| `kind` | Meaning | Next action |
| --- | --- | --- |
| `stale-input` | The assembly, artifacts or proof inputs changed after extraction or during verification | Run `extract` again, then `verify` |
| `unsupported-extraction` | The method or something it calls is outside the supported subset | Report the named item |
| `invalid-request` | The proof path, the theorem name or an import is wrong | Fix `--proof`, `--theorem` or the import |
| `internal-error` | Lean or a LeanCIL tactic printed an internal error, such as `PANIC at ...` or `Error: index out of bounds`, and the run is rejected even when Lean exited with `0`. The report says nothing about whether the proof holds | Report the message, with the proof and the module it names, as a LeanCIL issue |
| `elaboration-error` | A Lean error other than an unsolved goal or a resource limit: a failed tactic, a missing import, an unknown name | Read the error |
| `unsolved-goal` | A tactic block left goals open, or a `--goals` run found open goals | Rerun with `--goals` |
| `resource-limit` | Heartbeats or recursion depth ran out; `resource` names which | Confirm the method and profile first: a proof run on another method or of a false property also exhausts limits. Then split the proof or supply the missing fact |
| `replay-or-audit-rejected` | Kernel replay or the axiom audit rejected the proof | Remove `sorry` and extra axioms |
| `refutation` | The theorem verified, and it states `Not (contract.Holds ...)` | Report that the contract is refuted; `verified.json` certifies the refutation |
| `unclassified` | Anything else, such as a missing tool | Read `message` |

An unsolved goal or a failed tactic means the proof is incomplete or the property is false, and
the report does not say which. Only a verified theorem of the `refutation` form proves that the
code violates a contract.

## Goals, traces and JSON

| `verify` option | Output |
| --- | --- |
| `--goals` | `Invalid: N goals remain in <proof>.`, then each goal in source order as `file:line:column: sorry`, `failing tactic` or `unsolved`, with its hypotheses and target |
| `--trace` | Under `Trace (N entries):`, each step the proof takes, at its place in the proof file |
| `--format json` | One JSON report on stdout: `result` (`verified` or `failed`), `stage`, `rerun` and `failures`, one record per Lean error with its `source`, the `tactic` that stopped, the `cil` instruction, the `state` reached and expected, the `missing` fact and `suggestions` |

Write `sorry` where the next step is unclear and read its goal with `--goals`, under which a
`sorry` anywhere in the proof file is an open goal, whichever theorem is selected. Field details
are in
[goals](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#goals-of-an-unfinished-proof),
[JSON output](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#machine-readable-verify-output)
and [traces](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#trace-the-proofs-steps).

## Messages

| Message | Meaning | Next action |
| --- | --- | --- |
| `No method matches selector`, `Ambiguous method selector ... Candidates:` | The selector names no method, or several | Copy the signature from `leancil list` or a candidate, with its parameter list |
| `Unsupported assembly identity, target framework or build configuration` | The assembly is not a Release, IL-only .NET 10 build, or `--assembly` names another assembly | Build with `-c Release` for `net10.0` |
| `Unsupported static initialisation: T has a static constructor` | The method's type has a static constructor | Ask the user whether every caller runs it first; only then pass `--assume-initialized T` and report it as an assumption |
| `Unsupported ...` or `Recursive managed dependency` at `metadata and CIL validation` | The named instruction, call, type or signature is outside the supported subset | Report it. `leancil blockers` lists every blocker of a list of methods ([blockers](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#report-extraction-blockers)) |
| `Stale or mismatched verification artifact: assembly has changed since extraction.` | The DLL was rebuilt after `extract` | Run `extract` again. `verify` does so itself and prints `Re-extracted <directory>: the assembly changed since extraction.` |
| `Stale or mismatched verification artifact: extractor has changed since extraction.` | The tool was updated after `extract` | Run `extract` again. `verify` does so itself |
| `Stale or mismatched verification artifact: ... differs from regenerated CIL.` | `Extracted.lean` was edited or belongs to another build | Run `extract` again; never edit generated files |
| `Proof file not found:` | `--proof` or the saved setting names no file | Pass `--proof`; after moving files pass `--proof-root` again too |
| `... imports X, a LeanCIL repository module that the tool does not ship.` | The proof imports one of LeanCIL's example or test modules | Import `CIL` modules; `CIL.Safety.Memory.empty` is the empty caller memory |
| `Unapproved proof axioms:` | The selected theorem depends on the listed axioms | Remove them; `sorryAx` is a `sorry` or `admit` |
| `Required command not found:` | .NET, Lean or Lake is not on `PATH` | Install it |
| `Consumer package must depend on leancil.`, `Consumer leancil sources differ from the verifier's bundled framework:`, `Consumer and verifier Lean toolchains differ.`, `Consumer dependencies must be git packages pinned by a full revision in lake-manifest.json.` | The `--proof-root` package breaks a [package setup](bridge-model-proof.md#package-setup) rule | Pin the `[[require]]` block and the toolchain `leancil --version` prints, pin every dependency by Git revision, then run `lake update` |
| `Extracted.lean is reserved for the selected extraction artifact`, `Batch outputs must lie outside the consumer sources` | A generated `Extracted.lean` or a batch `output` is inside the proof package | Move extraction outputs outside the package, for example under `artifacts/` |
| `--check accepts compilation requests, not rejection expectations.`, `--check cannot evaluate mutation rejection expectations.` | A selected request or variant expects `rejected` under `--check` | Drop `--check`, or select requests that expect success |
| `No gates match the requested selection.`, `No gates depend on the changed paths.` | `--method`, `--profile` or `--changed` selected nothing | Widen the selection |

## Tactic messages

| Lean error | Meaning | Next action |
| --- | --- | --- |
| `cannot step pc N (op) at memory M` | A loop tactic lacks a fact for that instruction; the message's last line, `Supply ...`, names it | Prove that fact and pass it in the tactic's fact list |
| `pc N is a call (op); cross it with cil_loop_call` | `cil_loop_steps` or `cil_loop_finish` reached a call | Use `cil_loop_advance`, then `cil_loop_call holds input at site` |
| `target state not matched at pc N` | The path reached the target pc with another frame, stack or memory | State the fact or the target in the reached form the message shows |
| A stopped walk with `if c then target else next` as the pc, or `cil_lookup: undecided branch` | No fact decides the branch condition | Pass `c = 0` or its negation, or `split` and resume in each case |
| `Snapshot stepping took no step; justify the local premises` | The snapshot form found no home, write access or `WellFormed` fact for the first local store | Put those premises in context ([snapshot walks](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots)) |
| `cil_body: rfl could not prove the method-body binding` | The expected body differs from the extracted one; the message shows the first difference | Update the expected body, or bind by signature with `bind_method` |
| `no extracted method has signature` | A `bind_method` or `bind_callee` signature is not in this extraction; the message lists the extracted methods with that name | Copy a listed signature |
| `Case tag ... not found` | A `case` names no open goal; the message lists the open tags | Use a listed tag |
| ``Tactic `rfl` failed`` on an `invoke` equality | The stated result is not what the method computes for those arguments, or the fuel literal is smaller than the number of steps the run takes | Compare the statement with the C#; raise the fuel |

`cil_checked_steps`, `cil_contract_steps` and `cil_raise_steps` stop at the first instruction
they cannot step and leave its goal, and fail when they cannot take a first step. Rerun with
`--format json` and read `failures[].missing` for the kind of fact that step lacks
([stepping reference](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#supply-step-facts)).
