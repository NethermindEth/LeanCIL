# Validation

<!-- audience: maintainers -->

This page lists the verification suites, says which to run for a change and how to compare proof
cost with a base. Read it before changing LeanCIL itself; the linked pages hold the detail.

## Running suites

Run the smallest suite covering the changed behavior, then the checks required by `AGENTS.md`.

```sh
dotnet run --file scripts/Test.cs -- --suite core
dotnet run --file scripts/Test.cs -- --suite evidence
dotnet run --file scripts/Test.cs -- --suite loops
dotnet run --file scripts/Test.cs -- --suite outlines-objects
```

- Omit `--suite` to run everything; the [suite table](#suites) lists each name.
- A suite builds its own prerequisites, checks every Lean proof fresh and writes
  `artifacts/test-results-<suite>.json`; a full run writes `artifacts/test-results.json`.
- Suites build and mutate `artifacts/`, so run concurrent suites in separate checkouts.
- In CI one job builds the extractor and example assembly with `--build-tools`, and suite jobs set
  `LEANCIL_PREBUILT_TOOLS=true` to use them.
- `lake build` builds only `CIL`. A change under `CIL/` requires building every library target in
  `lakefile.toml` before pushing.
- A C# change requires analyzer validation, including changed file-based tests.
- Any `sorryAx`, unexpected diagnostic or failed proof is a failure.

| Changed area | Relevant suites or checks |
| --- | --- |
| Extraction certificates and metadata | `evidence`, plus the affected opcode or runtime-helper suite |
| Interface and managed dispatch, constant flag calls, stack allocation, compiler coverage | `dispatch` |
| Arithmetic and representations | `integer`, `narrow`, `primitive`, `checked`, `conversions`, `native` |
| Memory and references | `unsafe`, `blocks`, `copy`, `arguments`, `layout` |
| Calls and contracts | `callers`, `contracts`, `outcomes`, `imports` |
| Referenced assemblies and pins | `assemblies`, `evidence`, `dispatch`, `exportstyped` |
| Class-instance proofs over linked objects | `pool`, `evidence` |
| Loop contracts, runtime comparisons and control-flow validation | `loops` |
| Generated proof outlines | `outlines-control`, `outlines-objects`, `outlines-buffers`, `structoutlines`, `receiveroutlines`, `wordreader`, `savedwordreader` |
| Shared stepping, return and contract tactics | All loop and outline suites above, examples, and `Tests.Automation`, `Tests.StoreFacts`, `Tests.MethodContract`, `Tests.CodeAt`; compare [proof cost](#proof-cost) with the base |
| CLI, artifact identity and theorem selection | `core`, `cli`, `failures`, `workspace`, `audit` |
| Admission reports and self-admission of the extractor | `blockers`; see [self-admission](COMPILER-COVERAGE.md#self-admission) |
| Exported interfaces and implementation checks | The affected `exports` partition in the [suite table](#suites) |
| Documentation, its Lean snippets, cited names and documented command output | `docs`, plus `scripts/CheckDocReferences.cs`; see [documentation checks](CI.md#documentation-checks) |

## Suites

This table lists every name `--suite` accepts, in the order a full run executes them. The names
come from [VerificationSuites.cs](../scripts/VerificationSuites.cs) and
[ExportVerificationSuites.cs](../scripts/ExportVerificationSuites.cs);
`scripts/CheckDocReferences.cs` fails when this table and those registries disagree.

| Suite | Checks |
| --- | --- |
| `core` | the runner's own checks: example proofs and their rejections, the shared Lean test libraries including the public proof surface, binding catalogs and certified integer binding families, gate plans and required results, method selectors, caches, batched extraction and joint kernel replay |
| `templates` | shared profile templates, exact instruction equations and checked bindings |
| `workspace` | per-method editor extractions, watch refresh and ordinary fresh certification |
| `imports` | implementation-bound contract imports and conditional caller verification |
| `exceptionlint` | diagnostic XML exception drift without proof claims |
| `contracts` | universal checked contracts, caller memory preservation and incorrect implementations |
| `evidence` | independent extraction certificates and malformed evidence rejection |
| `dispatch` | constrained and managed dispatch, constant calls, stack allocation and pinned compiler coverage |
| `loops` | cyclic control-flow validation, universal termination, negative contracts and class/word-array composition |
| `outlines-control` | generated outlines for control flow, arithmetic and value types, completed proofs and rejection checks |
| `outlines-objects` | generated outlines for objects and reference arrays, completed proofs and rejection checks |
| `outlines-buffers` | generated outlines for word arrays, spans and array-valued fields, completed proofs and rejection checks |
| `structoutlines` | generated struct outlines, repeated field stores, nested values and narrow fields |
| `receiveroutlines` | struct receiver loop outlines with completed invariants and mutation rejection |
| `wordreader` | class cursor reads and skip/peek consumption, array separation and semantic mutation rejection |
| `savedwordreader` | saved numeric locals across class helper calls, 64-bit results, frame boundaries and semantic mutation rejection |
| `generics` | C# and F# generic method specialization, provenance and rejection proofs |
| `blocks` | block memory, alignment prefixes, runtime comparisons and safety faults |
| `unsafe` | layout-based Unsafe sizes, reference offsets and metadata validation |
| `math` | integer Math helpers, BigMul, runtime faults and universal minimum |
| `intrinsics` | exact SIMD call signatures, byte shuffles, AES rounds, unspecified lanes, opaque locals and profile rejection |
| `divrem` | X86Base.X64.DivRem and Math.DivRem through ValueTuple fields, divide faults and layout rejection |
| `fsharp` | F# arithmetic, branches, calls, references and struct construction |
| `constructors` | struct construction, initialized temporaries and constructor faults |
| `instance` | struct instance calls, managed this and constructor calls |
| `nested` | nested struct layout, snapshots, copies and metadata validation |
| `enums` | integer enum storage, flags, runtime comparisons and metadata validation |
| `cli` | CLI proof verification and incorrect implementation rejection |
| `failures` | failure reports that classify and locate each failed obligation |
| `integer` | integer opcode encodings, boundary cases and universal negation proofs |
| `narrow` | narrow integer conversions, storage, method boundaries and rejection proofs |
| `primitive` | primitive memory, switch, sizeof and rejection proofs |
| `division` | integer division and remainder runtime comparisons and proofs |
| `checked` | checked integer arithmetic runtime comparisons and proofs |
| `conversions` | checked integer conversions runtime comparisons and proofs |
| `layout` | sequential struct layout, runtime offsets and metadata validation |
| `bits` | portable bit operations, endian reversal and runtime signature validation |
| `copy` | typed copies, aliases, byte snapshots and rejection proofs |
| `arguments` | argument assignment, addressing, aliases and lifetime proofs |
| `native` | native integer storage, arithmetic and runtime comparisons |
| `identity` | methods bound by signature or call shape that survive renumbering and renaming |
| `labels` | loop-head and call-site labels that survive inserted statements |
| `names` | PDB local names and source locations that never change extraction |
| `symbols` | consumer proofs naming PDB locals through helper modules, bound only where imported |
| `callers` | caller proofs that survive reimplemented helpers through their contracts |
| `construction` | caller proofs that survive reimplemented constructors through their contracts |
| `outcomes` | outcome contracts that name exactly when each exception is thrown |
| `scaling` | compositional certificate for a six-method call graph and its consumer replay, and the header and per-method struct layout checks at a per-layout cost that does not grow with the table |
| `excluded` | hundreds of excluded and live sites at the default heartbeat budget |
| `lookups` | lookup equations of extracted methods, hand-written bodies and templates, and the scalar certificate of array element addresses, loaded and addressed integer locals and native-int locals consumed by calli, and the closed argument storage of those native-int locals, at a per-instruction cost that does not grow with the method, embeddings of bodies with many calls at a per-call kernel cost that does not grow with the calls, and type identity equality at a cost that does not grow with the name |
| `gates` | manifest project builds, extraction, named profiles, per-variant and templated proofs, witness refutations, kernel statement comparison, binding catalogs, planned groups, changed-source selection and mutation expectations |
| `stepping` | full scalar, checked-memory, running-sum, locals, contract, loop, loop-facts, outcome, lemma, depth and hypotheses bodies with per-instruction heartbeat, proof-size and latency budgets |
| `assemblies` | bodies, layouts and generic instantiations from pinned referenced assemblies, attribution and substitution rejection, and the strict binding library and audit |
| `pool` | object pool reuse, creation, exhaustion, null-pool and free-list search proofs and the mutations they reject |
| `blockers` | admission reports with deduplicated blockers, call chains, profile-excluded branches and self-admission |
| `audit` | theorem audits of replayed oleans that proof elaborators, initializers and substituted artifacts cannot forge |
| `docs` | documentation Lean snippets, cited library names and documented commands against the library and tool |
| `exports` | contract production, restrictions and caller reuse |
| `exportsaudit` | post-callback export integrity |
| `exportsprotected` | protected static export and separately compiled derived caller |
| `exportsresolution` | full module resolution |
| `exportsfullcomposition` | transferred composition statement integrity |
| `exportsfullconsumer` | fresh and repeated full consumer verification |
| `exportsfullordinary` | ordinary full caller verification |
| `exportsfullpair` | two imported slots from one bundle |
| `exportsfullchecks` | full input and caller rejection |
| `exportsfulltheorems` | producer theorem kind and statement rejection |
| `exportsmutationordinary` | ordinary caller artifact mutation |
| `exportsmutationconsumer` | consumer caller artifact mutation |
| `exportsmutationsource` | consumer caller source mutation |
| `exportsmutationshadow` | original caller root shadow mutation |
| `exportsstatics` | independent modular static exports |
| `exportsfullstatics` | independent full composition of shared and changed static tables |
| `exportstransitive` | independent transitive contract imports |
| `exportstransitiveoutcomes` | independent deep transitive named outcome contracts |
| `exportsdiscovery` | contract discovery with real export bootstrap |
| `exportstyped` | independent typed generic and layout imports |
| `exportsderived` | derived public contracts through DLL export and import |
| `exportsinitialized` | scoped initialization assumptions in exported and imported contracts |
| `exportsprofiles` | one contract family across independently checked profile extractions |

The [export page](VALIDATION-EXPORTS.md#export-suite-selection) lists the cases of each `exports`
partition.

## Proof cost

For a change to shared tactics or the library, also compare what each proof costs with the base.
Measure both checkouts on one machine:

```sh
git worktree add --detach ../base "$(git merge-base origin/main HEAD)"
dotnet run --file scripts/ProofCost.cs -- measure --tree ../base --libraries --output artifacts/cost/base.json
dotnet run --file scripts/ProofCost.cs -- measure --tree . --libraries --output artifacts/cost/head.json
dotnet run --file scripts/ProofCost.cs -- compare --base artifacts/cost/base.json \
  --head artifacts/cost/head.json --accepted scripts/proof-cost-accepted.json
```

`measure` runs from the head checkout for both trees, so the base needs no copy of the tool. Each
tree needs its compiled library: pass `--library` with a certified library, or build every `CIL`
module in the tree first, since `lake build CIL` leaves modules outside the aggregate unbuilt.

| `measure` option | Measures |
| --- | --- |
| `--libraries` | every test library |
| `--module Tests.Automation` | one module and the checkout modules it imports |
| `--artifacts artifacts` | the proofs a suite verified in that tree, after running the suite there |

A suite binds the sources of its checkout, so keep the base checkout outside the head checkout and
edit neither while its suite runs. Measurement stops on import errors before elaborating
diagnostic assertions: a module with missing imports produces no cost report and no compiled
output. `compare` exits nonzero on a regression and prints the table that CI puts in the job
summary; [proof cost in CI](CI.md#proof-cost) defines the measures, the thresholds and how to
accept an increase.

### Stepping scaling

```sh
dotnet run --file scripts/Test.cs -- --suite stepping
```

The `stepping` suite generates explicit scalar, checked-memory, accumulate, locals, contract,
loop, loop-facts, outcome, lemma, depth and hypotheses bodies and proves each end to end. The
scalar, memory, accumulate and locals bodies have 16, 64 and 256 instructions, and the accumulate
body also 1,024. The memory bodies repeat an idempotent checked store and reload, so the
operation facts stay constant as the instruction count grows. The accumulate, contract, loop,
loop-facts, outcome and lemma bodies keep a running sum on the stack, so the symbolic value a step
reads grows with the program counter. The contract body is proved by `cil_contract_steps`, the
loop body by `cil_loop_steps` along a path, the loop-facts body by the same with a case fact in
the context that every instruction reads, the outcome body by `cil_loop_outcome_advance`, and the
lemma body by `cil_checked_steps` with a universe-polymorphic lemma among its facts. The locals
bodies store a
reference into each of eight locals of a literal frame per cycle. The depth bodies push 8, 32 and
128 values and add them all. The hypotheses body is a 62-instruction accumulate body proved with 16,
64 and 256 equations in scope. The suite uses the proof-cost measuring frontend, with three
sequential proof compilations and a header-only baseline per scalar, memory, accumulate and locals
body up to 256 instructions, and one compilation for every other body.

- For each successive size, frontend and kernel heartbeats per instruction may grow by at most
  1.35 times. For the bodies with three compilations, compiled proof bytes per instruction may
  also grow by at most 1.35 times, and median frontend milliseconds by at most twice.
- The heartbeats a hypothesis adds may not grow by more than 1.35 times from the step between
  16 and 64 hypotheses to the step between 64 and 256, which a step that compares each hypothesis
  with every other would exceed.
- Heartbeats and bytes must repeat exactly across the three runs.
- Frontend heartbeats include the initial kernel check; the kernel columns measure a separate
  recheck. Compiled proof bytes subtract the same module containing only the body and its lookup
  equations.
- `artifacts/SteppingScaling/results.json` records revisions, toolchain, machine, cache
  assumptions, raw process-time samples and per-instruction costs.

Wall times vary with machine load; use isolated sequential runs for latency comparisons. These
measurements cover checked stepping only, and exclude extraction, editor feedback and certificate
completion.

## Coverage pages

Positive fixtures compare compiled .NET behavior with checked model execution or establish
universal theorems. Negative fixtures independently tamper with translation evidence, violate
memory premises, or change implementations while retaining their specifications.

- [Coverage reference](VALIDATION-COVERAGE.md): extraction, runtime comparisons, artifact binding
  and preparation infrastructure.
- [Proof automation regressions](VALIDATION-PROOFS.md): shared tactics, memory facts and
  composition.
- [Export and consumer checks](VALIDATION-EXPORTS.md): interface pins, audit and consumer packages.
- [CI operation](CI.md): job selection, prepared libraries and artifacts.
- [Pinned compiler corpus and runtime inventory](COMPILER-COVERAGE.md): compiler-sensitive
  recognizers, visible changes to admitted runtime-call definitions, and admission of
  LeanCIL's own assembly.

When adding a case, extend the existing fixture batch for related cases. When measuring, report
producer work, proof compilation and kernel replay separately; moving work between jobs or caches
does not itself demonstrate a reduction in total verification work.
