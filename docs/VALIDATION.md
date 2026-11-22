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

The blockers suite checks dead instructions in methods admitted from the extractor assembly under
the scalar profile. Its hole corpus baseline pins argument indices requiring homes only at dead
instructions, dead prefix positions and opcodes other than `unaligned.`, and the count of refused
methods skipped. The per-method lists are written to `artifacts/HoleCorpus/methods.json`; admission
results are reused from the self-admission check.

`dotnet run --file Tests/SelfAdmission.cs -- --lean-check` also extracts each admitted method alone and
elaborates it against the checkout's `CIL`, printing each method Lean refuses and failing when there is
one, which finds an admission the extractor grants and the Lean checks refuse. It is run by hand when a
change can move verdicts between the two, never by a suite: over the roughly 3750 admitted methods it
takes about 2.7 hours of CPU time.

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
| `core` | the runner's own checks: example proofs and their rejections, the shared Lean test libraries including the public proof surface, replay diagnostics, return narrowing and metadata restrictions, value opcode decoding, the extractor's table of decoded opcodes and decoding bodies with unreachable instructions and checking their frames and links, methods decoded from body bytes and defined by evaluating the decoder, Add extracted with no method literal, object array steps, embedding retention and profiles, full transfer, SHA-1 and assembly and pin index scaling, binding catalogs and certified integer binding families, gate plans and required results, method selectors, caches, support audit reuse bound to extraction identity, batched extraction and joint kernel replay |
| `templates` | shared profile templates, exact instruction equations and checked bindings |
| `workspace` | per-method editor extractions, watch refresh and ordinary fresh certification |
| `imports` | implementation-bound contract imports and conditional caller verification |
| `closures` | summaries at relocated indices, contract reuse for identical executable bodies, and rejection of decoded links to different method tokens |
| `exceptionlint` | diagnostic XML exception drift without proof claims |
| `contracts` | universal checked contracts, caller memory preservation and incorrect implementations |
| `evidence` | independent extraction certificates, malformed evidence rejection, the metadata decoder's method names against Cecil's and framework argument guards |
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
| `intrinsics` | exact SIMD call signatures, 128-, 256- and 512-bit equality contracts with swapped-word and repeated-operand counterexamples, 32-byte half swaps over arbitrary bytes at eight source/destination placements with a repeated-load counterexample, byte shuffles, AES rounds, unspecified lanes, opaque locals, profile rejection and the library of generated runtime comparisons |
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
| `primitive` | primitive memory, switch, sizeof and rejection proofs, and strings as opaque references |
| `division` | integer division and remainder runtime comparisons and proofs |
| `checked` | checked integer arithmetic runtime comparisons and proofs |
| `conversions` | checked integer conversions runtime comparisons and proofs |
| `layout` | sequential struct layout, runtime offsets and metadata validation |
| `bits` | portable bit operations, endian reversal and runtime signature validation |
| `copy` | typed copies, aliases, byte snapshots and rejection proofs |
| `arguments` | argument assignment, addressing, aliases and lifetime proofs |
| `native` | native integer storage, arithmetic and runtime comparisons |
| `identity` | methods bound by signature or call shape that survive renumbering and renaming, and typed identity display |
| `labels` | loop-head and call-site labels that survive inserted statements |
| `names` | PDB local names and source locations that never change extraction |
| `symbols` | consumer proofs naming PDB locals through helper modules, bound only where imported |
| `callers` | caller proofs that survive reimplemented helpers through their contracts |
| `construction` | caller proofs that survive reimplemented constructors through their contracts |
| `outcomes` | outcome contracts that name exactly when each exception is thrown |
| `scaling` | compositional certificate for a six-method call graph and its consumer replay, declared signature checks at flat per-method cost over 1, 4 and 16 parameters, header and per-method struct layout checks at a per-layout cost that does not grow with the table, and the generic owner index library |
| `excluded` | hundreds of excluded and live sites at the default heartbeat budget |
| `lookups` | lookup equations of extracted methods, hand-written bodies and templates, and the scalar certificate of array element addresses, loaded and addressed integer locals and native-int locals consumed by calli, the closed argument storage of those native-int locals, and the feature certificate of local loads, stores and addresses, at a per-instruction cost that does not grow with the method or with locals holding no known word and grows linearly with the known facts, embeddings of bodies with many calls at a per-call kernel cost that does not grow with the calls, type identity equality at a cost that does not grow with the name, the method name clause of the call operand check and the encoding of a metadata name at a per-byte cost that does not grow with the name, the bytes of a name stored as its bytes at a per-byte cost that does not grow with the name and, with the name's definition, below the cost of the bytes of its literal, and one native method table step and one load of its first entry at a kernel cost that does not grow with the table's entries; the managed-call check of a body with many call sites at a per-site cost that does not grow with the call sites; the call check and the evidence theorem of a body with no call at a per-statement and a total cost that do not grow with the body; the proof that 8, 32 and 128 evidence records decode to their methods at a per-record cost that does not grow with the records; the closure of a method in a program at a cost per unit of methods times program length plus link callees that does not grow with the methods, the callees or the program; the argument facts of `cil_resolution_facts` and the reads through them at a per-argument cost that does not grow with the parameters, and its static site facts and the reads through them at a per-site cost that does not grow with the sites; the program's static identity check at a per-site cost that grows less than 1.35 times from 8 to 32 to 128 sites; the array element shape facts of `cil_resolution_facts` and the reads through them at a per-element-type cost that does not grow with the layouts or the sites naming each type; a runtime model lookup at a kernel cost that does not grow with the model table, and the runtime model agreement check at a per-site cost that does not grow with the call sites; the shape facts of `cil_field_shape` and the reads through them at a per-field cost that grows less than 1.35 times from 8 to 32 to 128 fields in one struct and from 8 to 32 to 128 to 512 fields in a struct each, and the facts of `cil_value_shape` and their reads at a per-type cost that grows less than 1.35 times from 8 to 32 to 128 to 512 struct types; locating a class field on an instance, and rejecting a field whose owner is outside the instance's lineage, at a per-base cost that grows less than 1.35 times from 2 to 8 to 32 bases; the kernel check of one body at a cost independent of the methods and metadata rows of its extraction, and at a per-instruction cost that does not grow with the string tokens of the body; the kernel's selection of a calli body at a cost linear in the length of the pointer's owner; raw value opcode decoding and the method decoded from a raw body at a per-instruction kernel cost that does not grow with the body, and the method `cil_decoded_method` defines from that body at a per-instruction cost that does not grow with the body; and the certificate index, feature getter, layout accumulation and projection, and extraction home index libraries |
| `gates` | manifest project builds, extraction, named profiles, per-variant and templated proofs, witness refutations, kernel statement comparison, binding catalogs, planned groups, changed-source selection and mutation expectations |
| `stepping` | full scalar, checked-memory, reference-offset, native-table-offset, running-sum, locals, contract, loop, loop-facts, outcome, lemma, depth, hypotheses, snapshot, faulting, arguments, homes, array-allocation, calls, table-calls, class-field-load, statics, construction, object-constructor and array-element bodies with per-instruction heartbeat and proof-size budgets and a per-hypothesis heartbeat limit |
| `assemblies` | bodies, layouts and generic instantiations from pinned referenced assemblies, attribution and substitution rejection, the strict binding library and audit, and the checked-in strict binding fixture module |
| `pool` | object pool reuse, creation, exhaustion, null-pool and free-list search proofs and the mutations they reject |
| `blockers` | admission reports with deduplicated blockers, call chains, profile-excluded branches, runtime-async refusal, self-admission, the admitted hole corpus and the self-admitted, example and fixture methods defined from their decoder |
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

The `lookups` closed-argument row checks primitive storage at 1, 4 and 16 parameters with
8, 32 and 128 unrelated layouts. It bounds the cost per parameter and rejects growth with
unrelated layouts. The row accepts `--closed-arguments-only` for isolated measurement.

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

The `stepping` suite generates explicit scalar, checked-memory, reference, table, accumulate,
locals, contract, loop, loop-facts, outcome, lemma, depth, hypotheses, snapshot, faulting,
arguments, homes, allocation, calls, table-calls, objects, statics, constructions,
object-constructor, elements, typed-elements and typed-steps bodies and proves each end to end.
The scalar, memory, reference, table, accumulate and locals bodies have 16, 64 and 256
instructions, and the accumulate body also 1,024. The memory bodies repeat an idempotent checked
store and reload, so the operation facts stay constant as the
instruction count grows. The reference and table bodies repeatedly `add` a symbolic int32 byte
offset to a reference argument or a native method table argument and pop the result, each step
reading one supplied fact that the offset succeeds. The accumulate, contract, loop, loop-facts,
outcome and lemma bodies keep a running sum on the stack, so the symbolic value a step reads grows
with the program counter. The contract body is proved by `cil_contract_steps`, the loop body by
`cil_loop_steps` along a path, the loop-facts body by the same with a case fact in the context that
every instruction reads, the outcome body by `cil_loop_outcome_advance`, and the lemma body by
`cil_checked_steps` with a universe-polymorphic lemma among its facts. The locals bodies store a
reference into each of eight locals of a literal frame per cycle. The depth bodies push 8, 32 and
128 values and add them all. The hypotheses bodies are 62-instruction accumulate, contract and loop
bodies proved with 16, 64 and 256 hypotheses in scope, a contract body with as many
instruction-lookup equations in scope, and the lookups of every instruction of the accumulate body
made by `cil_lookup` outside a stepping run, with 16 and 256 equations in scope. The faulting bodies
have 17 and 62 instructions and repeat `div`, `rem`, `add.ovf` and `conv.ovf.i4` over the arguments,
each advanced by a supplied fact that the operation does not fault. The snapshot bodies store into
eight numeric locals and then update one local per store from its remembered value, with 10, 20, 40
and 80 stores, proved by `cil_contract_steps (snapshots := ..)` with caller memory facts in the
context. Each store clears the facts it supersedes, so the hypotheses in scope stay level, while the
value a store writes grows with the number of updates to its local; the cost per instruction rises
slowly with the stores. The arguments bodies have 16, 64 and 256 instructions and add 8, 32 and 128
`int32` arguments of a declared signature, each read once, with the method's `cil_resolution_facts`
in scope. The homes bodies have 16, 64 and 256 instructions and read each of 8, 32 and 128 reference
parameters once from its home in a literal frame. The allocation bodies have 16, 64 and 256
instructions and allocate and pop an array of two class references per cycle, each `newarr`
resolving its element shape and reading one supplied allocation fact. The calls bodies have 16, 64
and 256 instructions and pass their argument through 14, 62 and 254 calls of a callee that returns
it, each call reading its target from a link fact that `cil_instruction_equations` states; the
table-calls bodies are the same bodies with their link table written out, as a template writes it.
The objects bodies have 16, 64 and 256 instructions and load and pop an `int64` field of their
object argument per cycle, each `ldfld` reading the field's `cil_field_shape` fact and two supplied
facts that locate and read its slot; `cil.requireFieldShapeFacts` fails the body if a step
evaluates the shape instead of reading the fact. The struct fields bodies have 16, 64 and 256
instructions and load and pop the `int64` field at byte 8 of the struct their reference argument
addresses, then store their `int64` argument there, per cycle; each `ldfld` and `stfld` reads the
field's `cil_field_shape` fact and supplied facts that locate the field and read or write it, and
the struct fields contract bodies step the same bodies under contract stepping. At each size, both workloads compare the checked theorem's heartbeats with the recorded
cost of the lowered body at `8cc33b38` on Lean 4.35.0. The instruction counts must match.
The intrinsic call workload compares repeated typed `Math.Max(long, long)` calls against the
same program at `9c53e7f5`. Both field and intrinsic call workloads allow 1.03 times the reference
frontend heartbeats and 1.08 times the reference kernel heartbeats. The statics bodies have 16, 64 and 256
instructions and load a static field and pop it per cycle, with one static site per load, so each
step resolves its pc among all the body's sites. The constructions bodies have 16, 64 and 256
instructions and construct and pop a class instance per cycle, each `newobj` reading its link and
one supplied allocation fact and entering a constructor that returns. The object-constructor
bodies have 16, 64 and 256 instructions and call the `System.Object` constructor on their object
argument per cycle, each call reading that its pc has no link and the runtime model its pc's
`cil_runtime_models` fact states. The intrinsic-calls bodies have 14, 62 and 254 instructions and
call `Math.Max` on their two `int64` arguments and pop the result per cycle, each call reading the
same two facts and then stepping as its scalar intrinsic. The instance bodies have 16, 64 and 256
instructions and make one receiver-checked instance call on their object argument per cycle into a
method that returns at once. The virtual bodies make 16 virtual calls on it through a dispatch
table of 1, 16 or 64 classes, the receiver's class last, each call reading one supplied runtime
type fact and looking the class up in the table. The elements bodies have 16,
64 and 256 instructions and per cycle load and pop an `int32` element of their array argument and
store their index argument into it, each access reading one supplied element fact. The
typed-elements bodies have 16, 58 and 254 instructions and per cycle do the same through `ldelem`
and `stelem` with an `int32` type operand, then copy one struct element of a second array onto
itself. Each typed access steps by the fact `step_ldelem_any_of_element`,
`step_stelem_any_of_write`, `step_ldelem_any_of_transfer` or `step_stelem_any_of_transfer`
derives from supplied element facts and the generated shape fact of the body. The typed-steps
bodies are the same bodies with one supplied step fact per access.
The addresses bodies have 11, 56 and 254 instructions and per cycle form and pop a writable and a
`readonly.` address of an `int32` element of their array argument, each `ldelema` stepped by the
fact `step_ldelema_of_element` derives from one supplied element fact and the generated shape
fact of the body. The address-steps bodies are the same bodies with one supplied step fact per
address.
The suite uses the proof-cost measuring frontend, with three sequential proof compilations and a
header-only baseline per scalar, memory, reference, table, accumulate, locals, calls and table-calls
body up to 256 instructions, and one compilation for every other body.

- For each successive size, frontend and kernel heartbeats per instruction may grow by at most
  1.35 times. The arguments and homes bodies read one of a list of arguments or home slots that
  grows with the body, so their heartbeats per instruction may grow at most by the ratio of the
  sizes, linearly in the number of arguments. The virtual body makes 16 virtual calls through a
  dispatch table whose size is the row's size, and each call looks its receiver's class up in that
  list, so its heartbeats per instruction may grow at most by the ratio of the table sizes. For
  the bodies with three compilations, compiled
  proof bytes per instruction may also grow by at most 1.35 times. Frontend milliseconds are
  recorded for comparison between runs.
- For the hypotheses bodies the sizes are the numbers of hypotheses: in the accumulate, contract
  and loop bodies half of them are equations headed by an operator and half by a local variable,
  in the lookup body each is an instruction lookup like those stepping makes,
  `([.ldc_i4 i] : List CIL.Instruction)[0]? = some (.ldc_i4 i)`, and in the direct lookups
  each is an equation headed by an operator. The heartbeats and frontend milliseconds counted are
  those of the proof less those of the same statement closed by `sorry`, so that elaborating the
  hypotheses does not count as stepping. The same ratio limit applies, except to the direct
  lookups, which read every hypothesis in scope once each. One more hypothesis in scope may add
  at most 100 heartbeats to an instruction, which costs about 120,000, or to a direct lookup,
  between the smallest and the largest size. A lookup that tries to unify with every equation
  hypothesis adds 600 to 1,950 and fails that limit, as does a direct lookup that builds an index
  of the hypotheses, which adds about 410; reading each hypothesis once adds about 25.
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
