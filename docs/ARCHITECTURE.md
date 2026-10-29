# Architecture and proof APIs

| Layer | Public modules | Purpose |
| --- | --- | --- |
| Values and instructions | `CIL.Types`, `CIL.Instructions`, `CIL.Layout` | Bit vectors, references, byte snapshots, validated aggregate layouts |
| Execution | `CIL.Semantics`, `CIL.ExecutionLemmas` | Shared arithmetic, intrinsic and instruction evaluation |
| Memory safety | `CIL.Safety.Memory`, `CIL.Safety.Execution` | Allocation-aware interpreter, access checks, initialization, permissions and lifetime |
| Proofs | `CIL.Safety.ExecutionTrace`, `CIL.Safety.ExecutionInvariants`, `CIL.Safety.Certificate`, `CIL.Safety.BufferContents`, `CIL.Verification` | Shared execution traces and instruction contracts, invariants, invocation certificates, typed buffer contents and total-correctness specifications |
| Automation | `CIL.Safety.SymbolicExecution`, `CIL.Safety.LoopAutomation`, `CIL.Safety.LoopContract`, `CIL.Safety.LoopOutcome`, `CIL.SymbolicExecution` | Checked instruction composition, loop segments, loop calls through method and outcome contracts, definitional reduction and transactional proved summaries |
| Runtime features | `CIL.Features`, `CIL.SIMD.*`, `CIL.ProfileEquivalence` | Fixed capability profiles, supported SIMD semantics, profile equivalence through `ProfileAgreement.of_flags` |
| Extraction | `Extractor/` | Metadata validation, managed-call reachability, CIL translation and Lean generation |
| Verification | `leancil verify` | Source-keyed library cache, explicit fresh builds, kernel replay, theorem audit and assembly/source identity binding |

`CIL.Safety.invoke` is the sole whole-method execution model. Functional results and memory-safety claims use its checked frames, allocation-aware memory and located faults. Shared value evaluation lives in `CIL.Semantics`; it does not provide a separate method runner.

## Writing compact checked proofs

Return arity and fully specified results share one checked dispatcher proof. The existing
step, run and invocation theorems retain their statements while avoiding duplicate case analysis
during compilation and kernel replay.

Allocation-renaming proofs share dispatcher reasoning across ordinary instructions and
reference-aware arithmetic and branches, avoiding separate proofs of overlapping cases.

Import `CIL.Safety.SymbolicExecution` and use `cil_checked_steps` to compose
checked instruction steps. It first tries definitional equality when no facts
are supplied, then uses local instruction equations and simplification as needed.
For symbolic branches or memory operations, supply the proved conditions with
`cil_checked_steps [facts]`; local facts are normalised with the goal, so a
store fact may state its value in source form. Matching memory-dispatch facts preserve
their abstract results before per-shape evaluation, avoiding unnecessary byte expansion.
Loop segments use
`CIL.Safety.LoopAutomation` and still require an invariant and a decreasing measure.
Contract stepping also handles signed and unsigned widening in either argument order;
the [consumer stepping regressions](PROOFS-STEPPING.md#consumer-stepping-regressions)
cover all eight wrapper combinations under a fixed heartbeat budget.

`Segment` contracts compose checked prefixes through exact intermediate states and fuel costs.
`cil_segment` proves an exact-state contract from `CodeAt` placements and checked step facts.
A local frame rule preserves untouched numeric snapshots from actual write effects and
separate writable homes; placement alone never grants memory preservation.
See [composable segments](PROOFS.md) and [their acceptance tests](../Tests/Segment.lean).

`CodeAt` facts let the tactics resolve instructions within a known code segment without
expanding the whole method. `cil_checked_steps (snapshots := snapshots) [facts]` also
tracks numeric local stores and updated snapshots, including mixed Vector128, Vector256
and int32 locals. Snapshot facts do not supply write authority or justify a value of the wrong
local kind. Supported forwarder bodies can inherit a
callee's proved contract, and embedding proofs can ignore trailing unread byref,
pointer or span locals. Allocation refinement also relates numeric and interspersed dead
locals in ordinary frames, including inserted locals with valid initializers: retained
initializers, scalar results and caller-memory prefixes transfer,
as do named exceptions, while fresh allocation identities may differ. Import
`CIL.Safety.AllocationRefinement` explicitly for this API; the `CIL` umbrella does not load
its proof dependencies. See
[dead-local refinement](PROOFS-BINDING.md#bodies-modulo-dead-code) for its frame restrictions.
Contract refinement derives a public interface from a stronger proved
contract; that interface can be exported and imported by callers.
For unused numeric locals, retain the extracted declarations and local indices in
the expected body and use ordinary embedding. This preserves later allocation
identities; [the retained-local example](../Tests/RetainedNumericLocals.lean) covers
interspersed numeric homes and nested allocating calls. Numeric-local deletion
still requires a separate allocation-renaming simulation.

`cil_embed [facts]` binds a shared body template to an extraction using proved feature
flag and callee equalities. Local definitions also work without a fact list; relevant
flags left unconstrained are rejected, and the kernel checks the complete instruction map.

`leancil templates shared scalar-extraction sse42-extraction v3-extraction` generates
the shared bodies from compiled CIL, including per-instruction equations and a binding
module for each input. Prove the template once and use the generated bindings for the
selected profiles; see [generated profile templates](PROOFS-BINDING.md#generated-profile-templates)
for the supported domain and checking workflow.

Public and protected static methods can publish contracts for separately compiled callers,
including a derived class calling a protected base method. Calls remain statically resolved;
this does not add virtual dispatch support.

Exported contracts can carry an explicit type-initialization premise for libraries
with static constructors, including types containing `static readonly` struct fields.
The sidecar binds each premise to an assembly, type and profile; importing callers
retain it in their generated artifacts and verification reports. This is a runtime
assumption, not a proof that the CLR initializer ran. Constructor-initialized field
values remain unsupported for export. See [contract interfaces](CONTRACT-INTERFACES.md).

`leancil verify --force-full-verify` independently checks supported imported
libraries and their reachable contract dependencies against separately pinned
implementation DLLs, interfaces and source bundles. Conditional exports and shared
dependencies are checked in dependency order, including when ordinary verification
receipts are warm. Composition preserves normal returns and named exceptional
outcomes. Libraries may read immutable RVA static tables: checked composition preserves
their assembly-scoped identities and shared-table descriptors. Static-world
requirements remain explicit contract preconditions; static-constructor and
static-value assumptions are not supported in this mode. See
[independent verification](FULL_VERIFICATION.md) for the trust boundary and
required producer evidence.
Full verification checks caller and imported proofs again even when ordinary
verification has already cached successful results.
Transferred proofs share repeated expression nodes in a compact data table; reconstruction
still kernel-checks every declaration and independently replays the compiled result.
An `export-contracts` manifest can list several profile artifacts for one method and one
family theorem. Each extraction is checked independently, with kernel-checked flag agreement
and exact equality to the reprofiled reference program. See the
[profile-family manifest example](PROOFS.md) for the same-flag transport requirements.
Compatible exports share their source snapshot and reusable compilation work; each export
retains its own theorem, contract closure, replay and publication checks.

The [proof-writing guide](PROOFS.md) includes a complete example, reusable
contracts for framework proofs, and advice on avoiding repeated interpreter
expansion. See [proof automation validation](VALIDATION-PROOFS.md#proof-automation)
for the regression coverage and commands to run it.
