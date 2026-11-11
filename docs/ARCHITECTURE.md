# Architecture and proof APIs

This page maps the layers of LeanCIL to the Lean modules and commands that implement them, and
lists the proof APIs with the page that documents each. Read it to find which module to import
or which page to open for a task.

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

`CIL.Safety.invoke` is the sole whole-method execution model. Functional results and
memory-safety claims use its checked frames, allocation-aware memory and located faults. Shared
value evaluation lives in `CIL.Semantics`; it does not provide a separate method runner.

## Writing compact checked proofs

The [proof-writing guide](PROOFS.md) has a complete example, reusable contracts for framework
proofs and advice on avoiding repeated interpreter expansion. The APIs are:

### Stepping

Import `CIL.Safety.SymbolicExecution` and use `cil_checked_steps` to compose checked instruction
steps. With no facts it first tries definitional equality, then uses local instruction equations
and simplification. For symbolic branches or memory operations, supply the proved conditions with
`cil_checked_steps [facts]`. Local facts are normalised with the goal, so a store fact may state
its value in source form, and a fact that matches a memory dispatch keeps its abstract result
instead of expanding bytes. Contract stepping handles signed and unsigned widening in either
argument order.

`CodeAt` facts let the tactics resolve instructions within a known code segment without expanding
the whole method. `cil_checked_steps (snapshots := snapshots) [facts]` also tracks numeric local
stores and updated snapshots, including mixed Vector128, Vector256 and int32 locals, and names
each store's memory and evidence. Snapshot facts do not supply write authority or justify a value
of the wrong local kind.

`Segment` contracts compose checked prefixes through exact intermediate states and fuel costs.
`cil_segment` proves an exact-state contract from `CodeAt` placements and checked step facts. A
local frame rule preserves untouched numeric snapshots from actual write effects and separate
writable homes; placement alone never grants memory preservation. See
[composable segments](PROOFS-STEPPING.md).

Loop segments use `CIL.Safety.LoopAutomation` and require an invariant and a decreasing measure.

### Reusing a proof across bodies and profiles

- A supported forwarder body inherits its callee's proved contract; see
  [forwarder composition](PROOFS-CONTRACTS.md#inherit-a-callees-contract-in-a-forwarder).
- Contract refinement derives a public interface from a stronger proved contract; that interface
  can be exported and imported by callers.
- `cil_embed [facts]` binds a shared body template to an extraction using proved feature flag and
  callee equalities. Local definitions also work without a fact list; relevant flags left
  unconstrained are rejected, and the kernel checks the complete instruction map.
- `leancil templates shared scalar-extraction sse42-extraction v3-extraction` generates the
  shared bodies from compiled CIL, including per-instruction equations and a binding module for
  each input. Prove the template once and use the generated bindings for the selected profiles;
  see [generated profile templates](PROOFS-BINDING.md#generated-profile-templates) for the
  supported domain and checking workflow.
- Embedding proofs can ignore trailing unread byref, pointer or span locals. For unused numeric
  locals, retain the extracted declarations and local indices in the expected body and use
  ordinary embedding. This preserves later allocation identities, including for interspersed
  numeric homes and nested allocating calls. Deleting a numeric local requires a separate
  allocation-renaming simulation.
- Allocation refinement relates numeric and interspersed dead locals in ordinary frames,
  including inserted locals with valid initializers: retained initializers, scalar results,
  caller-memory prefixes and named exceptions transfer, while fresh allocation identities may
  differ. Import
  `CIL.Safety.AllocationRefinement` explicitly; the `CIL` umbrella does not load its proof
  dependencies. See [dead-local refinement](PROOFS-BINDING.md#bodies-modulo-dead-code) for its
  frame restrictions.

### Publishing and importing contracts

Public and protected static methods can publish contracts for separately compiled callers,
including a derived class calling a protected base method. A call through a published contract is
statically resolved.

Exported contracts can carry an explicit type-initialization premise for libraries with static
constructors, including types containing `static readonly` struct fields. The sidecar binds each
premise to an assembly, type and profile; importing callers retain it in their generated
artifacts and verification reports. The premise is a runtime assumption; it does not prove that
the CLR initializer ran. Constructor-initialized field values are not supported for export. See
[contract interfaces](CONTRACT-INTERFACES.md).

An `export-contracts` manifest can list several profile artifacts for one method and one family
theorem. Each extraction is checked independently, with kernel-checked flag agreement and exact
equality to the reprofiled reference program. See the
[profile-family manifest example](PROOFS.md) for the same-flag transport requirements. Compatible
exports share their source snapshot and reusable compilation work; each export retains its own
theorem, contract closure, replay and publication checks.

`leancil verify --force-full-verify` independently checks supported imported libraries and their
reachable contract dependencies against separately pinned implementation DLLs, interfaces and
source bundles. Conditional exports and shared dependencies are checked in dependency order, and
caller and imported proofs are checked again even when ordinary verification has cached
successful results. Composition preserves normal returns and named exceptional outcomes.
Libraries may read immutable RVA static tables: checked composition preserves their
assembly-scoped identities and shared-table descriptors. Static-world requirements are explicit
contract preconditions; static-constructor and static-value assumptions are not supported in
this mode. Transferred proofs share repeated expression nodes in a compact data table;
reconstruction kernel-checks every declaration and independently replays the compiled result.
See [independent verification](FULL_VERIFICATION.md) for the trust boundary and required
producer evidence.

See [proof automation validation](VALIDATION-PROOFS.md#proof-automation) for the regression
coverage and the commands that run it.
