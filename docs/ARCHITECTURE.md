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
steps; for symbolic branches or memory operations, supply the proved conditions with
`cil_checked_steps [facts]`. [Instruction composition](PROOFS-STEPPING.md#compose-instructions)
lists the tactics, the goals they accept and the facts each instruction family needs, and
[fact preparation](PROOFS-CONTRACTS.md#supply-facts-to-the-stepping-tactics) states how supplied
facts are normalised. Contract stepping handles signed and unsigned widening in either argument
order.

- `CodeAt` facts let the tactics resolve instructions within a known code segment without
  expanding the whole method, and `Segment` contracts compose checked prefixes through exact
  intermediate states and fuel costs; see
  [segments](PROOFS-STEPPING.md#place-code-and-compose-segments).
- The snapshot forms of the stepping tactics track numeric local stores and loads, including
  mixed Vector128, Vector256 and int32 locals; see
  [snapshot walks](PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots). Snapshot facts
  neither supply write authority nor justify a value of the wrong local kind.
- Loop segments use `CIL.Safety.LoopAutomation` and require an invariant and a decreasing measure;
  see [loops](PROOFS-STEPPING.md#step-loops).

### Reusing a proof across bodies and profiles

- A supported forwarder body inherits its callee's proved contract; see
  [forwarder composition](PROOFS-CONTRACTS.md#inherit-a-callees-contract-in-a-forwarder).
- Contract refinement derives a public interface from a stronger proved contract; that interface
  can be exported and imported by callers.
- `cil_embed [facts]` binds a shared body template to an extraction using proved feature flag and
  callee equalities; the template carries the extraction's declared signature and layout environment.
  Local definitions also work without a fact list; relevant flags left
  unconstrained are rejected, and the kernel checks the complete instruction map.
- `leancil templates shared scalar-extraction sse42-extraction v3-extraction` generates the
  shared bodies from compiled CIL, including per-instruction equations and a binding module for
  each input. Prove the template once and use the generated bindings for the selected profiles;
  see [generated profile templates](PROOFS-BINDING.md#generated-profile-templates) for the
  supported domain and checking workflow.
- Embedding proofs can ignore trailing unread byref, pointer or span locals. Allocation
  refinement (`CIL.Safety.AllocationRefinement`, which `import CIL` does not load) relates
  numeric and interspersed dead locals, with fresh allocation identities free to differ. See
  [dead-local refinement](PROOFS-BINDING.md#bodies-modulo-dead-code) for which route keeps exact
  memory and for the frame restrictions.

### Publishing and importing contracts

Public and protected static methods can publish contracts for separately compiled callers,
including a derived class calling a protected base method. A call through a published contract is
statically resolved.

Exported contracts can carry an explicit type-initialization premise for libraries with static
constructors, including types containing `static readonly` struct fields. The premise is a
runtime assumption and does not prove that the CLR initializer ran; the
[sidecar schema](CONTRACT-INTERFACES.md#sidecar-schema-1) states how it is bound and propagated.
Constructor-initialized field values are not supported for export.

An `export-contracts` manifest can list several profile artifacts for one method and one family
theorem. Each extraction is checked independently, with kernel-checked flag agreement and exact
equality to the reprofiled reference program. See the
[profile-family manifest example](PROOFS.md) for the same-flag transport requirements. Compatible
exports share their source snapshot and reusable compilation work; each export retains its own
theorem, contract closure, replay and publication checks.

`leancil verify --force-full-verify` independently checks supported imported libraries and their
reachable contract dependencies against separately pinned implementation DLLs, interfaces and
source bundles, using no cached proof result. Composition preserves normal returns and named
exceptional outcomes. See [independent verification](FULL_VERIFICATION.md) for the checks, the
supported libraries, the trust boundary and the required producer evidence.

See [proof automation validation](VALIDATION-PROOFS.md#proof-automation) for the regression
coverage and the commands that run it.
