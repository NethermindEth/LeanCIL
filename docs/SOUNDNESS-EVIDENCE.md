# Extraction and contract evidence

## Independently checked extraction evidence

Shift certificates distinguish native-integer counts from ordinary `int64` counts, although both use
64-bit values during execution. Only `int32` and native counts are admitted. Native counts normalize
to their low 32 bits before the existing modulo-32 or modulo-64 operation;
`CIL.binary_native_shift_count` proves this normalization for all three shifts. Count masking,
including negative and oversized counts, is an admitted .NET runtime behavior rather than a
guarantee for every CLI implementation.

`CIL.Extraction.TranslationValid` binds one evidence record to every emitted method in program
order. Its component validators recompute sequential and explicit layouts from raw fields, packing
and declared size; require the complete set of layout-dependent instruction/local/parameter sites;
derive parameter homes from reachable raw argument operations; check generic substitution through
signatures, locals, operands and nested calls; and bind managed calls to the specialized target
table. Method initialization and return shape are checked too.

`TranslationValid rawLayouts computedLayouts methodEvidence imports program` also takes the import
table `Extracted.imports`. Import slot `j` is method index `program.length + j`, so it never names
an extracted method. A live external call site may emit `.call t c` only as a plain `call` of a
non-generic method with `t ≥ program.length`, a slot `imports[t - program.length]` whose identity
(assembly scope and full method name) equals the site's, whose parameter count, receiver and result
match the site's metadata, and `c` equal to the site's argument count; any other external site must
emit a non-call operation, as before. `validated_import_call` states these facts for an accepted
call and `validated_call_bound` shows every accepted call targets an index below `program.length +
imports.length`. The extractor does not yet resolve imports, so it emits `imports := []` and every
external site keeps its runtime model or is rejected. A slot's `closureDigest` and
`Extracted.importSignatures` are outside `TranslationValid`: like `signatures`, the signature table
only locates a slot for `bind_import`, and nothing yet binds a slot to an implementation or
contract.

Feature certificates record abstract incoming states at every original instruction. Lean checks
entry state, abstract transfers, all required successors, joins, the reachable mask and emitted
feature-dependent operations, including decided type tests. Closure and weakening theorems support
the analysis. This is not a full concrete-interpreter simulation theorem for every raw CLI opcode.
Raw metadata fidelity, unsupported transformations, static-data serialization and general
instruction translation remain part of the trusted boundary.

Scalar certificates additionally record the complete incoming stack of `word32`, `word64`, `native`,
`reference`, `nullObject` or `other` kinds at each feature-reachable PC. `ScalarFlowValid` checks
the empty entry, code/certificate lengths, raw maximum stack, independently derived raw transfers
and exact incoming-stack agreement on every required successor, including joins and backedges.
Managed call parameter and result types are bound exactly to the specialized callee's closed
signature. Call operands must match the reversed parameter-kind list and a reference receiver where
required. External parameter types must match the raw full signature after method and declaring-type
argument substitution; unsupported type spellings stay opaque. Local and argument stores must match
the declared home kind, with the explicit 64-bit storage rule below. Returns require the declared
result representation and no extra stack values; only native/int64 storage interchange is permitted.
External result kinds require the recorded runtime type to agree with the return spelling in the
full raw method identity; unknown types remain `other` and cannot justify scalar arithmetic or
conversions. Only supported integer producers receive an integer kind; unhandled producers,
including floating conversions and reference/array loads, remain `other`. This is a type-flow check
of the recorded raw input, not a proof that metadata decoding or raw serialization is faithful.

For every reachable covered opcode, `ScalarFlowValid` requires an exact emitted operation before any
general stack-effect check can accept it. The covered families are integer literals (`ldc.i4.*`,
`ldc.i4.s`, `ldc.i4`, `ldc.i8`), wrapping and checked add/subtract/multiply, signed/unsigned divide
and remainder, bitwise operations, shifts, negation, integer comparisons, all admitted
checked/unchecked integer conversions, and all twenty short and long compare-and-branch encodings
with their exact target. Literal encodings must have their signed operand range and exact bit
pattern, including high-bit-set 64-bit words. Conversion width, result signedness, input signedness
and checkedness are matched independently. Mixed native/int32 binary and compare-and-branch operands
require exactly one `nativeBinary` wrapper; homogeneous operands forbid it, and native/int64
mixtures and non-integer branch operands are rejected. Mixed `bne.un`, `bge.un`, `bgt.un`, `ble.un`
and `blt.un` are rejected as in the extractor: on .NET 10 CoreCLR zero-extends an int32 argument
there but sign-extends an int32 constant, so inlining changes the outcome. Mixed `clt.un` and
`cgt.un` sign-extend for both argument and constant operands, direct and inlined, tiered and fully
optimized, on x64 and arm64; this is an observed runtime fact, like the native runtime comparisons,
not a proof. The admitted profiles have a 64-bit native width.

A non-covered opcode cannot emit a literal, arithmetic, comparison, conversion, compare-and-branch
or `nativeBinary` operation, even with a matching stack effect. The only exceptions are a decided
type test's word, which the feature check binds, and size constants: `sizeof` and the exact
`System.Runtime` `Unsafe.SizeOf<T>()` site emit the primitive or vector width, or for an aggregate
the size that its layout use binds. `ScalarFlowValid.instruction_checked` exposes this per-site
obligation from an accepted certificate. Direct Lean regressions tamper with emitted arithmetic,
literals, conversion flags, wrappers, branches, stack kinds, joins, managed return widths, size
constants and scalar operations emitted at uncovered opcodes, including whole `TranslationValid`
rejection cases.

The scalar extension does not verify the whole extractor or establish a concrete CLI-to-model
simulation. Non-scalar operations at non-covered opcodes keep their existing specialized checks or
stack-effect fallback; runtime models emitted for external calls are outside the scalar certificate.
Metadata decoding, faithful raw input and static-data serialization, external runtime-model
correspondence, and correspondence between the model and the runtime remain explicit trust
assumptions.

The verifier independently kernel-replays the generated module and directly audits its compiled
`Extracted.translation_valid` theorem. The native audit requires a theorem whose type is exactly
`TranslationValid rawLayouts computedLayouts methodEvidence imports program`, compared structurally,
and audits its transitive axioms. Imported contract assumptions retain their separate identity-bound
audit. A missing certificate, an unrelated `True` theorem, a non-theorem declaration or a
certificate over a different import table cannot substitute for this check. Expected-rejection
consumer groups and negative fixtures retain a separate `ExtractionAudit` wrapper; ordinary
standalone and consumer verification do not elaborate this redundant module. Malformed-layout,
omitted-site, home-redirection, generic-substitution, feature-pruning, forged type-test and
whole-program evidence regressions exercise the validators independently of positive example proofs.

## Negative evidence

The wrong-addition fixture has a finite execution witness plus a uniqueness theorem refuting the
requested output at every successful fuel. Out-of-bounds and dangling-reference examples have
classified semantic faults plus `invoke_fault_refutes_success`, ruling out success for every fuel.
These proofs explain rejection independently of the tactic diagnostic produced when a positive
contract fails.

## Caller proofs and published library contracts

An imported library contract is a hypothesis of the caller theorem. The theorem has the form `forall
linked, Links Extracted.program linked -> Extracted.ImportsHold linked -> claim linked`. Generated
import conditions use fully qualified canonical contract predicates. The library's implementation
proofs and full-verification bundle are not needed for this caller check.

The consumer audits the supplied interface sources and their canonical contract closures.
`leancil-audit` computes both from the kernel-replayed interface oleans, in one walk per root that
visits each declaration once. The closure representation includes definition values, theorem and
inductive types, constructor metadata and computational recursor metadata/rules. It removes binder
names and expression metadata, uses de Bruijn indices, and normalizes universe binders. Imported
framework/toolchain module identity defines the stop boundary. Custom axioms, sorry, unsafe/partial
declarations, unbound variables and missing opaque values are rejected. The ordinary caller theorem
axiom allowlist and kernel replay policy are unchanged.

Every supplied interface module is independently kernel-replayed before its compiled artifacts enter
the accepted snapshot. Published certification does not exempt interface declarations from this
check. Compilation and an axiom audit alone cannot detect an unchecked declaration inserted by an
elaborator. This replay checks interface source declarations; it does not require a library's
implementation proof or a full-verification bundle.

The implementation-to-contract assertion is accepted from published certification, as schema-4
reports state. This is separate from the kernel-checked caller reasoning. Sidecar/DLL hashes
establish identity; they do not authenticate a publisher or prove a library implementation theorem.
The supplied certification theorem, statement and statement digest are provenance records here. Full
implementation verification is a separate producer operation.

Named type-initialization premises are part of the digest-bound export descriptor, scoped by full
assembly identity, type and profile. Export checks bind the exact list to regenerated extraction
through a kernel-checked, structurally audited equality. Import validation checks local type
constructors and exact propagation from dependency contracts. Caller artifacts and reports retain
the inherited premises. This certifies which runtime assumptions accompany the CIL proof; it does
not model CLR initialization or establish that an initializer ran. Exported constructor-initialized
field values and forced-full initialization premises remain unsupported.

`--force-full-verify` instead rechecks the library proof and composes it with the caller theorem. It
elaborates the source bundle of every library in the caller's reachable dependency closure, possibly
from different publishers, with the verifier's privileges. It is sound only when none of those
bundles can change the toolchain, extractor, caller artifacts, other bundles or outputs: run
untrusted bundles in an isolated, read-only environment without network. See [Independent
imported-library verification](FULL_VERIFICATION.md).

Deployment must bind the exact implementation bytes, method/signature/profile and a library
implementation satisfying the published contracts. A false or unsatisfiable published contract can
make the caller theorem vacuous. Retaining `Links` and `ImportsHold` exposes this condition; it does
not prove satisfiability. A successful report must be read with that deployment obligation.
Reference-only authoring checks do not produce a deployment certificate.

## Exception documentation lint

`lint-exceptions` is a diagnostic experiment. Its potential model sites are structural observations,
not proved exception behavior. XML declarations and prose are untrusted. A documented exception
absent from this limited model is not evidence that the runtime cannot raise it. Lint does not check
proof terms, alter preconditions or issue a verification receipt. The selected XML bytes are
recorded but are not independently bound to the DLL build.
# Typed import metadata

Format 2 imports bind exact closed generic instances and imported byref struct layout metadata.
`LayoutProjectionValid` checks the signature-scoped raw catalog against selected artifact entries,
including nested reindexing and computed layout equality. Required `ImportedLayoutsValid` evidence
checks published versus selected raw values, `LayoutsValid`, unique identities and typed signature
coverage. The extractor also compares those values with the selected pinned DLL metadata. These
propositions do not verify Cecil decoding or establish CLR correspondence beyond the existing
admitted layout model. Reference-only interfaces and caller proof caches gain no new authority. See
[TYPED-IMPORTS.md](TYPED-IMPORTS.md) for the supported subset and rejection rules.

### Reference observations

`brtrue`, `brfalse`, `ceq`, `beq` and `bne.un` observe allocation-relative references, including
readonly views, without reading bytes or granting authority. Non-null operands must pass formation
and lifetime checks. Equality compares offsets within one allocation and distinguishes interiors of
different allocations. A comparison between different allocations involving an end pointer is
unsupported: allocation identities do not establish whether adjacent runtime addresses coincide.

Bounded `ldnull` emits the existing null-reference value, while scalar evidence tracks its raw
object-null kind separately from managed references. It can be truth-tested, compared with another
object null, duplicated or discarded. It cannot justify object parameters, locals or results, or a
comparison against a managed reference. The scalar certificate binds the raw null literal,
comparison operation and branch target exactly.

Pointer subtraction and unsigned ordering require live, well-formed references. Differences and
orderings additionally require both references to identify the same allocation; no relative runtime
addresses are inferred from different allocation identities. The runtime correspondence assumes an
allocation occupies one contiguous, non-wrapping address interval. Within that interval, unsigned
address order matches offset order and address subtraction cancels its base. Differences retain
their native-width two's-complement representation. Subtracting an int32 or native byte displacement
reuses checked wrapping reference arithmetic and retains readonly restrictions. None of these
observations reads, initializes or grants authority over storage.
