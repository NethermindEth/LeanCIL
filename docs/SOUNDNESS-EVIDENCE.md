# Extraction and contract evidence

<!-- audience: maintainers -->

## Independently checked extraction evidence

`TranslationValid rawLayouts computedLayouts methodEvidence imports program` checks one record
per emitted method in program order. The verifier kernel-replays and structurally audits
`Extracted.translation_valid`; an unrelated theorem, non-theorem or different program/import table
cannot substitute for it.

| Evidence | Independently checked relation | Remaining assumption or limit |
| --- | --- | --- |
| Layouts | Recompute layouts from raw fields, packing and size; check required use sites and bounds | Faithful metadata/serialization and runtime layout correspondence |
| Specialization | Substitute closed method/owner arguments through signatures, locals, operands and calls, including the owner segment of an external call identity (`scope::result owner::member`, open owners spelled `!!n`/`!n`); preserve control flow | Faithful raw definitions and admitted constraints |
| Feature flow | Entry, transfers, joins, required successors, reachable mask and feature-dependent operations | No complete concrete CLI simulation for every opcode |
| Method body decoding | Decode the bytes the extractor emitted for a body (tiny or fat header, every standard opcode, branch targets as instruction indices) through the token table and compare `maxStack`, `initLocals`, the locals and every instruction with the original definition | That the bytes are the method's body in the image (reconfirmed by the opt-in [strict binding audit](CLI.md#strict-binding-audit)), the PE and metadata readers, every token's resolution and the local types stay trusted; bodies with exception sections are rejected |
| Scalar flow | Complete stack kinds, raw maximum stack, joins/backedges, call arguments/results, homes and returns | Unknown types remain opaque |
| Scalar translations | Exact literal values, arithmetic, comparisons, conversion flags and branch targets | Other operations require specialized checks or retain stack-effect fallback |
| Managed/imported calls | Target slot, scoped identity, full signature, argument count, receiver and result | An import slot does not prove its implementation contract |
| Constrained calls | Resolve serialized interface/override declarations to the emitted closed direct target | Complete metadata serialization; no general vtable/boxing model |
| Static values | Checked execution yields emitted bytes without circular reads of the values being justified; unknown values have no initializer and are read only from the caller's binding | Initializer recognition and deployment initialization/immutability |

Exact scalar matching covers integer literals, wrapping/checked add/subtract/multiply, signed and
unsigned divide/remainder, bitwise operations, shifts, negation, integer comparisons, admitted
integer conversions and all short/long compare-and-branch encodings. Literal ranges and
high-bit-set int64 values, conversion width/signedness/checkedness and exact branch targets cannot
pass by stack effect alone. Non-covered raw opcodes cannot emit these scalar operations, except
feature-bound type-test words and size constants bound to exact primitive/vector widths or
validated layouts.

Mixed native/int32 operations require the exact `nativeBinary` wrapper; homogeneous operands forbid
it. Native/int64 arithmetic mixtures are rejected. The 64-bit representation interchange at homes
and returns does not justify arithmetic interchange. Native shift counts use their low 32 bits;
the normalization theorem does not establish behavior on arbitrary CLI implementations.
See [runtime assumptions](SOUNDNESS-RUNTIME.md#runtime-assumptions).

### Method body decoding

Each method's evidence holds the bytes the extractor emitted for its body (the header and the
code, not extra sections) and a token table. `BodyDecodes` decodes the bytes in the kernel
([BodyDecoding](../CIL/Extraction/BodyDecoding.lean)) and requires the result to equal the
original definition's `maxStack`, `initLocals`, locals and `code`:

- The header is a tiny header or a fat header of three words that sets at most the init-locals
  flag. A body with extra sections (exception handlers) is rejected, and the supplied bytes must
  be exactly the header and the declared code size.
- Every opcode of the ECMA-335 table has one operand encoding. The table is transcribed from the
  standard; `operand_kinds_agree_with_cecil` in `Tests/BodyDecoding.lean` compares it with a
  static list generated once from `Mono.Cecil.Cil.OpCodes`. An unknown opcode byte, a truncated
  operand or a token missing from the table is an error.
- A branch must land on the first byte of an instruction inside the body, and its operand
  becomes that instruction's index. A target outside the body, inside an instruction or on the
  instruction after a prefix opcode (`unaligned.`, `volatile.`, `tail.`, `constrained.`, `no.`,
  `readonly.`) is an error.
- A token operand is read from the four bytes in the body, looked up in the table, and must
  belong to a metadata table the opcode accepts. The header's local signature token must equal
  the table's.

In the default flow Lean does not establish that the emitted bytes are the method's body in the
assembly image, nor that a token resolves to the operand the table gives it. Mono.Cecil resolves
the tokens and System.Reflection.Metadata locates the body in the PE image; both stay trusted.
The opt-in [strict binding audit](CLI.md#strict-binding-audit) reconfirms the first of these in
the kernel for assemblies whose digests you state: each body's bytes must be the bytes at the
file offset that the section table gives for the RVA in the method's own MethodDef row. Token
resolution stays trusted, and the audit reports it as not covered. The local types
are the extractor's: one call produces them for the definition and for the table, so comparing
them can only fail if the two were edited apart. Decoding the local signature blob and checking
tokens against the emitted metadata rows are open items.

A closed generic instantiation carries the bytes of its open definition, so it shares the
`method{n}Bytes` definition of the first method that uses them. A token used at several sites
has one table entry, and the extractor refuses a token whose sites resolve to different operands.
An external call spells its identity as a materialized name at a reachable site and as a literal
at an unreachable one; the kernel decides that the two are equal strings, so one entry serves
both.
### Folded instruction patterns

A fold applies only to its recognized raw sequence with checked entry edges. Different compiler
output can lose admission without invalidating a theorem over an already admitted program.

| Pattern | Required binding | Limit |
| --- | --- | --- |
| Closed `typeof` equality/inequality calls, reference `ceq` and comparison branches | Exact type handles, runtime helper identities, substituted types, result and selected target; all encoded targets validated and no branch into the interior | Forwarding/scoped identity ambiguities, decorated names and arbitrary runtime `System.Type` use remain unsupported. Reference comparison relies on [CoreCLR runtime type equality](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Type.cs) and [GetTypeFromHandle](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/System.Private.CoreLib/src/System/Type.CoreCLR.cs). |
| `throw new E(...)` | Allowlisted type/constructor, permitted literal/null arguments and final throw; no branch into the interior | No exception-object identity, observable constructor effects, handlers or resource-exhaustion model. |
| `ldnull; throw` | Adjacent operand-free null load and throw, bound to `System.NullReferenceException`; no branch into the throw | No general exception-object evaluation or handlers. |
| Single-use span receiver | Exact local uses and permitted Length/Item receiver sequence; protected entry edges | No escaping or aliased receiver addresses. |
| In-place span constructor | Exact receiver/argument positions, constructor identity, element layout/width and capability | Unrecognized argument expressions and interior branch entries are rejected. |

The [compiler corpus](COMPILER-COVERAGE.md) checks admission changes, not compiler correctness or
every possible folded pattern. The runtime-call inventory does not count these folds.
[OPCODES](OPCODES.md) records the admitted forms. Metadata table decoding, token resolution,
static-data serialization and runtime-helper correspondence remain trusted even when evidence
validates.

## Negative evidence

Direct Lean mutations exercise validators independently of hashes/regeneration: scalar meanings,
stack kinds/joins, layouts, homes, generic substitution, pruning, call slots and folds. Positive
controls establish that fixtures reach the intended obligation. See
[validation](VALIDATION-COVERAGE.md). Wrong-addition has an execution witness and an
all-successful-fuel refutation; bounds/lifetime examples use `invoke_fault_refutes_success`. A
failed positive proof or resource exhaustion alone is not a semantic counterexample.

## Caller proofs and published library contracts

Ordinary caller theorems are conditional:
`forall linked, Links Extracted.program linked -> Extracted.ImportsHold linked -> claim linked`.
Canonical predicates and scoped identity/profile pins bind assumptions to selected interfaces.
Deployment must supply the exact implementation bytes and an implementation satisfying those
contracts. A false or unsatisfiable imported contract can make a caller theorem vacuous.

Every supplied interface module is kernel-replayed. The canonical contract-closure audit includes
definition values, theorem/inductive types, constructors and computational recursor rules. It
rejects custom axioms, sorry, unsafe/partial declarations, free variables and missing opaque
values. Normalization removes binder names/metadata, normalizes universe binders and stops at
pinned framework/toolchain identities.

Ordinary caller verification accepts the implementation-to-contract assertion from published
certification; it does not reprove the implementation. Sidecar/DLL hashes identify bytes, not
publisher authenticity. Theorem/statement digests are provenance records. `--force-full-verify`
rechecks reachable proof bundles and composes them with the caller. Those sources execute Lean
elaborator code with verifier privileges; untrusted bundles need isolated, read-only, network-free
execution. See [full verification](FULL_VERIFICATION.md).

Initialization premises are bound by assembly, type and profile, checked against extraction and
propagated through dependencies into reports. They identify assumptions; they are not evidence
that a CLR initializer ran. Constructor-derived exported field values and forced-full
initialization premises are unsupported. Reference-only authoring checks do not issue deployment
certificates.

## Pinned referenced assemblies

An extraction may include bodies and layouts from each `--reference` assembly. Those DLLs are
trusted inputs on the same terms as the selected one; no other assembly can contribute code.

- `Extracted.assemblies` lists every pinned identity, the selected assembly first, and each
  `MethodEvidence` carries the identity of the assembly its body came from. Hashes and MVIDs
  are not in the certificate, so `Extracted.lean` depends on the extracted program alone.
- `TranslationValid` requires `AttributionValid`: each body's owner identity is scoped by its
  own pin's colon-free identity, so a body attributed to the wrong assembly fails the kernel
  check ([tests](../Tests/AssemblyPins.lean)). Distinct pins and a complete `assemblies` list
  are extractor output that `check` regenerates; they are not a Lean obligation.
- Lean cannot hash bytes. `identity.json` records each assembly's identity, MVID and SHA-256;
  `check`, and so `verify`, rehashes the selected and every referenced DLL against it and
  regenerates the certificate, so a substituted DLL or a changed recorded hash is rejected
  before the proof is compiled.
- A reference that contributes only layouts appears in `Extracted.assemblies`, the manifest and
  the hash recheck, but not in `TranslationValid`;
  its layouts are bound by their assembly-qualified identities in the layout evidence.
- A closed generic struct of a referenced assembly is laid out from its defining module, and
  its `RawLayout.generic` evidence names that module's scope as the owner constructor;
  `genericLayoutValid` rederives the layout identity from the owner and every scoped argument,
  so an owner moved to another assembly fails `LayoutsValid`
  ([test](../Tests/MultiAssemblyGenerics.cs)). Specialized generic methods and static methods
  of generic classes keep their definition's module, so `AttributionValid` binds them to their
  defining pin.

Resolution never searches directories. A pinned full name resolves to its pinned module, the
four framework public-key tokens resolve to the runtime's trusted platform list as runtime
models, and anything else fails. A referenced type with a static constructor, a static field load
or `calli` in a referenced body, and a method signature shared by two pinned assemblies are
rejected. Constrained dispatch reads metadata from the selected assembly and the pinned
references only, so a struct may implement an interface of another pinned assembly. The rule's
invariant is catalog completeness: the receiver's interface list is closed under inheritance and
every entry is present, so no unseen override can be more specific than the selected body, and
every entry comes from hashed bytes `check` replays. In Lean each dispatch catalog entry names the
pin its metadata came from and resolution reads only entries whose pin scopes their type; the
selected program method must carry the target's token and scoped owner, so `AttributionValid`
binds its body to a pin as well. An interface of an unpinned assembly fails resolution.

## Typed import metadata

`LayoutProjectionValid` and `ImportedLayoutsValid` bind closed generic identities and admitted
byref aggregate layouts: raw catalog, selected entries, nested reindexing, computed layouts,
uniqueness and signature coverage. Extraction also compares the pinned DLL metadata. These checks
do not verify Cecil or remove runtime assumptions. See [typed imports](TYPED-IMPORTS.md).

An imported aggregate local sizes caller frame storage from the same pinned metadata that byref
contracts already trust; it adds a consumer and no trusted source. `ImportedLocalLayoutsBound`
requires every caller layout entry whose identity a slot publishes to equal that slot's selected
layout, nested indices bound by identity, with the same computed layout, for every such slot.
Extraction admits such a local only when its whole closure is published and one bound typed call
carries it, so the kernel link is never vacuous for an admitted local.

## Reference observations

Truth tests and equality check formation/lifetime without reading bytes or granting authority.
Same-allocation equality uses offsets. Different-allocation interiors are distinct; comparisons
involving end pointers across allocations are unsupported because adjacent addresses may coincide.
Pointer difference and unsigned ordering require a single live allocation and assume a contiguous,
non-wrapping runtime address interval. Native displacement arithmetic retains provenance and
readonly restrictions; no ordering between allocation bases is inferred.

Object `ldnull` has a distinct scalar-flow kind. The certificate admits it in truth tests, in
identity comparisons with class instance references, and as a local, argument, call parameter or
return value whose type is a class instance, a supported array or a typed handler table. It is
also admitted as the value of a class-typed field or of a reference-array element. It is never
admitted in a numeric or managed-reference slot, and its comparison with a managed reference is
rejected. The raw literal, comparison operation and branch target remain exactly checked.

Each `ldstr` emits the string literal of exactly its own text, typed as an object; no other raw
opcode emits a literal, and inside a folded `throw` the load emits nothing.

Each argument guard operation is decoded again from its raw `call`: the owner, method name, integer
type argument, parameter types and external identity fix the guard, its width and its signedness
(`CIL.Extraction.guardCallMatches`). No other instruction emits a guard, and a `ThrowIfNull`
argument is typed as an object reference.

## Exception documentation lint

`lint-exceptions` reports structural potential sites. XML prose is untrusted and not independently
bound to the DLL build. A missing site does not establish exception impossibility. Lint checks no
proof, changes no precondition and issues no verification receipt.
