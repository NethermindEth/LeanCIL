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
| Method body decoding | Decode the bytes the extractor emitted for a body (tiny or fat header, every standard opcode, branch targets as instruction indices) through the token table and compare `maxStack`, `initLocals`, the locals and every instruction with the original definition | That the bytes are the method's body in the image (reconfirmed by the opt-in [strict binding audit](CLI.md#strict-binding-audit)) and the PE container stay trusted; bodies with exception sections are rejected |
| Metadata binding | Decode the table rows, heap entries and signature blobs each method carries and check every token-table entry, every local type and the method's own definition against them | That the carried bytes are the image's, platform definitions, public key tokens, the hashed part of generic import identities, raw layout content, dispatch catalogs, static data and generic parameter constraints |
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
original definition's `maxStack`, `initLocals` and `code`, and checks the definition and locals
against the metadata it carries ([Metadata binding](#metadata-binding)):

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
  belong to a metadata table the opcode accepts. A token has one entry, and a field access names
  a static or instance field as its opcode requires.

Only the kernel decides `BodyDecodes`: the elaborator's `decide` is refused at once with `failed to reduce`.
Extractions prove it per method as `method{n}_body_validated`, whose `bodyMatches` part uses `cil_body_decodes`:
it runs `decide +kernel` and, when the kernel refutes it, reports the method and either the error the check
raised or the part of the decoded body that differs from the emitted definition. The kernel keeps nothing between
declarations, so the lookup tables of the metadata are written out once as a literal (see below) and each
method's check reads them by name: its cost is its own bytes and tokens times a logarithm of the rows, whatever
the number of methods or rows of the extraction.

In the default flow Lean does not establish that the emitted bytes are the method's body in the
assembly image: System.Reflection.Metadata locates the body in the PE image, and the PE container
stays trusted. The opt-in [strict binding audit](CLI.md#strict-binding-audit) reconfirms it in the
kernel for assemblies whose digests you state: each body's bytes must be the bytes at the file
offset that the section table gives for the RVA in the image's own MethodDef row for that method.
The carried rows have that RVA column zeroed, so the audit's comparison of a carried row with the
image's masks it. What the tokens, the locals and the method definition mean is checked against the
metadata rows the body carries, as the next section describes.

A closed generic instantiation carries the bytes of its open definition, so it shares the
`method{n}Bytes` definition of the first method that uses them. A token used at several sites
has one table entry, and the extractor refuses a token whose sites resolve to different operands.
An external call spells its identity as a materialized name at a reachable site and as a literal
at an unreachable one; the kernel decides that the two are equal strings, so one entry serves
both.

### Metadata binding

Each module's methods share one `module{k}Metadata`, a `MethodMetadata`
([MetadataBytes](../CIL/Extraction/MetadataBytes.lean)): the raw bytes of the table rows and heap
entries that the tokens, definitions and locals of all the module's methods reach, emitted once per
extraction, with one slice per assembly it reaches, and each pinned assembly has one small block with its
table stream header and `Assembly` row. The `RVA` column of every carried `MethodDef` row is zero: where a
body sits in the image moves whenever an earlier body changes length, so no method's evidence may depend
on it. The same holds for `#Strings` and `#Blob` offsets, which move when an earlier name changes length:
the extractor renumbers them, in the rows and the heap keys, to the rank of each carried entry among the
carried entries by bytes (the image's own entry order is a hash or suffix sort that one changed name can
reshuffle), and Lean reads a heap entry only through the offset a row names. (`#US` offsets are named by the body's own `ldstr`
tokens and stay the image's.) The extractor records each body's address as `bodyAddress` in `identity.json`,
outside the Lean evidence, for the strict audit. A slice also holds links, each naming for a token the definition it resolves to, its declaring type,
its `NestedClass` row or its first `GenericParam` row. Lean reads the rows by the widths the header
fixes, decodes strings, blobs and user strings, and decodes the signature blobs
([Signatures](../CIL/Extraction/Signatures.lean)). `MetadataResolution` and `MetadataBinding` then
check what the extractor states.

Building the lookup trees of a slice costs its size, and the kernel keeps no cache between declarations. The
extractor therefore writes them out once per module as the literal `module{k}Tables` (balanced search trees of the
rows, heap entries, links and instance field counts), and `module{k}_tables_valid` states that `tablesMatch`: the
decoder builds exactly that literal from `module{k}Metadata`. That decision costs the carried rows times a
logarithm and is made once per extraction; each `method{n}_body_validated` uses it as a premise.

What `MetadataResolution` and `MetadataBinding` check:

- The scope of every type is the assembly identity its `AssemblyRef` row spells (name, version,
  culture, key token); nested types are named `Outer/Inner`; a type defined in a carried slice has
  the value type, enum (with its integer type), class or interface kind its flags and base give.
- Each `.type`, `.field`, `.call`, `.indirectCall` and string operand of the token table is
  checked against its token. The extractor chooses among `atom`, `object`, `aggregate` and `enum`
  for a type, and Lean accepts the choices that name the same scoped type with a form its kind
  allows. A field's index and static flag, the generic arguments of a type or method instantiation,
  the parameter and return types after substitution, the definition a member reference resolves to
  in a pinned assembly (its name, its signature and its place in its type's members) and the
  external identity of a call (the scope and Cecil's `result Owner::name(parameters)`) are
  recomputed from the bytes.
- The local variable types are checked against the standalone signature the body header names.
- The method's own identity is checked against its `MethodDef` row: owner, flags, calling
  convention, parameter and return types, generic parameter counts and flags, the class layout
  facts of a class receiver. Every column of the row is compared but the address of the body.
- A table or signature form the checker does not read is an explicit error: tables other than
  those the checker names, general arrays, `typedref`, pinned locals and vararg conventions,
  modifiers other than `modreq(InAttribute)` on an `in` parameter and `modreq(IsExternalInit)` on a
  `void` return, forwarded types, module references and `AssemblyRef` rows with a public key flag.
- A type that a signature names only as a custom modifier is read by its scope and name alone, so it needs
  no link to a definition, whether or not its assembly is pinned or the type resolves
  (`modifierNamed` in [MetadataResolution](../CIL/Extraction/MetadataResolution.lean) and the extractor's
  slice collector agree). A type used any other way keeps the link, and a pinned type that does not resolve
  there stops the extraction with `Unresolved pinned type`.

Trusted: that each carried row, heap entry and body is the image's bytes at that position (a wrong
copy cannot be detected without the whole stream; every row must still have the length the header's
widths give, every blob its length prefix and every string one terminating zero), the PE container
where a body sits in the image and the mapping of its address to its bytes, definitions in platform assemblies (so whether a
platform type is an enum, the field order of `ValueTuple`, and that `System.Object` declares no
instance fields), public key tokens (the hash of a key is not computed in the kernel), the hashed
part of a generic import identity, raw layout content, dispatch catalog completeness, static data
bytes and generic parameter constraints. `check` hashes each assembly and regenerates the
extraction, so the rows are a deterministic function of hashed inputs.
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
