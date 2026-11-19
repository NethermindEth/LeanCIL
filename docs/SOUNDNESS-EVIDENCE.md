# Extraction and contract evidence

<!-- audience: maintainers -->

## Independently checked extraction evidence

`TranslationValid rawLayouts computedLayouts assemblies methodEvidence imports program` checks one
record per emitted method in program order, each body against the one list of pinned assemblies. The verifier kernel-replays and structurally audits
`Extracted.translation_valid`; an unrelated theorem, non-theorem or different program/import table
cannot substitute for it.

| Evidence | Independently checked relation | Remaining assumption or limit |
| --- | --- | --- |
| Layouts | Require one row per type identity, recompute field placement and size, and check use sites and bounds | Faithful raw metadata, including the byref-like declaration marker, and runtime layout correspondence |
| Specialization | Substitute closed method/owner arguments through signatures, locals, operands and calls, including the owner segment of an external call identity (`scope::result owner::member`, open owners spelled `!!n`/`!n`); preserve control flow | Faithful raw definitions and admitted constraints |
| Feature flow | Entry, transfers, joins, required successors, reachable mask and feature-dependent operations | No complete concrete CLI simulation for every opcode |
| Method body decoding | Decode the bytes the extractor emitted for a body (tiny or fat header, every standard opcode, branch targets as instruction indices) through the token table and compare `maxStack`, `initLocals`, the locals and every instruction with the original definition | That the bytes are the method's body in the image (reconfirmed by the opt-in [deep verification](CLI.md#deep-verification)) and the PE container stay trusted; bodies with exception sections are rejected |
| Metadata binding | Decode the table rows, heap entries and signature blobs each method carries and check every token-table entry, every local type and the method's own definition against them, including generic import descriptors and their open signatures and closed arguments | That the carried bytes are the image's, platform definitions, public key tokens, imported implementation definitions, raw layout content, dispatch catalogs, static data and generic parameter constraints |
| Scalar flow | Complete stack kinds, raw maximum stack, joins/backedges, call arguments/results, homes and returns | Unknown types remain opaque |
| Scalar translations | Exact literal values, arithmetic, comparisons, conversion flags and branch targets | Other operations require specialized checks or retain stack-effect fallback |
| Managed/imported calls | Target slot, scoped identity, full signature, argument count, receiver and result | An import slot does not prove its implementation contract |
| Call links | The emitted link table's keys ascend and are pcs of the code, and the link each pc reads from it, by one walk beside the code, is the one the instruction there implies; so the table is the one the emitted instructions imply, entry by entry | The interpreter does not read the link table, so a link adds no behavioral claim beyond its instruction |
| Declared signature | The method's receiver kind, parameter types and return type equal those of its closed raw method | Faithful raw metadata |
| Environment | Every method's environment is the program's raw and computed layout tables, which `LayoutsValid` recomputes | Layout correspondence, as for Layouts |
| Constrained calls | Resolve serialized interface/override declarations to the emitted closed direct target | Complete metadata serialization; no general vtable/boxing model |
| Static values | Checked execution yields emitted bytes without circular reads of the values being justified; unknown values have no initializer and are read only from the caller's binding | Initializer recognition and deployment initialization/immutability |

For a supported `MemoryMarshal` member, `RuntimeModelsAgree` checks the kept call against its
declaration, closed operand and checked layouts. Both element widths of `Cast` and the transfer
kind of the read and write operations come from the model. A missing overload or layout leaves
an opcode-tagged hole that the validator accepts only at an unreachable site.

For a method defined by its decoder, the evidence proves that its entire instruction list equals
the decoding of the closed body. At a reachable instruction outside a fold, the scalar validator
uses this equality for value encodings when the decoder supplies an instruction. A decoded hole
still needs the explicit site check, as do folded sites and methods emitted as literals.

Exact scalar matching covers integer literals, wrapping/checked add/subtract/multiply, signed and
unsigned divide/remainder, bitwise operations, shifts, negation, integer comparisons, admitted
integer conversions and all short/long compare-and-branch encodings. Literal ranges and
high-bit-set int64 values, conversion width/signedness/checkedness and exact branch targets cannot
pass by stack effect alone. Type-test folds and runtime queries can emit scalar constants when their site checks pass.
A `sizeof` instruction pushes the width of its closed operand. An `Unsafe.SizeOf` call retains
its call instruction and obtains its result from its runtime model.

For a span indexer or pinnable reference, scalar flow checks the same open declaration, closed
signature and external target as the model before classifying the result as a reference. The
readonly declaration requires the `InAttribute` modifier on the by-reference result.

Indirect accesses are matched exactly too. Each integer `ldind` and `stind` must emit the
`ldind` or `stind` of the kind its opcode names, which `Instruction.ofRaw?` decodes, and so must
each `newarr`, `ldlen`, integer `ldelem.*` and `stelem.*`, typed `ldelem` and `stelem`, `ldelema`,
`ldelem.ref` and `stelem.ref`, a handler table's `ldlen`, `ldelem.i` and `ldelem` included. A typed
access or element address takes its element's width from the element shape of the method's checked
layouts. An `ldelema` decodes read-only exactly when `readonly.` precedes it, and `readonly.`
decodes to `nop`; no instruction but `ldelema` decodes after `readonly.`, and the scalar check
requires the raw instruction after each reachable `readonly.` to be `ldelema`, which also holds a
translated instruction to the rule (`readOnlyPrefixMatches`). Object loads, stores, initializations, copies
and sizes decode with their type tokens.
`ObjectOperandsValid` checks the storage shape for each distinct live opcode and operand.
For methods with aggregate object instructions, the extractor supplies the named shape fact at
each site in instruction order. `ObjectOperandsValid.of_sites` checks this sequence against the
raw body and proves that it covers every distinct operand.
The scalar validator binds each literal opcode and type to its site. Only a proved decoding
can skip that comparison. A span load requires a direct source of the same span type. A span
reset uses the checked local fold. Block copies and initializations retain the alignment of
their prefix, with an alignment of eight for an unprefixed operation. `volatile.`, an
`unaligned.` alignment other than 1, 2 or 4, and `unaligned.` before an instruction that does
not take it are rejected.

Each `ldfld`, `ldflda` and `stfld` of an instance field of a struct, or of a class that is not
a generic instance, must emit the field instruction of the same opcode over the operand's field
reference, which `Instruction.ofRaw?` decodes, and the step resolves the field's offset and
width from the method's checked layouts (`CIL.Method.fieldShape`). `ldfld` and `stfld` decode
after `unaligned.` to the same instruction as without it, since the model gives a field access no
alignment of its own; `ldflda` after `unaligned.` and any of the three after `volatile.` do not
decode. The scalar check requires a struct field load to read a struct reference or value, a
struct field address or store to go through a reference, and a stored value to suit the field.

Mixed native/int32 operations execute the decoded arithmetic opcode with operand widening.
Native/int64 arithmetic mixtures are rejected. The 64-bit representation interchange at homes
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
  `readonly.`) is an error, whether or not any path reaches the branch. Decoded code therefore
  satisfies `PrefixEntryFree` over instruction indices (`checkBody_prefixEntryFree`), and so
  does the instantiated code of every method whose evidence is valid
  (`MethodEvidenceValid.prefixEntryFree`). The extractor refuses such a body with the blocker
  "Branch enters the instruction after a prefix".
- Direct raw method construction enforces the same branch-entry rule. Both raw construction
  and method shape evidence check each prefix and its taker, including unreachable sites.
  A constrained static call requires a static virtual method on an interface. Lean binds that
  claim to the declaring type and method flags in the carried metadata. A tail transfer
  requires matching return types and an adjacent return.
- A token operand is read from the four bytes in the body, looked up in the table, and must
  belong to a metadata table the opcode accepts. A token has one entry, and a field access names
  a static or instance field as its opcode requires.

Only the kernel decides `BodyDecodes`: the elaborator's `decide` is refused at once with `failed to reduce`.
Extractions prove it per method as `method{n}_body_validated`, whose `bodyMatches` part uses `cil_body_decodes`:
it runs `decide +kernel` and, when the kernel refutes it, reports the method and either the error the check
raised or the part of the decoded body that differs from the emitted definition. The kernel keeps nothing between
declarations, so the lookup tables of the method's own metadata slice are written out as a literal (see below)
and the method's check reads them by name: its cost is its own bytes and tokens times a logarithm of its slice,
whatever the number of methods or rows of the extraction.

In the default flow Lean does not establish that the emitted bytes are the method's body in the
assembly image: System.Reflection.Metadata locates the body in the PE image, and the PE container
stays trusted. The opt-in [deep verification](CLI.md#deep-verification) reconfirms it in the
kernel for assemblies whose digests you state: each body's bytes must be the bytes at the file
offset that the section table gives for the RVA in the image's own MethodDef row for that method.
The carried rows have that RVA column zeroed, so the audit's comparison of a carried row with the
image's masks it. What the tokens, the locals and the method definition mean is checked against the
metadata rows the body carries, as the next section describes.

A closed generic instantiation carries the bytes of its open definition, in its own `method{n}Bytes`,
and its own metadata slice, so its component names no other method. A token used at several sites
has one table entry, and the extractor refuses a token whose sites resolve to different operands.
An external call spells its identity as a materialized name at a reachable site and as a literal
at an unreachable one; the kernel decides that the two are equal strings, so one entry serves
both.

### Metadata binding

Each method carries its own `method{n}Metadata`, a `MethodMetadata`
([MetadataBytes](../CIL/Extraction/MetadataBytes.lean)): the raw bytes of the table rows and heap
entries that its own tokens, definition, signature and locals reach, with one slice per assembly it
reaches. Each pinned assembly has one small block, `assembly{k}Metadata`, with its table stream header
bytes, the header they decode to (heap sizes and the row count of each present table) and its `Assembly`
row, a function of that assembly alone, so every extraction of it writes the same bytes.
`assembly{k}_identified` proves once per assembly that the bytes decode to the stated header, which every
method's checks then read without decoding it again, and that the identity its `Assembly` row spells is
the string the block states (`assembly{k}Identity` holds those bytes). A method's `BodyDecodes` equates its own
assembly's identity with its pin, lists the identity of every pinned assembly (`pinned`, equated with
`Extracted.assemblies`) and names the identity each of its slices spells.

Every byte list of this evidence (body bytes, rows, heap entries, header bytes and UTF-8 names) is written
as `CIL.Extraction.fixedBytes count code` ([FixedDigits](../CIL/Extraction/FixedDigits.lean), specified in
[ByteLiterals](../CIL/Extraction/ByteLiterals.lean)): its length
and one number holding the bytes big-endian. The code of a list of at most 256 bytes is one hexadecimal numeral,
and a longer list's code joins numerals of at most 256 bytes with `Nat.lor` and `Nat.shiftLeft`. Elaborating a
numeral costs a few allocations, where a list literal costs a numeral and a constructor per byte; the kernel
computes the list when a check reads it, splitting the code in halves down to words of eight bytes, and the
checks see the same list values.

### Names tied to bytes by equations

A name the extraction states is a `String`; Lean reads the same name as heap bytes. A decision that
compared them would evaluate the string literal in the kernel, about ten thousand heartbeats for each
character, so the comparison is an equation instead: `spelled?` turns bytes into the string they spell as
well-formed UTF-8 in one pass ([KernelEquation](../CIL/Extraction/KernelEquation.lean)), and the tactic
`cil_kernel_rfl` proves `spelled? bytes = some name` by `Eq.refl`, which the kernel accepts when both sides
reduce to the same term. The tactic adds the proof as an auxiliary lemma first, assigns it only after the
kernel accepts it, and otherwise fails at the goal with both sides. `spelled?` agrees with `bytesOf`, the
bytes of a string literal, so the two kinds of comparison in the checker mean the same. Indices, ranges, flags
and blobs stay kernel decisions. The equations cover the owner and base class names of a method
(`MethodNames.Spell`), the method's own assembly against its pin, and each assembly's identity; the method's
signature string is equated the same way.
The checker and the raw-image audit both require a row to fit in 24 bits before forming its
token. This also applies to simple index columns and to rows computed while walking a table.
A method's evidence is a function of the method and its assemblies and of nothing else in the extraction,
so a verified method's component is reused by every extraction that holds the method. The `RVA` column of every carried `MethodDef` row is zero: where a
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
check what the extractor states. A coded index must have a valid table tag and a row number
that fits in 24 bits. Both readers require each signature to consume its entire blob.

Building the lookup trees of a slice costs its size, and the kernel keeps no cache between declarations. The
extractor therefore writes them out as the literal `method{n}Tables` (balanced search trees of the rows, heap
entries, links and instance field counts), and `method{n}_tables_valid` states that `tablesMatch`: the decoder
builds exactly that literal from `method{n}Metadata`. That decision costs the method's carried rows times a
logarithm; `method{n}_body_validated` uses it as a premise. Each closed instantiation of a generic method has
its own copy, built from the open definition and the assembly, so reuse does not depend on which
instantiations an extraction holds or in which order.

A field access carries the `Field` rows of its owner from the first up to the accessed field, and the
owner's and the next type's `TypeDef` rows; rows carried only to be counted keep their flag bytes and name
no heap entry. Lean counts the instance fields before the accessed one over the carried rows, which must
run unbroken from the owner's first field, so a gap fails at the lookup. The total number of instance
fields of a type is recorded only when every field is carried: base classes of a class receiver, the
owner of an instance method, and enums carry their whole field lists.

What `MetadataResolution` and `MetadataBinding` check:

- The scope of every type is the assembly identity its `AssemblyRef` row spells (name, version,
  culture, key token); nested types are named `Outer/Inner`, and the namespace and simple names of a
  type and of each type enclosing it stay apart in the comparison between a reference and its
  definition, so namespace `A.B` with name `C` is not namespace `A` with name `B.C`. A type defined
  in a carried slice has the value type, enum (with its integer type), class or interface kind its
  flags and base give: the base counts as `System.ValueType` or `System.Enum`, and a class's base
  chain ends at `System.Object`, only when the base's own `TypeRef` names a core-library assembly
  (`System.Runtime`, `netstandard`, `mscorlib` or `System.Private.CoreLib`), whatever the slice's
  `corlib` number says.
- A reference whose scope has the name of a pinned assembly, at any version, culture or key token,
  needs the pinned assembly's slice among the method's slices; without it the check fails with
  `missingSlice`, so a pinned type or call, or one of another version of a pinned assembly, is
  never read as a platform one.
- Each `.type`, `.field`, `.call`, `.indirectCall` and string operand of the token table is
  checked against its token. The extractor chooses among `atom`, `object`, `aggregate` and `enum`
  for a type, and Lean accepts the choices that name the same scoped type with a form its kind
  allows. For a closed generic aggregate, the identity must match the resolved instance, and every
  argument must be a primitive value, an enum, a value-like named type or another value-like
  instance whose arguments meet the same rule. Lean rejects an argument it resolves as a class at
  any depth, including when an array or a byref contains the aggregate. For an unpinned platform
  type, Lean trusts the signature's kind marker. A `VALUETYPE` marker can therefore admit a class
  from that assembly as a value argument when the aggregate identity matches.
  An instance field access needs its owner's definition in a carried slice, which gives the
  field's index. Lean also binds the two fields of a platform ``ValueTuple`2`` when its generic
  signature marks the head as a value type and its own `TypeRef` names the supported
  `System.Runtime` assembly with the exact version, culture and public key token.
  The extractor reads the marker on each signature use. Both arguments must use primitive
  element codes for integers, booleans or chars of the same storage width
  (1, 2, 4 or 8 bytes, including 8 for native integers).
  The field references must declare `Item1` as `!0` and `Item2` as `!1`, or the check fails
  with `operandMismatch`. Any other instance field of an owner outside the
  carried slices, and any other member of the pair, fails with `unboundInstanceField`. A static
  field access by `ldsfld`, `ldsflda`, `stsfld` or a field `ldtoken` likewise needs its owner's
  definition in a carried slice and otherwise fails with `unboundStaticField`; the one exception is
  System.Runtime's `BitConverter.IsLittleEndian`, admitted only as an `ldsfld`, which the feature
  check reads as the profile's endianness constant. A static field named through a generic
  instantiation of its owner fails with `instantiatedStaticField`, since each closed instantiation
  has its own storage. The descriptor of the static site at an access must name the instruction's
  field operand as its `field`.
- The decoder records the instruction index and token of each static access whose field a carried
  row defines, and the body must list the same ones (`BodyEvidence.statics`). Over the whole
  program, `StaticIdentitiesValid` requires two static sites to share an identity exactly when
  their tokens name the same `Field` row of the same assembly, so the model's storage keyed by
  identity is one storage per field. Two sorts of the S sites decide it in O(S log S) comparisons,
  and `StaticIdentitiesValid.pairs` states what it guarantees.
  A field's name, index and static flag,
  the generic arguments of a type or method instantiation,
  the full calling-convention byte and parameter and return types before and after generic
  substitution, the definition a member reference resolves to
  in a pinned assembly (its name, its signature and its place in its type's members) and the
  external identity of a call (the scope and Cecil's `result Owner::name(parameters)`) are
  recomputed from the bytes.
  A call to a generic member requires a `MethodSpec` with exactly as many arguments as the
  member declares. A call to a nongeneric member names the member directly.
  At each live modelled call, the runtime model entry also checks the member's open declaration.
  An open declaration distinguishes an owner's `!0` from a method's `!!0` even when both
  instantiate to the same type. The generic vector lane reader must return its method parameter.
  Each Unsafe transfer overload binds the raw target and open declaration to the closed address
  type. The unaligned overloads distinguish a byte reference from a void pointer.
  The entries for Unsafe.As and Unsafe.BitCast bind both method variables. Each resolving site
  must emit its call. The closed parameter of Unsafe.AsRef selects its byref or void-pointer
  declaration and external target. Unsafe.NullRef and Unsafe.IsNullRef each bind their single
  declaration and target. All three names check element storage through the indexed layouts.
- The local variable types are checked against the standalone signature the body header names.
- The method's own identity is checked against four columns of its `MethodDef` row. `Flags` and
  `ImplFlags` must equal the evidence's attributes and implementation flags. The `Signature` blob
  gives the calling convention, generic arity and parameter and return types. `Name`, with the
  signature, gives Cecil's full name of the method, for a generic instance at the type arguments
  its evidence states, and `BodyDecodes` equates it with the evidence's `signature`, the string
  `Extracted.signatures` lists and proofs select the method by. The owner is the `TypeDef` whose
  method range holds the row, and its `GenericParam` rows and the method's give the generic
  parameter counts and flags; a class receiver also checks the class layout facts. A row whose
  flags give it no IL body (abstract, platform invoke, internal call, or a code type other than
  IL) is refused, and so is a runtime-async row (`ImplFlags` 0x2000), whose body returns the
  result its signature states as a task. An `EXPLICITTHIS` method is refused because the model
  requires an implicit receiver outside the parameter list. Instantiation also refuses this
  flag, including for methods decoded directly from raw definitions.
  The `RVA` and `ParamList` columns are not read.
- Generic parameter counts come from `GenericParam` rows. An owner's carried rows must form its
  whole zero-based run. An owner with none carried must be shown to have none by its neighbours in
  the table, which ECMA-335 requires sorted by coded owner: the first carried row above the
  owner's coded value is row 1 or follows a carried row below it, or the table's last row lies
  below it, or the table is empty. A method whose signature lacks the GENERIC flag and that has
  no carried run has none, as ECMA-335 requires of its rows. A `TypeDef` or pinned `TypeRef` that
  names a type alone, a class's base, and the declaring type of a `Field` or `MethodDef` token
  used as an operand have no generic parameters, and the head of a generic instance has one per
  argument. A type outside the carried slices has no rows to count.
- A table or signature form the checker does not read is an explicit error: tables other than
  those the checker names, general arrays, `typedref`, pinned locals and vararg conventions,
  modifiers other than `modreq(InAttribute)` on an `in` parameter and `modreq(IsExternalInit)` on a
  `void` return, forwarded types, module references and `AssemblyRef` rows with a public key flag.
- A custom modifier binds its assembly and full name, including the namespace of each nested
  segment. A local nested `TypeDef` requires its enclosing `NestedClass` rows. A `TypeRef`
  follows its resolution scopes and needs no link to the modifier's definition
  (`modifierNamed` in [MetadataResolution](../CIL/Extraction/MetadataResolution.lean) and the extractor's
  slice collector agree). A type used any other way keeps the link, and a pinned type that does not resolve
  there stops the extraction with `Unresolved pinned type`.

Lean takes on trust that each carried row, heap entry and body is the image's bytes at that position (a wrong
copy cannot be detected without the whole stream; every row must still have the length the header's
widths give, every blob its length prefix and every string one terminating zero), the PE container
where a body sits in the image and the mapping of its address to its bytes, definitions in platform assemblies (so whether a
platform type is an enum, the field order of `ValueTuple`, and that `System.Object` declares no
instance fields), public key tokens (the hash of a key is not computed in the kernel), the
implementation, interface and closure digests that a generic import identity carries (no check
recomputes them from the library image), imported implementation definitions, raw layout
content, dispatch catalog completeness, static data bytes and generic parameter constraints.
[Deep verification](CLI.md#deep-verification) reconfirms each body at its RVA and each carried
row and heap entry, under one numbering of the `#Strings` and `#Blob` offsets per heap and with
MethodDef RVAs zeroed; the assembly identity, key token, core library, links, `#GUID` heap,
`Module` table and the RVAs of MethodDefs outside the evidence are not part of that check. It does
not reconfirm public key tokens or import identities: it reports both as not covered. `check` hashes each assembly and regenerates
the extraction, so the rows are a deterministic function of hashed inputs.
### Folded instruction patterns

A fold applies only to its recognized raw sequence with checked entry edges. Different compiler
output can lose admission without invalidating a theorem over an already admitted program.

| Pattern | Required binding | Limit |
| --- | --- | --- |
| Closed `typeof` equality/inequality calls, reference `ceq` and comparison branches | Exact type handles, runtime helper identities, substituted types, result and selected target; all encoded targets validated and no branch into the interior | Forwarding/scoped identity ambiguities, decorated names and arbitrary runtime `System.Type` use remain unsupported. Reference comparison relies on [CoreCLR runtime type equality](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Type.cs) and [GetTypeFromHandle](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/System.Private.CoreLib/src/System/Type.CoreCLR.cs). |
| `throw new E(...)` | Allowlisted type/constructor, permitted literal/null arguments and final throw; no branch into the interior | No exception-object identity, observable constructor effects, handlers or resource-exhaustion model. |
| `ldnull; throw` | Adjacent operand-free null load and throw, bound to `System.NullReferenceException`; no branch into the throw | No general exception-object evaluation or handlers. |
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
all-successful-fuel refutation; bounds/lifetime examples use `invoke_fault_refutes_success`, which
takes only a definite fault. A failed positive proof, fuel exhaustion or an `unsupported` fault
alone is not a semantic counterexample.

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
The four element-displacement overloads of each of `Unsafe.Add` and `Subtract` and the two
byte-displacement overloads of each of `AddByteOffset` and `SubtractByteOffset` keep their
calls. The closed address and displacement types select one overload. Its open signature and
external MemberRef must match that same overload. The runtime model reads the element shape
from the indexed layouts, including for byte offsets. At a live `Unsafe.ByteOffset<T>` call, the decoder checks the external target, the generic
declaration, both closed reference parameters, the native result and the checked size of `T`.
The site requires the original call. Pointer difference and unsigned ordering require a single
live allocation and assume a contiguous, non-wrapping runtime address interval.
Native displacement arithmetic retains provenance and
readonly restrictions; no ordering between allocation bases is inferred.

Object `ldnull` has a distinct scalar-flow kind. The certificate admits it in truth tests, in
identity comparisons with class instance references, and as a local, argument, call parameter or
return value whose type is a class instance, a supported array or a typed handler table. It is
also admitted as the value of a class-typed field or of a reference-array element. It is never
admitted in a numeric or managed-reference slot, and its comparison with a managed reference is
rejected. The raw literal, comparison operation and branch target remain exactly checked.

Each `ldstr` emits the string literal of exactly its own text, typed as an object; no other raw
opcode emits a literal, and inside a folded `throw` the load emits nothing.

Each argument guard keeps its call. The runtime table binds the open declaration and external
identity to the closed owner, member and parameter types. The type argument determines integer
width and signedness. The scalar certificate requires an object reference for the null guard.

## Exception documentation lint

`lint-exceptions` reports structural potential sites. XML prose is untrusted and not independently
bound to the DLL build. A missing site does not establish exception impossibility. Lint checks no
proof, changes no precondition and issues no verification receipt.
