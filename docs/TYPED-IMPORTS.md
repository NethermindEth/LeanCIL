# Closed method instances and imported struct references

Read this page to export or import a contract for a closed generic method instance, or for a
method that takes references to a struct the library defines. It extends
[contract interfaces](CONTRACT-INTERFACES.md), which covers imports over primitive types.

Format 2 contract descriptors carry the exact closed signature, definition
signature, scoped type arguments and signature-scoped raw layout closure. These
fields participate in the canonical sidecar interface hash. Format 1 covers ordinary
primitive imports; generic instances and imported structs require format 2.

To extract an exported instance, select the generic definition and supply each
closed primitive integer argument in order:

```text
leancil extract Lib.dll 'Namespace.Library::Identity(T)' artifact --type-argument System.UInt64
```

The producer's [export manifest](CONSUMERS.md#publishing-verified-contracts) names the same
definition and arguments:

```json
{
  "method": "Namespace.Library::Identity(T)",
  "typeArguments": ["System.UInt64"],
  "artifact": "artifact",
  "contract": "Published.identity",
  "theorem": "Author.correctness"
}
```

The artifact records the definition, ordered arguments and actual specialized
entry. Export preparation, integrity checking and full verification reconstruct
the same selection. The specialization certificate checks substitution
of the raw method. Import identity includes the complete assembly, generic
instance and fully scoped arguments. An unlisted instance fails even if another
instance of its definition is exported.

App can forward managed references to a reference-free Lib struct, including
`in` and `out` parameters. The selected implementation must define that struct
and its nested aggregate dependencies directly. The interface contains their
ordered field types/names, scope, value-type encoding/base, layout kind, packing,
declared size and offsets. Import admission compares those values with the pinned
DLL metadata. It does not use Cecil's ambient resolver to approve an external
layout. By-value imported aggregates and direct external field access are not
supported.

App can also declare a local of such a struct and pass its address on, as
`Library.Copy(in source, out var middle); Library.Copy(in middle, out destination)`
does. The interface must publish the struct's whole layout closure with values
equal to the pinned DLL metadata, and a call bound in the same extraction must
carry that closure in its typed signature. The local is admitted only by
address: `ldloc`, `stloc`, `initobj` and field access through it are rejected, so
its bytes never cross the App's evaluation stack. The extractor never resolves an
external field, so `ldflda` on the local fails resolution; a zero-initialized
`Pair value = default` is rejected at its `initobj`. Its layouts join the App's layout table,
computed from the selected module, and `ImportedLocalLayoutsBound` in
`TranslationValid` requires each such entry to equal the selected layout of every
slot that publishes its identity. Imported entries carry no interfaces, so they
cannot satisfy a generic constraint.

The public catalog is a signature closure, not the full implementation layout
table. Private layouts can occur before or between its entries. The generated
export audit kernel-checks `LayoutProjectionValid`, which reindexes nested
aggregate references, checks raw metadata equality and equates each public
computed layout with its selected implementation layout. The caller's required
`TranslationValid` evidence includes `ImportedLayoutsValid`: exact published and
selected metadata values, `LayoutsValid`, unique identities and complete typed
signature coverage. The raw layout algorithm and architecture rules
apply unchanged.

The typed signature boundary rejects open types, generic declaring types (an extraction entry may
be a static method of a generic class, but such a method cannot be exported or imported),
unsupported constraints, reference type arguments and recursively nested
`modreq`/`modopt` nodes, including the `modreq(InAttribute)` that entry selection admits on
`in` parameters of virtual members and the `modreq(IsExternalInit)` it admits on `init`
accessor returns. Contract methods are static and non-virtual, and C# emits those modifiers only
on virtual members, private explicit implementations and instance `init` accessors, so no
exported or imported identity can differ from another only in a modifier. Ordinary in/out
definition flags are retained. A call-site
MemberRef does not encode all definition parameter flags; the checker compares
the actual call-site type encoding and the published flags with the selected
definition. Memory read/write permission and aliasing remain contract obligations.

Verification reports include typed signatures, public layout metadata and type
arguments beside the exact implementation hash. Normal
verification uses the published-certification trust boundary.
[Full verification](FULL_VERIFICATION.md) re-extracts the current selected DLL and checks the
author, extraction, relocation and linked caller proof through its replay path.
Typed imports add no method-summary axiom and no native proof evaluation.

A typed import keeps the callee behind its contract. To extract the callee's body instead, pass
its DLL as a [pinned reference](CLI.md#extract-from-referenced-assemblies). The two are exclusive
per assembly: a sidecar for a pinned assembly is not discovered, and an explicit `--import` of
a pinned assembly is rejected.

The repository's `exportstyped` suite checks these rules on SDK-built Lib/App assemblies,
including the rejected cases above; see [validation](VALIDATION.md).
