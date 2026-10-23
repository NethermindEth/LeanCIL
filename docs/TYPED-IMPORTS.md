# Closed method instances and imported struct references

Format 2 contract descriptors carry the exact closed signature, definition
signature, scoped type arguments and signature-scoped raw layout closure. These
fields participate in the canonical sidecar interface hash. Format 1 remains available for ordinary
primitive imports. Generic instances and imported structs cannot use that path.

To extract an exported instance, select the generic definition and supply each
closed primitive integer argument in order:

```text
leancil extract Lib.dll 'Namespace.Library::Identity(T)' artifact --type-argument System.UInt64
```

The producer manifest names the same definition and arguments:

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
the same selection. The existing specialization certificate checks substitution
of the raw method. Import identity includes the complete assembly, generic
instance and fully scoped arguments. An unlisted instance fails even if another
instance of its definition is exported.

App can forward managed references to a reference-free Lib struct, including
`in` and `out` parameters. The selected implementation must define that struct
and its nested aggregate dependencies directly. The interface contains their
ordered field types/names, scope, value-type encoding/base, layout kind, packing,
declared size and offsets. Import admission compares those values with the pinned
DLL metadata. It does not use Cecil's ambient resolver to approve an external
layout. By-value imported aggregates, imported aggregate locals and direct
external field access remain unsupported.

The public catalog is a signature closure, not the full implementation layout
table. Private layouts can occur before or between its entries. The generated
export audit kernel-checks `LayoutProjectionValid`, which reindexes nested
aggregate references, checks raw metadata equality and equates each public
computed layout with its selected implementation layout. The caller's required
`TranslationValid` evidence includes `ImportedLayoutsValid`: exact published and
selected metadata values, `LayoutsValid`, unique identities and complete typed
signature coverage. The existing raw layout algorithm and architecture rules
remain in force.

The new signature boundary rejects open types, generic declaring types,
unsupported constraints, reference type arguments and recursively nested
`modreq`/`modopt` nodes. Ordinary in/out definition flags are retained. A call-site
MemberRef does not encode all definition parameter flags; the checker compares
the actual call-site type encoding and the published flags with the selected
definition. Memory read/write permission and aliasing remain contract obligations.

Verification reports include typed signatures, public layout metadata and type
arguments beside the exact implementation hash. Normal
verification still uses the published-certification trust boundary. Force-full
verification re-extracts the current selected DLL and checks the author,
extraction, relocation and linked caller proof through its existing replay path.
No new method-summary axiom or native proof evaluation is introduced.

`Tests/GenericLayoutImports.cs` builds real Lib/App SDK assemblies. It verifies
the nested `in`/`out` forwarding contract and `Identity<UInt64>`, then checks the
linked claims with full verification. It also exercises a private layout before
the public nested closure, metadata tampering, wrong/open/unlisted instances,
custom modifiers from two assemblies and the canonical format 2 sidecar digest. `Tests/ImportedLayouts.lean` directly checks malformed validator
inputs independently of DLL hashes.
