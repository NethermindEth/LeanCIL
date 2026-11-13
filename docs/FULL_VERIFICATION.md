# Independent imported-library verification

Read this page when a caller proof imports
[published contracts](CONTRACT-INTERFACES.md) and you want the libraries' own proofs re-checked
instead of trusting the publisher's certification. It states what full verification checks, what
it requires of a library's [source bundle](CONSUMERS.md#publishing-verified-contracts) and what
stays trusted.

```text
leancil verify artifact --force-full-verify [--full-artifact Lib=directory]...
```

`--force-full-verify` checks each selected imported
library against its current independently pinned DLL. `--full-artifact Lib=directory`
selects a local copy of the producer's content-addressed source bundle. Its
directory name and complete inventory must match the recorded bundle identity.
Missing, stale or unsupported inputs fail without fallback or `verified.json`.

The assurance levels are:

| Level | Checked result |
| --- | --- |
| Conditional caller theorem | The caller works if its imported contracts hold. |
| Published certification | The caller also records the publisher's implementation/contract assertion. |
| Independent verification | Current library DLLs are re-extracted, author proofs are freshly checked, and actual theorem terms discharge the caller imports in a concrete linked CIL program. |

Full mode uses no proof receipts, portable support or successful proof caches.
It validates source inventory and framework/toolchain bytes, rebases proof
paths into a fresh package and ignores original absolute filesystem locations.
Library exports may depend only on the `leancil` source package. Extra source
packages, static-value assumptions and initialization assumptions fail.

A library export may itself import other libraries. Its fresh extraction is pinned
to the caller's dependency graph nodes. Every export reachable this way is
re-extracted before any library is built; then each bundle is built once, after
the bundles it depends on. Every bundle in the reachable closure is located and
validated before the caller is checked. A missing, changed or failing dependency
bundle fails the run; the dependency's published certification is never used in
its place. The composition proves each dependency's contract on
its own linked program, discharges the importer's `ImportsHold` with those
proofs, and links the importer with its dependencies before linking it into the
caller. The report marks each re-checked `contractDependencies` node with
`acceptedVia` and `sourceBundleDigest`. Package configuration is
generated from the validated source inventory; no Git history is inferred from a
source bundle.

Libraries may read immutable RVA static tables. The fresh extraction decides
each export's reachable tables. Their scoped identities must equal the
certification's, the caller binding's and the bundled extraction's records, and
each must name a field of the library assembly. The three published records are
compared before any build; the fresh extraction is compared with them after it runs. Table bytes
come only from the
fresh extraction, so a re-certified DLL with changed bytes fails the author
proof that ties them to the published `StaticWorldValid` descriptors. The
composed theorem states `linkChecked` for the whole linked program: the
caller's tables and every imported table, including one table read through
several imports, have one descriptor per identity. `StaticWorldValid` premises
remain preconditions of the contracts and of the caller's claim; the composed
theorem does not establish the runtime's static state at the call. Mutable
statics, static constructors and `ldsfld` of constructor-initialized fields
are not supported.

Imports from one source bundle share one staged package and one fresh library
build. The author source first passes the ordinary fresh export, extraction,
closure, statement, axiom and replay checks. The verifier then transfers the
actual checked `LeanCILExportAudit.certified` term and the definitions, theorems
and opaques it depends on into fresh namespaces. It preserves
universe information and renames constant and projection type references.
Every transferred declaration passes `Lean.addDecl` with kernel checking on.
Unsupported user inductives, constructors, recursors and cyclic declarations
fail. A source rename or a matching hash does not prove correctness.

A separate fresh compilation of the regenerated extraction supplies the concrete
program definitions. Kernel proofs check program equality, extraction evidence,
library closure, prefix linking, relocation and `CIL.Safety.composed`. The final
composed theorem uses the actual rechecked library proof terms and caller theorem.
Its independent kernel replay and exact theorem/constant audit share one authenticated native
auditor invocation. If that invocation rejects or is unavailable, the toolchain checker runs
before a separate audit; source, module ownership and axiom checks remain mandatory.
Staging and composition use a temporary directory outside every Lean search
root, so their files cannot shadow a caller or toolchain module.

Building the author source elaborates producer code with the verifier's
privileges: macros, `initialize` and `run_cmd` can read and write any file the
verifier can, start processes, and use the network. Hash checks do not restrict that code.
The verifier snapshots the inputs, caller artifacts and module resolution once
before and once after each run that elaborates producer-derived code. Caller
artifacts are compared by size and modification time rather than hashed. These
snapshots detect accidental mutation only; they omit the trusted toolchain. Run
full verification of an untrusted bundle in an isolated environment: a
read-only toolchain, extractor and caller, no network, and a workspace
discarded afterwards.

Before the first dependency build, the verifier snapshots every staged bundle's
complete file set, including its framework sources and regenerated extraction.
It rechecks the selected bundle immediately before building it, detecting changes
left by an earlier dependency before the later bundle starts. The isolation
requirement still applies to ongoing or hostile producer processes.

Reports retain the original conditional caller theorem and add the composed
theorem and audit, source bundle identities, and `acceptedVia:
independently-verified`. Metadata and token resolution, the PE container, the extractor's translation of instructions
outside the checked families and CIL/runtime correspondence remain trust boundaries of full verification. To reconfirm in the
kernel that the method bodies of an extraction of a library assembly are the bytes of its DLL, run
[`leancil audit-binding`](CLI.md#strict-binding-audit) with the digest of that DLL. These checks
establish CIL theorems. They do not establish correctness of CoreCLR or a JIT.

Imported libraries may depend on each other in any acyclic graph, such as a chain (a caller
importing A, which imports B) or a diamond (a caller importing A and C, which both import B). A
dependency cycle fails the run. A shared dependency has one selected
identity, and each implementation is checked once per run, also when an ordinary proof receipt
for it exists. A named exceptional outcome is preserved through forwarding libraries, and a
table-reading contract through a transitive dependency keeps its explicit `StaticWorldValid`
premise and is covered by the final `linkChecked` composition audit.
