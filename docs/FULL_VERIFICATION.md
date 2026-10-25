# Independent imported-library verification

`leancil verify artifact --force-full-verify` checks each selected imported
library against its current independently pinned DLL. `--full-artifact Lib=dir`
selects a local copy of the producer's content-addressed source bundle. Its
directory name and complete inventory must match the recorded bundle identity.
Missing, stale or unsupported inputs fail without fallback or `verified.json`.

The three assurance levels are distinct:

| Level | Checked result |
| --- | --- |
| Conditional caller theorem | The caller works if its imported contracts hold. |
| Published certification | The caller also records the publisher's implementation/contract assertion. |
| Independent verification | Current library DLLs are re-extracted, author proofs are freshly checked, and actual theorem terms discharge the caller imports in a concrete linked CIL program. |

Full mode uses no proof receipts, portable support or successful proof caches.
It validates source inventory and framework/toolchain bytes. It rebases proof
paths into a fresh package and ignores original absolute filesystem locations.
The first version supports closed library exports with the `leancil` source
dependency only. Transitive library imports, extra source packages, static-value
assumptions and initialization assumptions fail. Package configuration is
generated from the validated source inventory; no Git history is inferred from a
source bundle.

Libraries may read immutable RVA static tables. The fresh extraction decides
each export's reachable tables. Their scoped identities must equal the
certification's, the caller binding's and the bundled extraction's records, and
each must name a field of the library assembly. The three published records are
compared before any build; the fresh extraction is compared with them after it
runs. Table bytes come only from the fresh extraction, so a re-certified DLL
with changed bytes fails the author proof that ties them to the published
`StaticWorldValid` descriptors. The composed theorem states `linkChecked` for
the whole linked program: the caller's tables and every imported table,
including one table read through several imports, have one descriptor per
identity. `StaticWorldValid` premises remain preconditions of the contracts and
of the caller's claim; the composed theorem does not establish the runtime's
static state at the call. Mutable statics, static constructors and `ldsfld` of
constructor-initialized fields remain unsupported.

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
Staging and composition use a temporary directory outside every Lean search
root, so their files cannot shadow a caller or toolchain module.

Building the author source elaborates producer code with the verifier's
privileges: macros, `initialize` and `run_cmd` can read and write any file the
verifier can, start processes, and use the network. Hashes cannot contain that.
The verifier snapshots the inputs, caller artifacts and module resolution once
before and once after each run that elaborates producer-derived code. These
snapshots detect accidental mutation only; they omit the trusted toolchain. Run
full verification of an untrusted bundle in an isolated environment: a
read-only toolchain, extractor and caller, no network, and a workspace
discarded afterwards.

Reports retain the original conditional caller theorem. They add the composed
theorem and audit, source bundle identities, and `acceptedVia:
independently-verified`. Faithful DLL decoding and CIL/runtime correspondence
remain trust boundaries. These checks establish CIL theorems, not correctness
of CoreCLR or a JIT.
