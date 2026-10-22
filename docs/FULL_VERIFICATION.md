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
dependency only. Transitive library imports, extra source packages, static sites
and initialization assumptions fail. Package configuration is generated from the
validated source inventory; no Git history is inferred from a source bundle.

The author source first passes the ordinary fresh export, extraction, closure,
statement, axiom and replay checks. The verifier then transfers actual checked
definition/theorem/opaque kernel terms into fresh namespaces. It preserves
universe information and renames constant and projection type references.
Every transferred declaration passes `Lean.addDecl` with kernel checking on.
Unsupported user inductives, constructors, recursors and cyclic declarations
fail. A source rename or a matching hash does not prove correctness.

A separate fresh compilation of the regenerated extraction supplies the concrete
program definitions. Kernel proofs check program equality, extraction evidence,
library closure, prefix linking, relocation and `CIL.Safety.composed`. The final
composed theorem uses the actual rechecked library proof terms and caller theorem.
Source and compiled artifact hashes are rechecked around replay and publication.

Reports retain the original conditional caller theorem. They add the composed
theorem and audit, source bundle identities, and `acceptedVia:
independently-verified`. Faithful DLL decoding and CIL/runtime correspondence
remain trust boundaries. These checks establish CIL theorems, not correctness
of CoreCLR or a JIT.
