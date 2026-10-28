# Export audits and fixture reuse

Contract closures use the replay's checked declaration-owner map. They retain the same
serialization, permitted-declaration checks and recursive axiom inspection. Missing owners
fail closed. Eligible interface validation also reuses that environment; see
[interface replay](ReplayAndEvidence.md). Source-location audits and ambiguous declaration
ownership use imported metadata. Every target declaration undergoes kernel checking.

A Windows comparison alternated the previous and new native auditors three times on the
same compiled contract, including a private definition. Previous times were 3.36, 3.38 and
3.48 seconds; fused times were 1.37, 1.42 and 1.37 seconds. Canonical closure JSON matched
exactly. This small fixture measures the avoided import, not the complete export-suite gain.
`Tests/JointReplay.cs` also compares both paths with private declarations, an untrusted
declaration named under `CIL`, and a rejected axiom dependency. Existing forged-proof,
duplicate-owner, shadowing and source-location regressions remain enabled.

## Repeated test work

- The scaling test checks the complete original extraction through production consumer
  verification, including kernel replay and exact certificate/theorem audits. The
  deliberately monolithic negative control keeps every generated definition and UTF-8
  witness, but omits unrelated proved lemmas. Its one error must be the default-heartbeat
  timeout. The workload contains six methods with 48 operation pairs each, using the
  default heartbeat limit.
- Component-reuse and support-union fixtures batch extraction of their shared assemblies.
  Each output still has its own request, profile and initialization assumptions. Verification,
  cache-corruption controls and both support orders remain independent and unchanged.
  Three paired Windows measurements of the four component extractions took 0.77–0.99s
  separately and 0.21–0.23s batched, with byte-identical generated Lean sources. This is a
  modest setup saving; the consumer proof checks still dominate that fixture.
- The prepared fixture artifact compiles `ModularStaticExports.cs` once alongside the shared harnesses.
  Both suites retain their arguments and assertions. Source, SDK, runtime and output hashes
  still govern reuse; a changed source falls back to compilation.
- Transitive-export tests keep their isolated child traces under the configured trace root,
  making the inner operations available in CI timing artifacts.
