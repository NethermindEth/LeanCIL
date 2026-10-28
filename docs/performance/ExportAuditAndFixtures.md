# Export audits and fixture reuse

Run 40762591714 reduced total workflow time to 27m19s, but the export-profile and
transitive-export suites regressed. Their combined replay/audit operations still loaded
two environments: contract closures requested module ownership metadata, triggering a
full import after kernel replay. The replay environment remained alive during that import.

Contract closures now use the replay's checked declaration-owner map. They retain the same
serialization, permitted-declaration checks and recursive axiom inspection. Missing owners
fail closed. Interface validation, source-location audits and duplicate-declaration cases
still use imported metadata when needed. This does not cache or skip kernel checking.

A Windows comparison alternated the previous and new native auditors three times on the
same compiled contract, including a private definition. Previous times were 3.36, 3.38 and
3.48 seconds; fused times were 1.37, 1.42 and 1.37 seconds. Canonical closure JSON matched
exactly. This small fixture measures the avoided import, not the complete export-suite gain.
`Tests/JointReplay.cs` also compares both paths with private declarations, an untrusted
declaration named under `CIL`, and a rejected axiom dependency. Existing forged-proof,
duplicate-owner, shadowing and source-location regressions remain enabled.

## Repeated test work

- The scaling test previously checked the complete expensive generated prefix, then checked
  the complete original extraction again through production consumer verification. It now
  retains the latter, including kernel replay and exact certificate/theorem audits. The
  deliberately monolithic negative control keeps every generated definition and UTF-8
  witness, but omits unrelated proved lemmas. Its one error must be the default-heartbeat
  timeout. The six-method, 48-operation-pair workload and heartbeat limit are unchanged.
  The removed prefix check cost 84.5 seconds in the referenced CI run; hosted savings need
  confirmation on the new run.
- Component-reuse and support-union fixtures batch extraction of their shared assemblies.
  Each output still has its own request, profile and initialization assumptions. Verification,
  cache-corruption controls and both support orders remain independent and unchanged.
  Three paired Windows measurements of the four component extractions took 0.77–0.99s
  separately and 0.21–0.23s batched, with byte-identical generated Lean sources. This is a
  modest setup saving; the consumer proof checks still dominate that fixture.
- `ModularStaticExports.cs` was compiled separately in two jobs (17.9s and 10.7s in that run).
  The prepared fixture artifact now compiles it once alongside the existing shared harnesses.
  Both suites retain their arguments and assertions. Source, SDK, runtime and output hashes
  still govern reuse; a changed source falls back to compilation.
- Transitive-export tests keep their isolated child traces under the configured trace root,
  making the inner operations available in CI timing artifacts.

## Investigations without retained changes

The other recorded C# fixture-build commands each occurred once. Preparing all of them would
mainly move compilation into the preparation job. A shared verifier assembly could remove
more compiler work, but requires separating the current partial-program harness and preserving
worker dispatch and verifier identity. This change does not assume that migration is free.

The Linux toolchain inventory is dominated by private compiled metadata (1.37 GB), static
libraries (415 MB), interpreter IR (381 MB), ordinary compiled modules (349 MB), and shared
libraries. Lean sources are only 29 MB and editor indexes 88 MB before compression. Retaining
the complete installation preserves interpreted tactics, replay and native consumer builds.
No toolchain files are removed, and the existing measured level-6 compression is unchanged;
see [toolchain distribution](ToolchainDistribution.md).
