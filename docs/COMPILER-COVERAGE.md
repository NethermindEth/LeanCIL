# Compiler coverage and runtime-model inventory

<!-- audience: maintainers -->

This page describes the checks that pin which compiler output and which runtime calls the
extractor admits, and how to review and record a change to either. Read it when one of these
baselines fails.

The `dispatch` suite checks a pinned source corpus against the latest pinned Roslyn (`5.9.0`) at
`/langversion:latest` using the .NET 11.0.0 reference pack and optimized compilation. Pass
`--all-compilers` (also runnable manually via `.github/workflows/compiler-regression.yml`) to run
the full multi-compiler matrix across Roslyn 4.14.0, 5.0.0 and 5.9.0 at `default`, `14` (where
supported) and `latest`. The default column omits `/langversion`, so it tests the compiler default,
not an SDK-selected language version. Compiler binaries
and reference assemblies come from exact NuGet package versions in
[CompilerToolchain.cs](../Tests/CompilerToolchain.cs).

Run `dotnet run --file Tests/CompilerCoverage.cs` after building the Release extractor.
[Corpus.cs](../Tests/CompilerCorpus/Corpus.cs) covers generic type identity, exception
construction, single-reference span locals, slices, unaligned reads and integer array allocation.
It includes null constructor arguments, branch variants, implicit array-to-span conversions,
span-to-read-only-span conversions and reused span locals. Unsupported floating-point array
allocation is a rejection control. Each supported compiler/language column extracts the
positive methods in one batch and checks the rejection separately. A failed batch fails the
column and triggers individual extractions to report each method's diagnostic. The Lean evidence
validator checks each distinct generated translation across the columns.

`artifacts/CompilerCoverage/coverage.json` records compiler versions and hashes, source hash,
reference-pack version, acceptance and rejection diagnostics.

The whole-corpus scan recompiles the C# sources in `Examples/Assembly`, the contract-import
library and application, and `Tests/NativeProbe` with each compiler/language combination.
The application is scanned a second time, as `ImportFixture.App+ImportFixture.Lib`, with its
library pinned through the blocker manifest's `references`.
It runs the extractor's blocker analysis under the scalar profile over every metadata method,
including constructors and open generic methods. The checked-in
[baseline](../Tests/CompilerCoverageBaseline.tsv) records each method as admitted (`A`),
blocked (`B`) or not checked (`N`) in each column. A missing method is `-`. The gate fails only
when a previously admitted method that still exists in the scan regresses; newly admitted or
removed methods are reported without failing, and `--all-compilers --update` refreshes the full
table. Per-method comparison catches losses even when gains elsewhere leave the accepted count
unchanged. Reports include counts and detailed blocker diagnostics. Admission is extraction
coverage; it is not a correctness proof.
Each compiler/language directory also contains `not-checked.tsv`, listing the method and
selection failure for every `N` entry; console output groups these entries by reason.
An open generic definition is not an entry `extract` accepts, so it is `B`, with that shape as
one of its blockers and its open body analysed behind it; closed callers can still exercise its
specializations. Profile-dependent SIMD coverage is tested
separately and is not measured by this scalar whole-corpus baseline.
This scan does not compile F# or the C# strings and mutated assemblies constructed by test scripts.

The weekly, manually runnable advisory workflow tests the latest stable Roslyn from NuGet
against the latest pinned compiler's admission sets. It reports gains and fails on losses;
it is independent of PR checks. `--latest --whole-only` runs this comparison locally without
Lean certification. `--whole-only` checks the pinned whole-corpus baseline alone.
Neither scan establishes coverage over arbitrary programs or future compiler releases.

Run `dotnet run --file Tests/RuntimeModelInventory.cs` to check the production runtime-call
translator against the pinned reference metadata. The checked-in
[catalog](../Tests/RuntimeModelInventory.txt) contains 473 admitted method definitions in 43
API-owner groups. The fixed primitive domain produces 1,998 admitted closed instances; these are
reported separately so that a generic instantiation does not count as a new definition. The
artifact `artifacts/RuntimeModelInventory/inventory.json` records the complete inventory and
counts by API owner. Additions and removals fail with a diff; after reviewing the model and its
assumptions, update the catalog with `--update`.

The probe covers public methods in System.Runtime, System.Memory and System.Runtime.Intrinsics,
up to one owner type parameter and two method type parameters, instantiated over the fixed
primitive domain in the script. It checks scalar, x64-v4 and arm64-advsimd profiles, and x64-v4 and
arm64-advsimd with their AES capability declared, since no built-in enables AES. It does
not enumerate arbitrary aggregate specializations or separately folded instruction patterns.
Feature and process-width getters handled by `FeatureProfiles` are outside this dispatcher
catalog; their exact signatures and constants are checked by the feature-evidence tests.
The count measures admitted API definitions, not independent semantic assumptions or verified
CLR implementations. Changing the meaning of an existing mapping still requires semantic review
and its targeted proof tests, even when the catalog is unchanged.

The pinned compiler check and inventory run inside the `dispatch` suite. Compiler checks
share reference downloads and batch their Lean evidence checks rather than duplicating runtime
proofs for every compiler.

## Self-admission

The `blockers` suite also runs `leancil blockers` under the scalar profile over every method of
the extractor's own `Nethermind.LeanCIL.dll`, a realistic program that changes with every PR.
[SelfAdmission.cs](../Tests/SelfAdmission.cs) generates the manifest from the built assembly's
metadata and compares the report with the checked-in
[baseline](../Tests/SelfAdmissionBaseline.txt), the list of admitted methods. It needs no Lean; its
opt-in Lean check of every admitted method is described in [validation](VALIDATION.md).

The gate checks admission regressions and ignores blocker totals: it fails only when a method
present in the assembly and admitted in the baseline is no longer admitted. Newly gained admissions
and removed or renamed methods are reported in `artifacts/SelfAdmission/summary.md` and the CI job
summary without failing CI; refresh the baseline periodically with
`dotnet run --file Tests/SelfAdmission.cs -- --update`. The baseline names a
compiler-generated method (a closure, lambda, local function or state machine) by the source
method it was generated for, one line per admitted method, since the compiler numbers it by
positions that unrelated edits shift. Any change to a source compiled into the extractor, or to
the baseline, selects the suite.

The suite also requires the methods the report extracts for admitted entries, its
`decodedMethods`, to be exactly the admitted methods: each admitted method is extracted, and
every method extracted for an admitted entry is itself admitted.

[ExampleAdmission.cs](../Tests/ExampleAdmission.cs) runs `leancil blockers` over every method
`leancil list` prints for the examples assembly, under the `scalar`, `x64-sse42`, `x64-v3`,
`x64-v4` and `arm64-advsimd` profiles at once, and compares the methods each extracts for its
admitted entries, as `<profile> <name>` lines named as the baseline names methods, with the
checked-in [baseline](../Tests/ExampleAdmissionBaseline.txt). A closed generic instantiation an
admitted entry calls is listed with it. A method still in the assembly that leaves the baseline
fails the scan; newly admitted or removed methods are logged without failing and can be recorded
with `dotnet run --file Tests/ExampleAdmission.cs -- --update`. The runs only read the built
extractor, and the check fails if its hash changes while they run.
