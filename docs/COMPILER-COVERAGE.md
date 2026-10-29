# Compiler coverage and runtime-model inventory

The evidence suite checks a pinned source corpus against Roslyn 4.14.0, 5.0.0 and 5.9.0,
using the same .NET 10.0.0 reference pack and optimized compilation. Each compiler runs at its
default language version and at `latest`; compilers supporting C# 14 also run explicitly at `14`.
The default column omits `/langversion`, so it tests the compiler default, not an SDK-selected
language version. Compiler binaries
and reference assemblies come from exact NuGet package versions in
[CompilerToolchain.cs](../Tests/CompilerToolchain.cs).

Run `dotnet run --file Tests/CompilerCoverage.cs` after building the Release extractor.
[Corpus.cs](../Tests/CompilerCorpus/Corpus.cs) covers generic type identity, exception
construction, single-reference span locals, slices, unaligned reads and integer array allocation.
It includes null constructor arguments, branch variants, implicit array-to-span conversions,
span-to-read-only-span conversions and reused span locals. Unsupported floating-point array
allocation is a rejection control. Each supported compiler/language column must accept the
other cases. Accepted translations are checked by the Lean evidence validator; byte-identical
generated evidence is checked once across columns.

`artifacts/CompilerCoverage/coverage.json` records compiler versions and hashes, source hash,
reference-pack version, acceptance and rejection diagnostics.

The whole-corpus scan recompiles the C# sources in `Examples/Assembly`, the contract-import
library and application, and `Tests/NativeProbe` with each compiler/language combination.
It runs the extractor's blocker analysis over every metadata method, including constructors
and open generic methods. The checked-in
[baseline](../Tests/CompilerCoverageBaseline.tsv) records each method as admitted (`A`),
blocked (`B`) or not checked (`N`) in each column. A missing method is `-`. Any difference
requires review; use `--update` to record an intentional change. Per-method comparison catches
losses even when gains elsewhere leave the accepted count unchanged. Reports include counts
and detailed blocker diagnostics. Admission is extraction coverage, not a correctness proof.
This scan does not compile F# or the C# strings and mutated assemblies constructed by test scripts.

The weekly, manually runnable advisory workflow tests the latest stable Roslyn from NuGet
against the latest pinned compiler's admission sets. It reports gains and fails on losses;
it is independent of PR checks. `--latest --whole-only` runs this comparison locally without
Lean certification. `--whole-only` checks the pinned whole-corpus baseline alone.
Neither scan establishes coverage over arbitrary programs or future compiler releases.

Run `dotnet run --file Tests/RuntimeModelInventory.cs` to check the production runtime-call
translator against the pinned reference metadata. The checked-in
[catalog](../Tests/RuntimeModelInventory.txt) contains 340 admitted method definitions in
37 API-owner groups. The fixed primitive domain produces 1,631 admitted closed instances;
these are reported separately to avoid counting each generic instantiation as a new definition.
The artifact `artifacts/RuntimeModelInventory/inventory.json` records the complete inventory
and counts by API owner. Additions and removals fail with a diff; after reviewing the model
and its assumptions, update the catalog with `--update`.

The probe covers public methods in System.Runtime, System.Memory and System.Runtime.Intrinsics,
up to one owner type parameter and two method type parameters, instantiated over the fixed
primitive domain in the script. It checks scalar, x64-v4 and arm64-advsimd profiles. It does
not enumerate arbitrary aggregate specializations or separately folded instruction patterns.
The count measures admitted API definitions, not independent semantic assumptions or verified
CLR implementations. Changing the meaning of an existing mapping still requires semantic review
and its targeted proof tests, even when the catalog is unchanged.

The pinned compiler check and inventory run inside the existing evidence suite. Compiler checks
share reference downloads and batch their Lean evidence checks rather than duplicating runtime
proofs for every compiler.
