# Compiler coverage and runtime-model inventory

The evidence suite checks a pinned source corpus against Roslyn 4.14.0, 5.0.0 and 5.9.0,
using the same .NET 10.0.0 reference pack, C# 13 and optimized compilation. Compiler binaries
and reference assemblies come from exact NuGet package versions in
[CompilerToolchain.cs](../Tests/CompilerToolchain.cs).

Run `dotnet run --file Tests/CompilerCoverage.cs` after building the Release extractor.
[Corpus.cs](../Tests/CompilerCorpus/Corpus.cs) covers generic type identity, exception
construction, single-reference span locals, slices, unaligned reads and integer array allocation.
Unsupported floating-point array allocation is a rejection control. Each compiler must accept
seven cases and reject the control. All accepted translations are checked together by the Lean
evidence validator, reusing the generated-evidence harness.

`artifacts/CompilerCoverage/coverage.json` records compiler versions and hashes, source hash,
reference-pack version, acceptance and rejection diagnostics. This is a small recognizer
regression corpus, not a claim of coverage over arbitrary programs or future compiler releases.
Extend it when adding a compiler-sensitive recognizer; advance compiler pins deliberately.

Run `dotnet run --file Tests/RuntimeModelInventory.cs` to check the production runtime-call
translator against the pinned reference metadata. The checked-in
[catalog](../Tests/RuntimeModelInventory.txt) contains 299 admitted method definitions in
27 API-owner groups. The fixed primitive domain produces 1,579 admitted closed instances;
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

Both checks run inside the existing evidence suite; they add no CI jobs. The compiler checks
share reference downloads and batch their Lean evidence checks rather than duplicating runtime
proofs for every compiler.
