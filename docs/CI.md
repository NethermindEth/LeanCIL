# Verification CI

Regression tests share checked setup where their import and replay requirements agree.
Runtime bit tests [deduplicate identical typed inputs](performance/RuntimeBits.md),
and replay fallback tests check rejection and attribution in one invocation. Independent
metadata mutations, malformed proofs, cache invalidation and native/bootstrap paths remain covered.
Feature-flow mutation tests check their intended validator obligation with
[checked positive controls](performance/EvidenceHarnessReuse.md), avoiding repeated
unrelated certificate proofs.

CI builds the shared test runner and contract-export fixtures once per workflow. Suite jobs
authenticate their manifests and compiled outputs before reuse; source, SDK or runtime changes
fall back to a local build. Assembly mutation tests still rebuild their changed inputs.

The preparation job also publishes its pinned Lean installation as a Zstandard archive.
Suite jobs verify the producer's archive and toolchain-file hashes before restoring executable
permissions and links, avoiding repeated release downloads. The initial installation and its
retry each have a three-minute limit. Failed-suite reruns retain the producer's artifact ID.
The [compression measurements](performance/ToolchainDistribution.md) retain the complete
installation while reducing the archive size and repeated decompression work.

Pushes to `main` and manual runs execute every verification suite. Pull requests
select suites from changed test entry points, referenced proofs, and their
transitive source imports. Markdown and license-only changes skip the expensive
suites. Shared framework, extractor, fixture projects, build configuration,
workflow changes, and unrecognized paths conservatively run the full matrix.

The required `Build and verify` check always runs. It succeeds only when selection
succeeds and every selected suite passes, or when selection explicitly reports
that no suites are needed. Failed or cancelled selection/tests cannot pass it.
Keep this aggregate check required rather than individual matrix jobs, which may
be absent on a PR. Run `dotnet run --file scripts/TestSelectVerification.cs` to test the
selection rules and final gate locally.

The separate scheduled/manual consumer advisory checks a pinned int256 library
and four compiled-method certificates. It does not participate in PR checks.
When upgrading the pin, follow the [consumer API migration notes](CONSUMER-MIGRATION.md)
and validate both the supporting library and those certificates.

The [fixed-consumer performance report](performance/issue270/README.md) separates
historical extraction-certificate costs from consumer proof checking and joint replay.
