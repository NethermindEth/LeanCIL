# Verification CI

Certified libraries travel as authenticated tar/zstd payloads. The archive and manifest digests
come from the same producer job; restoration verifies the archive before decompression and
rejects unsafe entries. Legacy raw artifacts retain their manifest checks. See
[library distribution](performance/LibraryDistribution.md) for the format and measurements.

Library donation first checks this commit, then up to ten successful runs of the same PR whose
heads are ancestors of its current head. Both the PR and donor must belong to this repository;
forks and force-pushed nonancestors cannot donate. It then checks an identical merged PR tree,
the exact base-main commit and at most ten recent successful main pushes. This covers a base
run that skipped preparation or has no artifact. Every candidate still needs a successful
producer job, its logged manifest digest and an artifact with sufficient remaining retention.
Source/toolchain checks and kernel replay remain mandatory; changed sources use dependency-aware
incremental preparation or fall back to a fresh build.
Transient HTTP failures (408, 429, 500, 502, 503 and 504) receive at most two retries, after
one and two seconds. An unavailable listing, job, artifact or log skips that candidate rather
than aborting the search. Failed responses never supply evidence, and a candidate still needs
both its own valid artifact and its producer's digest. If no candidate qualifies, CI builds fresh.

Regression tests share checked setup where their import and replay requirements agree.
Runtime bit tests [deduplicate identical typed inputs](performance/RuntimeBits.md),
and replay fallback tests check rejection and attribution in one invocation. Independent
metadata mutations, malformed proofs, cache invalidation and native/bootstrap paths remain covered.
Feature-flow mutation tests check their intended validator obligation with
[checked positive controls](performance/EvidenceHarnessReuse.md), avoiding repeated
unrelated certificate proofs.

CI builds the shared test runner, group runner, archive helper and contract-export fixtures once
per workflow. Suite jobs authenticate the producer's checksum list before running the archive
helper, which reports authentication, extraction and publication time separately. Suite jobs
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

Suites measured at no more than 60 seconds share a job with at most two other short suites,
with a combined measured budget of 120 seconds. The duration table uses verification time,
excluding setup, and unknown suites remain separate. Each member runs in its own process with
its own cache and transcript; a failure does not skip later members, and any member failure
fails the group. Selection still includes exactly the requested suites. This removes repeated
toolchain/library downloads without reducing coverage or increasing concurrent runners.

The duration table uses the slower verification step from runs `40746599661` and `40734844413`.
It produces 48 jobs for the current 66 suites. Applying those groups to the latest run's setup
times, retaining the slowest setup in each group, estimates 996 fewer runner-seconds. Network
variation and the job dependency graph mean this is not a wall-clock guarantee.

Reference-interpreter stepping rewrites feature and return instructions directly before using
the general dispatcher. The three `LegacyFeatures` proofs fell from about 23 seconds to 3–4
seconds locally. Child invocation matching skips duplicate facts and incompatible literal fuel
budgets for abstract programs; `ContractCalls` fell from about 12 seconds to 3.3 seconds. These
are Windows measurements with compiled imports; the full library and tactic regressions still
kernel-check the resulting proofs.

Single-request contract exports combine declaration replay with the complete theorem, constant
and closure audit. Source and artifact checks still surround the export callback. External-call
mutation fixtures check only the intended division/intrinsic validator, with a complete positive
certificate and a checked unchanged-obligation control in the replayed evidence batch.

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
