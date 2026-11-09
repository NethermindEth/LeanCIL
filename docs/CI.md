# Verification CI

<!-- audience: maintainers -->

Certified libraries travel as authenticated tar/zstd payloads. The archive and manifest digests
come from the same producer job; restoration verifies the archive before decompression and
rejects unsafe entries. Legacy raw artifacts retain their manifest checks. See
[library distribution](performance/LibraryDistribution.md) for the format and measurements.

Library donation first checks this commit, then the ten most recent runs of the same PR whose
heads are ancestors of its current head, nearest first. Both the PR and donor must belong to this
repository; forks and force-pushed nonancestors cannot donate. It then checks an identical merged
PR tree, the exact base-main commit and at most ten recent successful main pushes. This covers a
base run that skipped preparation or has no artifact. A PR or merged-tree run donates when its
prepare job succeeded, even if its suites failed or are still running, since only that job
produces the library. Every candidate still needs that successful producer job, its logged
manifest digest and an artifact with sufficient remaining retention.
A donated library is trusted because our own CI produced it: that run kernel-replayed every
module and logged the manifest digest, and reuse checks that every file matches that digest and
that the manifest binds the current sources and toolchain. Reuse skips kernel replay only when
GitHub metadata shows the donor ran reviewed producer code: a push of a commit reachable from
`refs/heads/main`, or the run of exactly one same-repository PR into main whose head commit leaves
`.github/workflows/verification.yml`, `scripts/` and the root .NET build files as its merge base
with the PR's base commit has them, so the merge it built ran main's producer code. A stacked PR,
a fork, any other run, or unavailable metadata replays the library as a fresh build would; these
checks do not rely on the branch filters of the donor queries. Changed sources use
dependency-aware incremental preparation, which replays every module of the result, or fall back
to a fresh build, which replays everything it built.
A library's identity covers the toolchain, `CIL.lean`, `CIL/`, `lake-manifest.json` and the
library view of `lakefile.toml`, which is the file the library is built from: the checkout
lakefile without blank lines, comments and plain `[[lean_lib]]` tables naming a library outside
CIL. Package settings, dependencies, the `CIL` library, the `leancil-audit` executable and any
library with further keys stay in it. Adding or removing a test library therefore keeps both the
identity and incremental donors; checkout inputs, such as session cache keys, still hash the
complete lakefile. `Tests/LibraryConfiguration.cs` checks both directions.
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

The preparation job installs elan 4.2.4 from its Linux x64 release archive, checking the pinned
SHA-256 before extracting or executing the installer. The archive download retries once after
30 seconds; each download attempt is limited to 150 seconds. The installer uses no moving
installer script or release alias. Lean and Lake resolve the checkout's `lean-toolchain` pin.
The preparation job publishes that installation as a Zstandard archive.
Suite jobs verify the producer's archive and toolchain-file hashes before restoring executable
permissions and links, avoiding repeated release downloads. The Lean toolchain installation and
its retry each have a three-minute limit. Failed-suite reruns retain the producer's artifact ID.
The [compression measurements](performance/ToolchainDistribution.md) retain the complete
installation while reducing the archive size and repeated decompression work.

Pushes to `main` and manual runs execute every verification suite. Pull requests
select suites from changed test entry points, referenced proofs, and their
transitive source imports. Markdown under `docs/` and `skills/` and the README select only the
`docs` suite; other Markdown and license changes skip the suites. Shared framework, extractor,
fixture projects, build configuration,
workflow changes, and unrecognized paths conservatively run the full matrix.

Suites measured at no more than 60 seconds share a job with at most two other short suites,
with a combined measured budget of 120 seconds. The duration table uses verification time,
excluding setup, and unknown suites remain separate. Each member runs in its own process with
its own cache and transcript; a failure does not skip later members, and any member failure
fails the group. Selection still includes exactly the requested suites. This removes repeated
toolchain/library downloads without reducing coverage or increasing concurrent runners.

The `loops` suite covers core loop contracts and class/word-array composition. Generated outline
checks run in `outlines-control`, `outlines-objects` and `outlines-buffers`; each selects its
cases from the shared `Tests/ProofOutlines.cs` runner with `--group`. Each partition prepares
its own extractions and checks its completed proofs and rejection cases. The `structoutlines`,
`receiveroutlines`, `wordreader` and `savedwordreader` suites run their respective focused
fixtures independently. All partitions use the shared certified library and tool artifacts.

Checked stepping rewrites feature and return instructions before using the general dispatcher.
Child invocation matching skips duplicate facts and incompatible literal fuel budgets for
abstract programs. The library and tactic regressions kernel-check the resulting proofs.

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

## Proof cost

A tactic or library change alters the terms proofs build and the work it takes to build them, and
a shorter proof can cost more than the one it replaces. On a pull request the `Proof cost` jobs
measure each proof at the merge base and at the head, on one runner, and put the comparison in the
job summary. The base is the first parent of the PR's merge commit, so main's own changes are never
attributed to the PR, and no checked-in baseline has to be refreshed.

`scripts/ProofCost.cs measure` elaborates a module one command at a time on one thread, through
the frontend `scripts/ProofCost.lean`, and writes one row per command and one per module:

| Measure | Meaning | Decides the result |
| --- | --- | --- |
| Heartbeats | Lean's deterministic work counter for elaborating and kernel-checking the command; `maxHeartbeats` counts thousands of them | yes |
| Olean bytes | size of the compiled module, every part included; module rows only | yes |
| Kernel heartbeats | the kernel alone rechecking the theorems the command declared | no |
| Proof objects | allocated expression objects in those theorems' proof terms | no |
| Lines | source lines of the command or module | no |
| Elapsed ms | wall time of the command; kernel time is in the JSON report | no |

Elapsed time depends on the runner's load, so it is reported and never fails a job. The frontend
checks nothing: a proof is accepted by the verification suites, and a module that reports an error
is listed as not measured.

Each job measures one source on both trees:

- `libraries` measures every test library of `lakefile.toml`, meaning each `[[lean_lib]]` table
  that only names a library, with the checkout modules it imports. It runs when the PR changes a
  Lean file, the lakefile, the toolchain pin or the Lake manifest.
- A proof suite (`core`, `loops`, `outlines-control`, `outlines-objects`, `outlines-buffers`,
  `structoutlines`, `receiveroutlines`, `wordreader`, `savedwordreader`) runs when selection chose
  that suite. The job verifies the suite with each tree's own runner, then measures every output
  directory the suite verified: its `Extracted.lean`, its `Symbols.lean` when present, and the proof
  that `verified.json` names, provided the proof is unchanged since. The extraction's generated
  instruction equations are rows too. A suite that the base does not have, or cannot pass, leaves
  its proofs without a base, with a warning on the job.

The head uses the certified library of the run. The merge base uses the same library when its
library inputs are identical; otherwise `Prepare the merge base for proof cost` builds the base
library with the base's own scripts, incrementally from the head's, and publishes it for the jobs.

`scripts/ProofCost.cs compare` fails when a row's heartbeats grow by more than 5% and by more than
50,000, or a module's olean grows by more than 5% and by more than 4,096 bytes. Both conditions
must hold: 5% of a proof that costs a few thousand heartbeats is not a cost, and a large module
may grow by a small share. Reruns of one tree differ by a few dozen heartbeats in millions and in
no olean byte, as the [measurements](performance/ProofCost.md) record, so the threshold marks what
deserves a reviewer's decision, not noise.

A row is a declaration by its full name, or an unnamed command such as an `example` by its
keyword and a hash of its source, so rows keep their identity when code around them moves.
Smaller changes, improvements, and added, removed, renamed or edited-unnamed rows are reported
only. A module's totals decide only while the module holds the same rows at the base and the
head: a module that gained a proof grew for that reason. A proof measured at the base that cannot
be measured at the head fails, as does a head with nothing measured.

An increase that is worth its cost is accepted by adding it to `scripts/proof-cost-accepted.json`
in the same PR. The summary prints the entry: the row, the measure, the base and head values and a
reason to fill in. An entry applies only to that exact base value and up to that head value, so
it cannot excuse later growth; entries that match nothing are listed for removal and never fail.

The `Proof cost` jobs are separate checks and not part of `Build and verify`, so a regression
shows as a failed check on the PR without blocking a merge the reviewer has accepted. A manual run
of the workflow measures its own tree twice, which reports the runner's measurement noise.

Another producer adds rows by writing the same JSON and passing its file as a further `--base` or
`--head`: a row is a group, a name, a kind and named integer measures. Measures other than the
ones above are reported in their own table and never fail. Each job uploads its measurements,
comparison and suite logs as `proof-cost-<source>`. Run `dotnet run --file scripts/TestProofCost.cs`
to test the comparison rules; [validation](VALIDATION.md#proof-cost) shows a local comparison.

## Documentation checks

A stale document misleads as much as a missing one, so the README, `docs/` and `skills/` are
checked in two places. Selection first runs `dotnet run --file scripts/CheckDocReferences.cs`,
which needs no Lean, so every PR runs it:

- Every relative link, and every link to a file of this repository on GitHub, must resolve, an
  anchor into a Markdown file must name one of its headings, and
  every backticked path under `CIL/`, `Examples/`, `scripts/` or `docs/` must exist with exactly
  that spelling, as a case-sensitive file system resolves it. Build outputs under `bin/` or `obj/`
  are not paths.
- A link whose text is one code span and whose target is a `.lean` or `.cs` file must name
  something that file still contains: a Lean declaration, a declared C# type or member, or a quoted
  string literal such as a test mutation name. A label may also be the file's own path. A link
  whose text names a `.lean` or `.cs` line, or whose target has a `#L` line anchor, fails: cite
  code by name, not by line number.
- Every `bind_*` and `cil_*` command, tactic or attribute named in prose or in an unelaborated
  block must still be declared under `CIL/`.
- Every line of a Lean block, excerpts included, fits in 100 characters, the limit of the
  library's own Lean. An excerpt copies whole lines of its source, so a wide excerpt is
  fixed by wrapping its source.
- A document's audience decides what it may cite. Documents are for users unless they declare
  `<!-- audience: maintainers -->` below their title; maintainers documents describe how LeanCIL
  itself is built, validated and audited (the `VALIDATION*`, `SOUNDNESS-*` detail pages, this page,
  compiler coverage, performance and evidence records). The tool ships `CIL/`, and `Examples/` holds
  complete proofs that the `core` suite verifies end to end; `Tests/` is the repository's own
  regression fixtures, which users cannot import or run. A user document therefore cites no
  `Tests/` path, `Tests.*` module or excerpt of one; it cites an example, states the API in a
  checked snippet, or links the maintainers document that describes the evidence.
- The [suite table](VALIDATION.md#suites) lists each suite `scripts/Test.cs` accepts exactly
  once, as registered in `scripts/VerificationSuites.cs` and `scripts/ExportVerificationSuites.cs`.

Every fenced Lean block is elaborated unless its info string says why not:

| Info string | Check |
| --- | --- |
| `lean` | Elaborated by the `docs` suite against the current library with exactly the block's own imports, as if it were a file of its own: nothing is imported or opened implicitly, so a block starts with `import CIL` or the modules it needs. Imports must name library modules; a block that needs `Extracted` fails until it is marked. |
| `lean excerpt PATH` | The block must be a contiguous range of whole lines of `PATH`, which may be dedented as a block; `PATH` is a file the suites verify, such as an example under `Examples/Proofs`. |
| `lean extracted` | Code that needs a generated `Extracted` module. Its imports and commands are checked statically and its `CIL.` names by the `docs` suite. |
| `lean illustrative` | A shape rather than code to run, checked like `extracted`. |

Any other info string fails. Prefer an elaborated block, then an excerpt of a verified example;
`extracted` and `illustrative` blocks can drift in ways only a reader notices. Never mark a block
to hide an error.

The `docs` suite (`Tests/DocSnippets.cs`) needs the certified library. It writes the elaborated
blocks into one Lean file per distinct import set, so a block sees only the modules it imports, and
the names cited outside elaborated code into a file that imports every library module; the files
elaborate concurrently. Names are probed by these rules:

- A `CIL.`-rooted name in prose or in an unelaborated block must be a declaration or namespace as
  written, unless it is a module path.
- A code span in prose that is wholly a `bind_*` or `cil_*` word must start a tactic, command or
  other syntax, or be an attribute, of the library.
- A code span in prose that is wholly a snake_case word (`invoke_loop_induction`), or a dotted name
  whose first component is capitalised (`LoopFrame.store_field`), must be a declaration, namespace,
  syntax or attribute of the environment, or the suffix of a declaration or namespace of a `CIL`
  module. A dotted name whose part before the last component is no namespace, such as
  `X86.Aes.Encrypt`, is .NET's and not probed; so are names rooted at `Extracted`,
  `ExtractedSymbols`, `Examples`, `Tests` or `System`, file names, and .NET accessor names such as
  `get_Item`, which capitalise after the underscore. A lowercase dotted span such as `entry.memory`
  or `ldind.i` is a term or an opcode, not a name.
- A name that a Lean block of the documentation declares, or binds with `have`, needs no probe; in
  a maintainers document neither does a name declared under `Tests/`, which its own suite checks.

Each diagnostic, warning or `sorryAx` is reported at the document line it came from. The suite then
checks that a pre-`Except` `invoke` statement, a removed or renamed name, a removed tactic and a
block using a module it does not import each fail at their own lines, while the current forms and
names outside the library pass. Run it locally with
`dotnet run --file scripts/Test.cs -- --suite docs`; `scripts/TestCheckDocReferences.cs` tests the
static rules.

## Other workflows

The ARM64 AES workflow runs only `Tests/AesHardware.cs` and the runtime probe on a macOS Apple
silicon runner, for changes to the AES model, its hardware check, the probe or the macOS evidence;
see [runtime profiles](RUNTIME-PROFILES.md). The x64 suites check x86 AESENC.

Downstream libraries check their own compatibility with LeanCIL in their own CI, pinning a
LeanCIL revision and advancing it through a reviewed change; LeanCIL's checks build no consumer.
