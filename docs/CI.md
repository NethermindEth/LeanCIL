# Verification CI

<!-- audience: maintainers -->

This page describes how `.github/workflows/verification.yml` selects and runs the
[verification suites](VALIDATION.md#suites), how the certified library, toolchain and tools reach
the suite jobs, and what the proof-cost and documentation checks enforce. Read it before changing
the workflow, the selection scripts or a documentation marker.

## Jobs

All jobs run on `ubuntu-24.04`. A newer run on the same ref cancels the one in progress. Uploaded
artifacts are kept for 14 days.

| Job | Name | Limit | Does |
| --- | --- | --- | --- |
| `select` | `Select verification suites` | 5 minutes | Runs the static documentation check and the script self-tests, then selects suites and proof-cost sources |
| `prepare` | `Prepare certified Lean library` | 20 minutes | Installs the toolchain and reuses or builds the [certified library](#certified-library) |
| `tools` | `Build extractor, examples and shared fixtures` | 10 minutes | Builds the tools every suite job restores |
| `suites` | `Verify (<suites>)` | 30, 90 or 120 minutes | Runs one group of suites; at most eight jobs run at once |
| `proof-cost` | `Proof cost` | 10 minutes | Compares or publishes [proof cost](#proof-cost) rows |
| `verify` | `Build and verify` | 5 minutes | The [required check](#required-check) |

`prepare`, `tools` and `suites` are skipped when selection reports that no suite is needed.

## Suite selection

Pushes to `main` and manual runs execute every suite. A pull request runs the suites that own a
changed file. A suite owns its entry script and, transitively, the `Tests/` and `Examples/` sources
that script names, its file-based includes and the Lean modules those import.

| Changed path | Suites selected |
| --- | --- |
| `README.md`, Markdown under `docs/` or `skills/` | `docs` only |
| Other Markdown, `LICENSE` | none |
| A workflow file other than `verification.yml` | none; that workflow runs its own jobs |
| `CIL/`, `Extractor/`, `Examples/Assembly/`, `Examples/FSharp/`, `Tests/Support.lean`, `scripts/ExportVerificationSuites.cs`, a script compiled into the extractor | all |
| A file some suite owns | its owners |
| Any other path, including `verification.yml` and build configuration | all |

The `docs` suite also owns each example file that a `sh run` block names. Selection includes
exactly the selected suites: grouping them into jobs adds none. Test the selection rules and the
final gate locally with `dotnet run --file scripts/TestSelectVerification.cs`; it needs no Lean
build or fixture SDK project.

## Required check

The required `Build and verify` check always runs. It succeeds only when selection
succeeds and every selected suite passes, or when selection explicitly reports
that no suites are needed. Failed or cancelled selection/tests cannot pass it.
Keep this aggregate check required rather than individual matrix jobs, which may
be absent on a PR.

## Suite jobs

Every job spends about a minute on checkout, toolchain, library and tool restores and uploads
before and after its suites, so suites are packed into as few jobs as a target allows. The target
is one runner's share of a round: the measured time of all suites divided by the eight runners
and by the fewest rounds that keep a job no longer than the longest suite, which is two rounds with
the checked-in durations. The longest suite is then the longest job and the runners finish
together. Suites go longest first into the fullest job that still has room, at most eight to a job,
and jobs start longest first. The matrix runs at most eight jobs at once; the runners are shared,
so do not raise that limit.

- The duration table `scripts/verification-durations.json` holds verification time, excluding
  setup, which a job's summary and each member's transcript report per suite. A suite without a
  measured time runs alone.
- `dotnet run --file scripts/EstimateVerificationSchedule.cs -- --jobs` prints the jobs of a full
  run with their estimated minutes.
- A job's time limit is the largest of its members': 90 minutes for `imports`, 120 for each
  `exports` partition and 30 for any other suite.
- A job is named for its suites, or for its longest suite and the number of others when it runs
  more than three, so job names change when the durations do. Only `Build and verify` is a stable
  check name.

Each member of a job runs in its own process with its own cache, transcript and trace label, in
the checkout a full local run shares between all suites. A failure does not skip later members,
and any member failure fails the job. The log folds each member's output under its name, a failed
member raises an error annotation that names it, and the job summary lists every member with its
result and time.

The generated outline checks run in `outlines-control`, `outlines-objects` and `outlines-buffers`.
Each selects its cases from the shared `Tests/ProofOutlines.cs` runner with `--group`, prepares its
own extractions and checks its completed proofs and rejection cases; `--case name[,name...]`
narrows a local run to the named cases of that group. `loops`, `structoutlines`,
`receiveroutlines`, `wordreader` and `savedwordreader` each run their own fixture.

## Certified library

The `prepare` job provides one kernel-replayed `CIL` library per workflow attempt and passes its
artifact ID, the run that uploaded it, its archive digest and its manifest digest to the suite jobs
as job outputs. A rerun of failed suite jobs keeps the producer's artifact ID.

### Donors

`scripts/FindCertifiedLibrary.cs` looks for a library that an earlier run certified, in this
order:

1. Runs of this commit.
2. On a pull request: the ten most recent runs of the same PR whose heads are ancestors of its
   current head, nearest first. The PR and the donor must belong to this repository; forks and
   force-pushed nonancestors cannot donate.
3. On a push: runs of at most ten merged PRs of this repository whose merge commit is this push and
   whose complete Git tree matches it exactly.
4. The `main` push of the checkout's first parent.
5. At most ten recent successful `main` pushes, for a base run that skipped preparation or has no
   artifact.

A candidate needs a successful `prepare` job, the manifest digest that job logged, and an artifact
with at least a day of retention left. A PR or merged-tree run donates even if its suites failed or
are still running, since only the `prepare` job produces the library. The digest is read from the
donor job's log, never from the artifact.

Transient HTTP failures (408, 429, 500, 502, 503 and 504) get at most two retries, after one and
two seconds. An unavailable listing, job, artifact or log skips that candidate instead of aborting
the search, and a failed response never supplies evidence. If no candidate qualifies, CI builds
from source.

### Reuse and replay

`scripts/PrepareLibrary.cs --reuse` rechecks the library key, the source binding and every file
against the donor's logged manifest digest. A donated library is trusted because this repository's
CI produced it: that run kernel-replayed every module and logged the digest.

Reuse skips kernel replay (`--producer-replayed`) only when GitHub metadata shows the donor ran
reviewed producer code:

- a push of a commit reachable from `refs/heads/main`, or
- the run of exactly one same-repository PR into `main` whose head commit holds the same Git
  objects as its merge base with the PR's base commit at every
  `CertifiedLibraryDonor.ProducerPaths` entry: `.github/workflows/verification.yml`, `scripts/` and
  the root .NET build files. The merge that run built therefore ran `main`'s producer code.

A stacked PR, a fork, any other run or unavailable metadata replays the library as a fresh build
does; a PR that changes the workflow or `scripts/` can log a digest for a forged library, so any
reuse of it replays. These checks do not rely on the branch filters of the donor queries.

When reuse fails and a donor was restored, CI tries `--incremental`, which authenticates every
donor file, rebuilds what the changed sources affect and kernel-replays every module of the
result. If that fails, or there is no donor, CI builds from source and replays everything.
[Certified library preparation](VALIDATION-COVERAGE.md#certified-library-preparation) describes
the `PrepareLibrary.cs` modes and their tests.

CI does not restore compiled libraries from the GitHub Actions cache: a cache's source key and
self-described file hashes cannot authenticate the native auditor or establish that compiled
modules came from those sources.

### Identity

A library's identity covers the toolchain, `CIL.lean`, `CIL/`, `lake-manifest.json` and the library
view of `lakefile.toml`, which is the file the library is built from: the checkout lakefile without
blank lines, comments and plain `[[lean_lib]]` tables naming a library outside CIL. Package
settings, dependencies, the `CIL` library, the `leancil-audit` executable and any library with
further keys stay in it. Adding or removing a test library therefore keeps both the identity and
incremental donors; checkout inputs, such as session cache keys, hash the complete lakefile.
`Tests/LibraryConfiguration.cs` checks both directions.

### Publication and transfer

A run uploads the library it built. A `main` push also uploads after exact reuse, so that it stays
a donor for later PRs without a chain of earlier runs. Suite jobs take the current run's artifact
when it uploaded one; a PR run that reused a donor takes that donor's artifact directly.

A library travels between jobs as one authenticated tar/zstd archive;
[library distribution](performance/LibraryDistribution.md) defines the format, the restore checks
and how to measure them. A donor artifact stored as raw files, with no archive digest, is checked
against its manifest.

`scripts/TestFindCertifiedLibrary.cs` covers `main` pushes, unchanged and changed PR producer
paths, non-main bases, forks, PR entry and head mismatches, unreachable pushes, ambiguous main
refs, unknown merge bases and other runs.

## Toolchain and shared tools

The `prepare` job installs elan 4.2.4 from its Linux x64 release archive and checks the pinned
SHA-256 before extracting or executing the installer; it uses no moving installer script or
release alias. The archive download retries once after 30 seconds, and each attempt is limited to
150 seconds. Lean and Lake resolve the checkout's `lean-toolchain` pin; the toolchain installation
and its one retry, 30 seconds later, each have a three-minute limit.

The job publishes that installation as a Zstandard archive holding the complete installation.
Suite jobs verify the producer's archive hash and the `lean-toolchain` file hash before restoring
executable permissions and links, so they download no release.
[Toolchain distribution](performance/ToolchainDistribution.md) gives the archive command and
reference figures for its size and restore time.

The `tools` job builds the extractor and example assembly, the shared test runner, group runner,
archive helper, proof-cost tool and contract-export fixtures once per workflow. Suite jobs
authenticate the producer's checksum list before running the archive helper, which reports
authentication, extraction and publication time separately, and authenticate the fixture manifest
and compiled outputs before reuse. A source, SDK or runtime change falls back to a local build, and
assembly mutation tests rebuild their changed inputs. The
[coverage page](VALIDATION-COVERAGE.md#preparation-and-shared-infrastructure) describes the
fixture identity.

## Proof cost

A tactic or library change alters the terms proofs build and the work it takes to build them, and
a shorter proof can cost more than the one it replaces. On a pull request the `Proof cost` job
compares what each proof costs at the head with what `main` measured at the merge base and puts
one table per source in its summary. The base is the first parent of the PR's merge commit, so
`main`'s own changes are never attributed to the PR, and there is no checked-in baseline.

### Measures

`scripts/ProofCost.cs measure` elaborates a module one command at a time on one thread, through
the frontend `scripts/ProofCost.lean`, and writes one row per command and one per module:

| Measure | Meaning | Decides the result |
| --- | --- | --- |
| Heartbeats | Lean's work counter for elaborating and kernel-checking the command, the unit `maxHeartbeats` limits in thousands; reruns agree to within a few dozen | yes |
| Olean bytes | size of the compiled module, every part included; module rows only | yes |
| Kernel heartbeats | the kernel alone rechecking the theorems the command declared | no |
| Proof objects | allocated expression objects in those theorems' proof terms | no |
| Lines | source lines of the command or module | no |
| Elapsed ms | wall time of the command; kernel time is in the JSON report | no |

Elapsed time depends on the runner's load, so it is reported and never fails a job. The frontend
does not certify proofs: a proof is accepted by the verification suites. An error in any command
or nested elaboration snapshot makes the module unmeasured; later successful commands cannot
erase it. Expected diagnostics consumed by `#guard_msgs` do not count as errors. Auxiliary
theorems contribute to the declaring command's kernel heartbeats and proof objects.

A row is a declaration by its full name, or an unnamed command such as an `example` by its
keyword and a hash of its source, so rows keep their identity when code around them moves.

### Sources

A source is measured on each tree by the run that verifies it:

- `libraries` is every test library of `lakefile.toml`, meaning each `[[lean_lib]]` table that
  only names a library, with the checkout modules it imports. It is compared when the PR changes
  a Lean file, the lakefile, the toolchain pin or the Lake manifest.
- A proof suite (`core`, `loops`, `outlines-control`, `outlines-objects`, `outlines-buffers`,
  `structoutlines`, `receiveroutlines`, `wordreader`, `savedwordreader`) is compared when
  selection chose that suite. Its rows are every output directory the suite verified: its
  `Extracted.lean`, its `Symbols.lean` when present, keyed re-export modules imported by the
  proof, and the proof that `verified.json` names, provided the proof is unchanged since.
  Package-local imports are resolved through Lake and measured with the proof; their source bytes
  and package configuration must match its verified inputs. Missing or changed support is
  reported as unmeasured. Each extracted method's instruction equations are one row, named for
  its `cil_instruction_equations` command. A directory is measured only while it holds the report
  of an accepted proof, so a suite that also checks rejected proofs against an extraction verifies
  the accepted one last.

### Where rows are measured

The head is measured where it is verified, in no job of its own. A `Verify` job that ran a proof
suite measures that suite once it has passed. A suite's rows are the output directories it owns,
which `VerificationSuites.ProofOutputs` declares, so a suite that shares its job with others is
measured alone. Before measuring, the job checks that ownership accounts for everything it
verified: the group runner records when each member started, and an owned directory whose report
another member wrote, or a report a proof suite wrote outside its directories, stops the
measurement of the suites involved. A proof suite that gains an output directory declares it
there. The shortest `Verify` job also measures `libraries`, which needs only the certified
library. Neither step can fail its job: a source without rows fails the comparison instead.

A run measures only its own tree. A push to `main` measures every source, and its `Proof cost` job
gathers those that hold rows into one artifact and logs its digest; a suite that failed on `main`,
or left no rows, is not among them, and the rows of the suites that passed are. A PR run takes
those rows as its base when the push run of its merge base published them: the run must be a push
of that commit on `main`, which is what reusing a certified library without replay requires of its
producer, the file must have the digest that job logged, and its rows must come from the same
measurer and from that commit. The measurer is `scripts/ProofCost.lean`,
`scripts/ProofCostReport.cs`, the shared selection helpers in `scripts/Verification.cs`, the row
schema and the two workflow steps that measure. No other run supplies a base, and no pull request
run measures one.

### Comparison

`Proof cost` waits for the suites and measures nothing: on a pull request it downloads the head's
rows and the published rows and compares every source before it fails for any of them.

| Case | Result |
| --- | --- |
| A row's heartbeats grow by more than 5% and by more than 50,000 | fails |
| A module's olean grows by more than 5% and by more than 4,096 bytes | fails |
| A proof measured at the base cannot be measured at the head | fails |
| A source has a published base and no head rows, or the head has nothing measured | fails |
| Smaller changes, improvements, and added, removed, renamed or edited-unnamed rows | reported only |
| `main` published no rows for the source | reported as `No rows published for merge base <commit>; not compared`; does not fail |

Both conditions of a threshold must hold: 5% of a proof that costs a few thousand heartbeats is
not a cost, and a large module may grow by a small share. Reruns of one tree differ by a few dozen
heartbeats in millions and in no olean byte, as the [measurements](performance/ProofCost.md)
record, so the threshold marks what deserves a reviewer's decision, not noise. A module's totals
decide only while the module holds the same rows at the base and the head: a module that gained a
proof grew for that reason.

`main` has published no rows while the push run of the merge base is running or was cancelled,
when the PR changes the measurer, and for the parent branch of a stacked pull request. That is the
only way to pass without a comparison.

`Proof cost` is a separate check and not part of `Build and verify`, so a regression shows as a
failed check on the PR without blocking a merge the reviewer has accepted. A manual run of the
workflow on a commit `main` has published compares that tree with `main`'s rows for it, which
reports the measurement noise between two runs.

### Accepting an increase

Accept an increase that is worth its cost by adding it to `scripts/proof-cost-accepted.json` in
the same PR. The summary prints the entry: the row, the measure, the base and head values and a
reason to fill in. An entry applies only to that base value and up to that head value, each with
1,000 heartbeats of allowance for the difference between reruns, so it cannot excuse later growth;
entries that no source of the run matched are listed for removal and never fail.

### Other producers and local runs

Another producer adds rows by writing the same JSON and passing its file as a further `--base` or
`--head` of `compare`: a row is a group, a name, a kind and named integer measures. Measures other
than the ones above are reported in their own table and never fail. The job uploads the head's
rows, the published rows and each source's comparison as `proof-cost`. Run
`dotnet run --file scripts/TestProofCost.cs` to test the comparison rules;
[validation](VALIDATION.md#proof-cost) shows a local comparison.

## Documentation checks

The README, `docs/` and `skills/` are checked in two places: a static check that every PR runs,
and the `docs` suite.

### Static check

Selection runs `dotnet run --file scripts/CheckDocReferences.cs`, which needs no Lean:

- Every relative link, and every link to a file of this repository on GitHub, must resolve, an
  anchor into a Markdown file must name one of its headings, and
  every backticked path under `CIL/`, `Examples/`, `scripts/` or `docs/` must exist with exactly
  that spelling, as a case-sensitive file system resolves it. Build outputs under `bin/` or `obj/`
  are not paths.
- A link whose text is one code span and whose target is a `.lean` or `.cs` file must name
  something that file contains: a Lean declaration, a declared C# type or member, or a quoted
  string literal such as a test mutation name. A label may also be the file's own path. A link
  whose text names a `.lean` or `.cs` line, or whose target has a `#L` line anchor, fails: cite
  code by name, not by line number.
- Every `bind_*` and `cil_*` command, tactic or attribute named in prose or in an unelaborated
  block must be declared under `CIL/`.
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
- No `simp`, `simp only`, `simpa`, `simp_all` or `dsimp` list of an example under
  `Examples/Proofs`, or of a Lean block that is not an excerpt, names one of the interpreter's own
  functions: `step`, `run`, `invoke`, `pureArity`, `scalars`, `instructionStep`,
  `staticInstruction`, `checkedIntrinsic`, `checkedValue`, `numericValue`, `checkedAt`,
  `formValue`, `storeValue`, `instruction`, `memoryInstruction`, `otherMemoryInstruction`,
  `observerCount`, `unspecifiedOperands` or `hasUnspecified`, or the monad plumbing
  `Except.mapError`, `Bind.bind`, `Except.bind`, `Pure.pure` or `Except.pure`, by any suffix of its
  full name. Such a proof runs the method by unfolding the interpreter; step with
  `cil_checked_steps` and pass a fact about the operation instead. A name the block binds with
  `have` is a hypothesis.
- Every theorem of an example under `Examples/Proofs` has a `#print axioms` line in its file.
- The consumer proof fixture imports only `CIL`, uses no interpreter dispatch or value-check
  implementation helpers, and prints every theorem's axioms. Its elaboration in `core` checks
  named call evidence and the goal forms described by the
  [public proof surface](PROOFS.md#public-proof-surface).
- A document declares at most one audience, `users` or `maintainers`, and closes every code
  fence. A Lean block's info string starts with exactly `lean`; another spelling of it fails.

### Lean blocks

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

### The docs suite

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
checks that an `invoke` statement whose result is not an `Except`, a removed or renamed name, a
removed tactic and a block using a module it does not import each fail at their own lines, while
the current forms and names outside the library pass.

### Documented commands

Documented commands and their output are checked the same way. A block is part of its document's
walkthrough when its info string marks it:

| Info string | Check |
| --- | --- |
| `sh run` | The `docs` suite runs each line as a command, in document order, and each must exit with `0`. Only `leancil` and `dotnet build Examples/...` commands are run; other commands stay in an unmarked `sh` block. |
| `sh run fails` | As `sh run`, except that the last command must exit with a failure. |
| `text stdout` | The whole standard output of the last command run above it. A line `...` stands for any run of lines. |
| `text stderr` | Lines that the standard error of that command holds in a row, such as the start of a diagnostic. |
| `csharp edit PATH` | Each line replaces the one line of `PATH`, a file under `Examples/`, that declares the same expression-bodied member; the commands after it see the edit. |

Any other word after `sh`, `text` or `csharp` fails, as does a command the suite does not run, a
`sh run` block with no command, an output block with no command above it and an edit that names
no single line;
`scripts/CheckDocReferences.cs` checks these on every PR. The suite runs each document's commands
from a copy of the example sources they name, with `leancil` being the tool built from the
checkout, so an edit never touches the checkout and a path prints as in the document. Before
comparing, it replaces each SHA-256 and each `line:column` after a `.lean` or `.cs` file name on
both sides, since those vary with the machine or an unrelated edit. A documented line the tool
does not print, a printed line the document lacks and a command that exits otherwise than marked
each fail at the document line. The suite then replays the getting-started walkthrough with a
label the tool does not print, a line removed and an altered error line, and requires each to
fail at its line. A change to a tool source or to an example file a `sh run` block names selects
the suite.

Run it locally with `dotnet run --file scripts/Test.cs -- --suite docs`;
`scripts/TestCheckDocReferences.cs` tests the static rules and the output comparison.

Separately, the `Countdown` case of the `outlines-control` suite fails unless the first
`lean extracted` block of `docs/CLI.md` that starts by importing an extraction is, byte for byte,
the generated `Countdown` proof outline.

## Other workflows

The ARM64 AES workflow runs only `Tests/AesHardware.cs` and the runtime probe on a macOS Apple
silicon runner, for changes to the AES model, its hardware check, the probe or the macOS evidence;
see [runtime profiles](RUNTIME-PROFILES.md). The x64 suites check x86 AESENC.

Downstream libraries check their own compatibility with LeanCIL in their own CI, pinning a
LeanCIL revision and advancing it through a reviewed change; LeanCIL's checks build no consumer.
