# Fixed-consumer attribution for [#270](https://github.com/NethermindEth/LeanCIL/issues/270)

In this fixed Equality workload, holding the consumer and decoded methods fixed,
extraction certificates account for
all of the historical scalar kernel-cost increase and 98.47% of the realizable-vector
increase. The consumer's scalar proofs became slightly cheaper. The new division,
scalar and call certificates account for 99.68% of the vector extraction increase.
This does not support attributing the main regression to unspecified-lane or vector-local
consumer proofs.

This is endpoint attribution, not a commit-by-commit bisect. It identifies the dominant
added certificate categories, not a first bad commit or every historical CI wall-time factor.
These are deterministic kernel-work comparisons, not isolated wall-time benchmarks.
Builds ran alongside other validation; their elapsed times are deliberately not compared.
The measurements include the entire imported consumer proof closure, not just the final
theorem or selected expensive declarations. All successful cells also passed independent
joint kernel replay of that closure and its extraction.

## Fixed inputs

| Input | Pin |
| --- | --- |
| Consumer | `NethermindEth/int256` commit `00fcecf53e22b5c9090052779e14b3ba246fb117` |
| Before framework | `199af3db744758d0a6ae5b32e559041c9162cf83` |
| Regressed framework | `08a2d7cacbb58024edb6a282481d2ef11bc1598c` |
| Current scalar control | `9461a1898aa51234e29e294583c7cc41d1f57fc9` |
| Combined current endpoint | `a4a48b6936ba6a43a5a7ab41138c7d8494978e75` |
| Lean | `leanprover/lean4:v4.35.0` |

The current scalar control is an explicit historical comparison pin, not the latest
published framework. The combined endpoint includes shared external-identity certificates
and the memory-fact dispatch fix; both profiles were regenerated and checked on that exact
revision, rather than adding independent estimates. The input is the consumer's
`Equality` **Baseline fixture**, not
its full production assembly. Its entry is
`System.Boolean Nethermind.Int256.UInt256::op_Equality(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)`,
with three reachable methods. This makes the historical attribution bounded and reproducible;
it does not claim to reproduce all 80/104 cases or the complete historical CI run.

The one assembly used by every cell had SHA256
`b554c7a801b4fbc77e99590e5fdaa5585b9d13c6148bd3dcb09f43324d568b03`
and MVID `ca99a8ea-6ca5-428b-9659-58fdc3c901bd`. Assembly identity, entry,
method signatures, tokens, local kinds and every decoded instruction/operand matched
across all three framework extractions for each profile.

Scalar uses the named `scalar` profile. Vector uses the exact explicit, realizable
[x64-v3 feature record](vector-profile.json) on every framework. The old named
`x64-vector256` profile has different feature flags, so comparing those two profile names
would not hold the workload fixed.

The production proof entries from the pinned consumer are `proofs/EqualityScalar.lean`
and `proofs/EqUInt256UInt256Vector.lean`. Their contents are unchanged across all versions.
The SHA256 values are respectively
`289033987e3af27505ce2cb5870f8203fcb5fa3fa4def2323f93b6f11e1adeb7` and
`07bbc930bce4e915e5ca24e3c2854cf1a9f608414d5d9afc489e4448727f9731`.

## Results

`ProfileConsumer.lean` independently checks each theorem's original statement and proof
with `Kernel.check`, including generated equation lemmas. Framework prerequisites are
excluded. Counts include all reachable `UInt256`, `Extracted` and `Proof` modules.

| Profile / framework | Extraction raw HB | Consumer raw HB | Total raw HB |
| --- | ---: | ---: | ---: |
| Scalar / before | 31,484,194 | 18,065,869 | 49,550,063 |
| Scalar / regressed | 58,109,380 | 16,551,497 | 74,660,877 |
| Scalar / current354 | 32,495,891 | 16,768,053 | 49,263,944 |
| Scalar / combined current | 21,754,873 | 16,768,053 | 38,522,926 |
| Vector / before | 37,722,774 | 11,871,660 | 49,594,434 |
| Vector / regressed | 85,374,292 | 12,610,568 | 97,984,860 |
| Vector / combined current | 30,044,089 | 17,495,132 | 47,539,221 |

The current354 scalar total is 0.58% below the original baseline. Between the before and
regressed endpoints, vector consumer proofs increased 6.22%, but only by 738,908 raw
heartbeats. By contrast, vector extraction grew
47,651,518 raw heartbeats: division validation added 22,211,073, scalar validation added
20,926,210 and call validation added 4,363,150.

At the combined current endpoint, scalar theorem checking is 22.25% below the original
baseline and vector theorem checking is 4.14% below it. These are measurements of the
combined revision, including the complete consumer closure; they are not projected sums.

Independent joint replay also checks definitions and combines declarations across the
whole target set. Its raw counts therefore differ from the theorem-only attribution above.
`JointReplay.lean` uses the verifier's complete-part loading, duplicate-equation check and
kernel replay rules, with a counter around the actual replay operation. No target module
is imported as trusted evidence; ordinary framework prerequisites remain imported.

| Profile / framework | Target modules | Complete declarations | Joint replay raw HB |
| --- | ---: | ---: | ---: |
| Scalar / before | 23 | 1,072 | 60,096,519 |
| Scalar / regressed | 23 | 879 | 83,783,395 |
| Scalar / current354 | 23 | 896 | 58,535,873 |
| Scalar / combined current | 23 | 906 | 47,802,012 |
| Vector / before | 39 | 788 | 53,832,291 |
| Vector / regressed | 39 | 829 | 102,388,141 |
| Vector / combined current | 39 | 883 | 56,436,388 |

Combined current scalar joint replay is below its original baseline. Vector joint replay
is 44.88% below the regressed endpoint but remains 4.84% above the original baseline;
the report does not claim that every component has returned to its old cost.

The declaration-count changes include automatically generated equations. Comparing only
matching names would omit real work; the totals deliberately retain every declaration in
the measured closure. See [machine-readable theorem results](results.json).

## Compatibility boundaries

The consumer source was written against the regressed framework. The
[before patch](before.patch) records every required migration in the reachable proof
closure. It removes unavailable guard/opaque-local API names, uses an empty opaque-local
list where the old model has no such field, and uses the constant-false unspecified-bit
predicate because the old value type cannot represent partial unspecified bits. It does
not remove any return-value or caller-memory obligation. The scalar current354 proof
closure needs no source migrations.

[The regressed patch](regressed.patch) only sets the vector helper's measurement budget
explicitly to 2,000,000; both historical vector proofs had already passed at the original
200,000 limit. This option changes no theorem statement or proof term. It was applied
equally while diagnosing the current-vector failure and is included to reproduce the
exact measured source configuration.

Current354 vector proof migration exposed a separate defect: step automation reduced a
bitcast past a supplied abstract evaluation fact, then tried to unfold a symbolic 32-byte
value during unification. Its `run32` and `run64` proofs failed even with the larger
measurement budget. Those failed objects are excluded from the tables. A focused framework
fix restores the supplied fact and the original 200,000 budget. Both complete production
proof entries, per-declaration checks and independent joint replays pass at the combined
current endpoint in the tables.

The [current patch](current.patch) records the six reachable source migrations for the
combined endpoint: zero initial `Frame.stackBytes`, tolerance of an already-closed simp goal,
and an explicit unchanged 200,000 budget. The original `run32`/`run64` proof tails are retained.
All three patches were applied in fresh nested repositories and every resulting changed file
was compared with the measured source after newline normalization. The before, regressed
and current patches change exactly 13, 1 and 6 files respectively.

## Reproduce

Use isolated checkouts and one fixed assembly for every cell. The commands below are
PowerShell examples; choose absolute paths for `$framework`, `$consumer`, `$cell`, `$tools`
and `$assembly`. `$tools` is this directory. Do not build inside an active consumer checkout.

1. Check out the exact framework and consumer commits above. Build the framework extractor
   with `dotnet build Extractor/Extractor.csproj -c Release -o Extractor/bin`. Build its Lean
   prerequisites with `lake build`; the consumer build resolves any additional imports.
2. Build the pinned consumer fixture once and reuse that output for every framework/profile:

   ```powershell
   dotnet build "$consumer/verification/Tests/Fixtures/Equality/Nethermind.Int256.csproj" `
     -c Release -p:FixtureCase=Baseline `
     "-p:BaseOutputPath=$consumer/verification/artifacts/perf-fixed-equality/bin/" `
     "-p:BaseIntermediateOutputPath=$consumer/verification/artifacts/perf-fixed-equality/obj/" `
     "-p:MSBuildProjectExtensionsPath=$consumer/verification/artifacts/perf-fixed-equality/obj/"
   ```

   Rebuilding with another SDK or source path may change the assembly hash. Record the new
   hash and MVID, then hold that exact binary fixed; do not mix independently rebuilt DLLs.
3. Create a fresh cell and copy only tracked `.lean` files under the pinned consumer's
   `verification` directory, preserving relative paths:

   ```powershell
   New-Item -ItemType Directory -Force $cell | Out-Null
   git -C $cell init
   $files = git -C "$consumer/verification" ls-files '*.lean'
   foreach ($relative in $files) {
     $destination = Join-Path $cell $relative
     New-Item -ItemType Directory -Force (Split-Path $destination) | Out-Null
     Copy-Item (Join-Path "$consumer/verification" $relative) $destination
   }
   Copy-Item "$consumer/verification/lean-toolchain" "$cell/lean-toolchain"
   Copy-Item "$consumer/verification/proofs/EqualityScalar.lean" "$cell/Proof.lean"
   ```

   For the vector cell, copy `proofs/EqUInt256UInt256Vector.lean` to `Proof.lean` instead.
   Initializing the cell as its own repository is necessary: otherwise `git apply` can
   resolve paths against an enclosing repository and silently skip these files.
   In the cell directory, apply `before.patch` only for the before framework, or
   `regressed.patch` only for the regressed framework. Apply `current.patch` for the combined
   current endpoint; apply no patch to reproduce the scalar-only current354 control:

   ```powershell
   git add -- .
   $patch = "$tools/before.patch" # Select the matching endpoint patch.
   git apply --check --unidiff-zero $patch
   git apply --unidiff-zero $patch
   $expected = @(Get-Content $patch | Where-Object { $_.StartsWith('+++ b/') } |
     ForEach-Object { $_.Substring(6) } | Sort-Object -Unique)
   $changed = @(git diff --name-only | Sort-Object -Unique)
   if (@(Compare-Object $expected $changed).Count -ne 0) {
     throw 'Migration did not change exactly the expected files'
   }
   ```

   The zero-context patches avoid whitespace-only context records in the stored diffs.
   They are relative to the cell's `verification`-contents root. When checking
   against the original consumer repository root, use `--directory=verification`.
4. Create this `lakefile.toml` with the selected framework's absolute path:

   ```toml
   name = "fixed_consumer"
   version = "0.1.0"
   defaultTargets = ["Proof"]
   [[require]]
   name = "leancil"
   path = "ABSOLUTE_FRAMEWORK_PATH"
   [[lean_lib]]
   name = "UInt256"
   [[lean_lib]]
   name = "Extracted"
   [[lean_lib]]
   name = "Proof"
   ```

5. Generate the extraction with the framework belonging to that cell. Use `scalar` or the
   same explicit vector profile file, then copy the resulting `Extracted.lean` to the cell:

   ```powershell
   $entry = 'System.Boolean Nethermind.Int256.UInt256::op_Equality(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)'
   dotnet "$framework/Extractor/bin/Nethermind.LeanCIL.dll" extract `
     $assembly $entry "$cell/extraction" "@$tools/vector-profile.json"
   Copy-Item "$cell/extraction/Extracted.lean" "$cell/Extracted.lean"
   ```

   Before comparing costs, compare `identity.json` assembly hash/MVID, entry, profile and
   all decoded methods/locals/instructions across framework versions. Stop on any mismatch.
6. In the cell, build the complete production proof, profile its complete imported closure,
   derive the replay target list, and independently replay it:

   ```powershell
   Copy-Item "$tools/ProfileConsumer.lean" .
   Copy-Item "$tools/JointReplay.lean" .
   lake update
   lake build Proof *> build.log
   if ($LASTEXITCODE -ne 0) { throw 'Proof build failed' }
   lake env lean ProfileConsumer.lean *> profile.log
   if ($LASTEXITCODE -ne 0) { throw 'Kernel attribution failed' }
   $targets = @(Get-Content profile.log | Where-Object { $_.StartsWith('TARGET ') } |
     ForEach-Object { $_.Substring(7) })
   ConvertTo-Json -InputObject $targets | Set-Content ReplayTargets.json
   lake env lean JointReplay.lean *> replay.log
   if ($LASTEXITCODE -ne 0) { throw 'Independent replay failed' }
   if (Select-String build.log,profile.log,replay.log -Pattern 'sorryAx') {
     throw 'Unproved axiom in measured closure'
   }
   ```

Do not compare profiled checking milliseconds with unprofiled CI wall times. For a new
wall-time experiment, warm the same framework prerequisites, rebuild only the fixed
consumer closure, and run each checking/replay process without competing workloads.
