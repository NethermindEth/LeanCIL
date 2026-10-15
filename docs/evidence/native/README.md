# Native/int32 runtime evidence

Recorded on 2026-10-15. The probe executes the exact CIL recorded in each manifest on isolated .NET **10.0.0** runtimes:

| Runtime | Admitted cases | Mismatches | Rejected mixed unsigned branches | Historical model divergences |
| --- | ---: | ---: | ---: | ---: |
| Windows x64 | 3,600 | 0 | 500 | 38 |
| macOS ARM64, Apple M4 | 3,600 | 0 | 500 | 38 |

Each architecture's `results.csv` records opcode, operand order, int32 provenance, explicit conversion, admission status, both operand bit patterns, expected result, and actual result/fault. `manifest.json` records runtime build/version/architecture, runtime binary hashes, probe and generated fixture hashes, exact method signatures and CIL instructions, and the results hash. Both machines executed the same probe binary and generated the same deterministic fixture bytes. The CSV bytes differ only in platform newline encoding.

The local `.gitattributes` preserves those runtime-produced CSV bytes, including Windows CRLF, so checkout and commit do not invalidate the recorded SHA256 values.

The corpus contains 31 arithmetic/comparison/branch opcodes, both operand orders, five native boundaries and five int32 boundaries, loaded from arguments and embedded as `ldc.i4` constants. It also exercises all five affected unsigned branches with explicit `conv.i` and `conv.u` on both operand sources. Zero divisors, signed division/remainder overflow, unsigned boundaries, and negative int32 values are included. Results are compared with a separate `BigInteger` oracle; this is finite runtime evidence, not a proof of CoreCLR.

Both architectures were also run with `DOTNET_TieredCompilation=0`, forcing fully optimized JIT compilation rather than default tiering. All 4,100 rows were identical to the original runs, including the 38 historical divergences. [optimized-runs.json](optimized-runs.json) records the exact commands, environment setting, runtime and binary identities, and result hashes. It references the existing CSVs and CIL listings because their hashes match exactly; unchanged rows and instructions are not duplicated. The probe binaries are identified independently for each run, including rebuilds between runs.

## Discovered discrepancy and enforced boundary

The old opcode-only widening rule predicts zero extension for mixed native/int32 unsigned branches. CoreCLR instead sign-extends negative int32 constants in this path. For example, `ldarg.0; ldc.i4 -1; bne.un` with native argument `0xffffffffffffffff` does **not** branch, while replacing the constant with an int32 argument **does** branch. There are 38 such divergences per architecture in the recorded matrix. They remain visible as `pass=False,admitted=False`, rather than being deleted or changed into passing expectations.

`NativeOperands` now rejects mixed `bne.un`, `blt.un`, `bgt.un`, `ble.un`, and `bge.un`, including every short form. The checked native wrapper rejects them too. The diagnostic requires explicit `conv.i` or `conv.u`; those same-width forms remain supported and are tested. Accepting argument-only cases would require an extra runtime assumption: inlining can expose constant actual arguments, and propagation can change local provenance. Neither is part of the verification contract.

`Tests/NativeIntegers.cs` checks all 60 combinations of short/long opcode, operand order, and argument/negative-constant/local provenance are rejected. It also compares and kernel-checks explicitly converted branches. Ordinary mixed arithmetic, scalar comparisons including `clt.un`/`cgt.un`, signed branches, and same-width branches remain admitted.

## Pinned official source and binary provenance

The official `v10.0.0` source tag resolves to **60629d14374c56f1cb51819049ad1fa529307f8d**. Relevant source locations are:

- [Arithmetic widening](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/importer.cpp#L5556-L5579): mixed native/int32 arithmetic inserts casts using the arithmetic unsigned flag. The [opcode dispatch](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/importer.cpp#L7434-L7544) sets that flag for unsigned checked arithmetic; unsigned division/remainder use unsigned operators without unsigned operand widening.
- [Scalar comparisons](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/importer.cpp#L7833-L7892) use the implicit-cast helper's default, which is [false](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/compiler.h#L4634), even for unsigned comparisons.
- [Conditional branches](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/importer.cpp#L7947-L7975) pass the unsigned flag. The [helper's constant path](https://github.com/dotnet/runtime/blob/60629d14374c56f1cb51819049ad1fa529307f8d/src/coreclr/jit/importer.cpp#L2459-L2485) retags constants without consulting that flag, unlike its nonconstant cast path. This explains the observed provenance-sensitive discrepancy.

`provenance.json` pins source file SHA256 values and official runtime archive URLs/SHA512 values from Microsoft's release manifest. Both downloaded archives were checked against those SHA512 values. The installed binaries identify build **b0f34d51fccc69fd334253924abd8d6853fad7aa**, which was not publicly available at that GitHub commit URL when checked. Thus the evidence links the official release source and official release binaries; it does **not** assert a reproducible build or an exact public-source match for the binary's internal build commit. The manifests retain that difference explicitly.

## Reproduce

Build the standalone probe with the repository SDK:

```sh
dotnet build Tests/NativeProbe/NativeProbe.csproj -c Release -p:EnforceCodeStyleInBuild=true -p:GenerateDocumentationFile=true
```

Download the appropriate archive from `provenance.json`, verify its SHA512, and unpack it into an isolated directory. Run its `dotnet` executable, rather than a system installation:

```sh
/path/to/isolated-runtime/dotnet Tests/NativeProbe/bin/NativeProbe.dll /path/to/results
```

The project pins runtime 10.0.0 and disables roll-forward. To run on a second machine without installing an SDK, copy `NativeProbe.dll`, `NativeProbe.deps.json`, `NativeProbe.runtimeconfig.json`, and `Mono.Cecil.dll` from the build directory. The generated fixture uses a deterministic MVID and timestamp. An admitted mismatch returns exit code 1; historical mismatches in the explicitly rejected category remain recorded separately. The full extraction/proof regression suite is `dotnet run --file Tests/NativeIntegers.cs` after normal repository build prerequisites.

To repeat the optimized-mode run, set `DOTNET_TieredCompilation=0` for that process. In PowerShell, set `$env:DOTNET_TieredCompilation = '0'` before invoking the isolated runtime. On macOS, prefix the command with `DOTNET_TieredCompilation=0`. Use a separate output directory to retain both runs.
