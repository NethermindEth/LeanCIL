# .NET 10 runtime profiles

Execution profiles describe the capabilities reported by a deployed .NET 10
CoreCLR process. They are not arbitrary CPU feature subsets. Both
`FeatureProfile.Validate()` and Lean's `FeatureProfile.Valid` enforce the groups
below. Passing these checks does not establish that a particular deployment uses
the selected profile: deployment must still match the recorded capabilities.

## Evidence

The runtime sources pin this policy to .NET 10:

- [InstructionSetDesc.txt, v10.0.13](https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/tools/Common/JitInterface/ThunkGenerator/InstructionSetDesc.txt)
  assigns SSE/SSE2 to X86Base, SSSE3/SSE4.1/SSE4.2 to one group, BMI1/BMI2 to AVX2,
  and AVX-512 F/DQ/VL to one group.
- [codeman.cpp, v10.0.13](https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/vm/codeman.cpp)
  enables groups from CPU capabilities and runtime switches. On ARM64 it enables
  ArmBase and AdvSimd together under EnableHWIntrinsic.

Fresh-process observations collected on 2026-10-24 are checked in:

- [Windows x64, .NET 10.0.13](evidence/runtime-profiles/windows-x64-net10.json).
- [macOS ARM64, .NET 10.0.12, Apple M4](evidence/runtime-profiles/macos-arm64-net10.json).

Each record includes the actual runtime version, process architecture, OS, switch
and observed flags. Reproduce with:

```sh
dotnet run --file scripts/ProbeRuntimeProfiles.cs -- observations.json
```

The probe launches a new runtime process for each configuration and removes the
tested DOTNET_/COMPlus_ switches before applying that case. It records observations;
it does not certify a runtime, install one, or assume missing hardware is present.
These measurements do not claim coverage of Mono, NativeAOT, .NET 11 or every
future .NET 10 servicing release. Recheck runtime changes before extending the
supported deployment boundary.

## Constraints

| Capabilities | Constraint |
| --- | --- |
| X86Base.X64, SSE2 | Equal; x64 only |
| SSSE3, SSE4.1, SSE4.2 | Equal; require SSE2 |
| AVX | Requires SSE4.2; may be enabled without AVX2 |
| AVX2, BMI1, BMI2 | Equal; require AVX |
| AVX-512 F, F.VL, DQ, DQ.VL | Equal; require AVX2 |
| ArmBase.Arm64, AdvSimd | Equal; ARM64 only |
| Vector128 acceleration | Equal to SSE2 or AdvSimd |
| Vector256 acceleration | Requires AVX2; may be disabled independently |

On the measured x64 runtime, EnableSSE42, EnableAVX, EnableAVX2 and EnableAVX512
disable whole groups and their dependents. Legacy individual switches such as
EnableBMI2 and EnableAVX512DQ have no effect. PreferredVectorBitWidth=128 disables
Vector256 acceleration without disabling AVX2. On the measured ARM64 runtime,
EnableHWIntrinsic=0 disables ArmBase, AdvSimd and Vector128 acceleration together;
the tested individual ARM switches do not split that group.

## Migration

Impossible built-ins are retired with an error, not silently remapped:

| Retired name | Starting point for a new proof |
| --- | --- |
| x64-sse41 | x64-sse42 |
| x64-avx2, x64-avx2-bmi1, x64-bmi2, x64-vector256 | x64-v3 |
| x64-avx512, x64-avx512-bmi1 | x64-v4 |
| arm64-armbase | arm64-advsimd |

`x64-sse2` supplies the x64 baseline with SSE4.2 and higher groups disabled.
`scalar` remains the no-hardware-intrinsics profile. The repo's extraction and
verification fixtures use the supported names.

The built-in list intentionally does not name every valid configuration. Use
custom JSON for SSE4.2+AVX without AVX2 and for v3/v4 with
`vector256Accelerated: false`. The validators accept these observed states;
their absence from the built-in list is not a deployment restriction.

`Tests/FeatureEvidence.cs` runs the same built-in, mutated and recorded-observation
cases through the production C# validator and generated kernel-checked Lean
theorems. The runtime-profile drift workflow probes Linux x64 and ARM64 weekly,
on demand and on policy changes, using the installed .NET 10 servicing runtime.
Its artifacts record the actual runtime version and architecture; a successful
job validates only those observations, not every possible deployment.

Evidence field `bmi2` is `Bmi2.X64.IsSupported`, `x86Base64` is
`X86Base.X64.IsSupported`, and `armBase64` is `ArmBase.Arm64.IsSupported`.
These are the model's 64-bit capabilities, not the corresponding base-class flags.

Custom consumer profiles, including int256's historical `x64-avx2-bmi2.json` and
`x64-avx512dqvl.json`, must obey the same constraints. Set AVX2/BMI1/BMI2 together;
set all four modeled AVX-512 flags together; set all three modeled SSE4.2-group
flags together. ARM64 profiles must set ArmBase/AdvSimd/Vector128 together and
cannot enable Vector256 acceleration. A reduced-width x64 profile may retain
`vector256Accelerated: false` with the full AVX2 group enabled.

In the int256 revision pinned by the consumer workflow, 161 of 256 gates need
profile migration: all 14 custom profiles and the retired built-ins. The 95
already valid gates cover scalar, ARM64 AdvSimd and x64 SSE4.2 only; they do not
establish v3/v4 correctness. Migration must add realistic v3/v4 proofs, including
reduced vector width where required, and may consolidate split-group variants.

These changes can select different CIL branches. Regenerate extraction, reprove
each affected method/profile, re-export interfaces and rebuild full-verification
bundles. Update consumer gates only after those proofs pass. Do not reuse old
certificates, merely rename a profile, suppress the group checks, or weaken a
contract to preserve an old gate. Cross-version runtime support needs its own
explicit evidence and policy rather than relaxing these .NET 10 constraints.
