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
  and AVX-512 F/DQ/VL to one group. Avx512Vbmi and Avx512Vbmi_VL belong to the separate
  AVX512v2 group, which implies AVX512; the `x86-64-v4` group is `x86-64-v3` plus AVX512 only.
- [codeman.cpp, v10.0.13](https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/vm/codeman.cpp)
  enables groups from CPU capabilities and runtime switches. On ARM64 it enables
  ArmBase and AdvSimd together under EnableHWIntrinsic. On x64 it enables AVX512v2 under
  its own EnableAVX512v2 switch, after AVX512.
- [cpufeatures.c, v10.0.14](https://github.com/dotnet/runtime/blob/v10.0.14/src/native/minipal/cpufeatures.c)
  reports AVX512v2 only when the CPU has both AVX512-IFMA and AVX512-VBMI on top of AVX-512.
  Machines with AVX-512 F/BW/CD/DQ/VL, such as Skylake-SP and Cascade Lake, lack VBMI, so
  x86-64-v4 hardware differs on it. InstructionSetDesc.txt, codeman.cpp and cpufeatures.c are
  unchanged between v10.0.13 and v10.0.14.
- [corinfoinstructionset.h, v10.0.13](https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/inc/corinfoinstructionset.h)
  defines ArmBase_Arm64 and AdvSimd_Arm64 only for ARM64 targets. `Set64BitInstructionSetVariants`
  adds each exactly when its base set is enabled, and `EnsureInstructionSetFlagsAreValid`
  removes either one when the other is absent. Both files are unchanged in v10.0.14.

Fresh-process observations collected on 2026-10-30 are checked in:

- [Windows x64, .NET 10.0.14, AMD Ryzen 9 9950X](evidence/runtime-profiles/windows-x64-net10.json).
- [macOS ARM64, .NET 10.0.14, Apple M4](evidence/runtime-profiles/macos-arm64-net10.json).

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
| AVX-512 VBMI, VBMI.VL | Equal; require AVX-512; off in x64-v4 |
| ArmBase.Arm64, AdvSimd, AdvSimd.Arm64 | Equal; ARM64 only |
| Vector128 acceleration | Equal to SSE2 or AdvSimd |
| Vector256 acceleration | Requires AVX2; may be disabled independently |

On the measured x64 runtime, EnableSSE42, EnableAVX, EnableAVX2 and EnableAVX512
disable whole groups and their dependents. EnableAVX512v2=0 disables VBMI and VBMI.VL
and leaves AVX-512 F/DQ/VL enabled, which is exactly x64-v4; EnableAVX512=0 disables both.
The default configuration on the measured Ryzen 9 9950X reports VBMI, so it matches x64-v4
plus `avx512Vbmi`, not x64-v4. Legacy individual switches such as
EnableBMI2 and EnableAVX512DQ have no effect. PreferredVectorBitWidth=128 disables
Vector256 acceleration without disabling AVX2. On the measured ARM64 runtime,
EnableHWIntrinsic=0 disables ArmBase, AdvSimd, AdvSimd.Arm64 and Vector128 acceleration
together; the tested individual ARM switches do not split that group.

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
Evidence field `advSimd64` is `AdvSimd.Arm64.IsSupported`. Extraction answers that getter
with the `advSimd` capability, so validation rejects an observation that lacks it or
records a different value; it is not a separate profile field. Other nested ARM64
getters, such as `Crc32.Arm64` and `Rdm.Arm64`, remain unclassified and are rejected.

Evidence field `avx512Vbmi` is `Avx512Vbmi.IsSupported` and is a profile field.
`avx512VbmiVL` is `Avx512Vbmi.VL.IsSupported`; extraction answers it with `avx512Vbmi`, so
validation rejects an observation that lacks it or records a different value. Every built-in
profile, including x64-v4, sets `avx512Vbmi` to false: x86-64-v4 does not include VBMI, and a
constant true would be refuted by v4 hardware without it. Proofs of a method that reads either
VBMI getter under x64-v4 therefore cover only deployments where .NET reports no VBMI, such as
Skylake-SP or `DOTNET_EnableAVX512v2=0`. For VBMI hardware such as Ice Lake or Zen 4 and later,
use a custom v4 profile with `avx512Vbmi: true`. A proof of a method that never reads VBMI
transfers between the two through
[`Program.ProfileAgreement`](../CIL/ProfileEquivalence.lean), which compares only the flags a
program reads. Other AVX-512 getters, such as `Avx512BW` and `Avx512Vbmi2`, remain unclassified.

Custom consumer profiles, including int256's historical `x64-avx2-bmi2.json` and
`x64-avx512dqvl.json`, must obey the same constraints. Set AVX2/BMI1/BMI2 together;
set all four modeled AVX-512 flags together; set `avx512Vbmi` only with them; set all three
modeled SSE4.2-group flags together. Custom profiles written before `avx512Vbmi` existed are
rejected for the missing field; add it with the value the deployment reports. ARM64 profiles
must set ArmBase/AdvSimd/Vector128 together and cannot enable Vector256 acceleration. A reduced-width x64 profile may retain
`vector256Accelerated: false` with the full AVX2 group enabled.

int256 migrated under these constraints. Before migration, 161 of its 256 gates
used invalid profiles (all 14 custom profiles and the retired built-ins), and none
covered v3/v4. After the migration in int256#141 it had 188 gates, all on valid
profiles: scalar, ARM64 AdvSimd, x64 SSE4.2, x64-v3, x64-v4, and custom
`x64-v3-v128`/`x64-v4-v128` reduced-width profiles. Split-group variants collapsed
into v3/v4, and each method is gated once per distinct reachable body.

These changes can select different CIL branches. Regenerate extraction, reprove
each affected method/profile, re-export interfaces and rebuild full-verification
bundles. Update consumer gates only after those proofs pass. Do not reuse old
certificates, merely rename a profile, suppress the group checks, or weaken a
contract to preserve an old gate. Cross-version runtime support needs its own
explicit evidence and policy rather than relaxing these .NET 10 constraints.
