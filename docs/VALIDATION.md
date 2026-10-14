# Validation results

Validated on Windows with .NET SDK **10.0.402** and Lean **4.35.0** on 2026-10-14.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The complete C# regression runner passed **36 check groups**. This includes initial CLI proof selection and theorem output, an actual addition-to-subtraction source edit and rebuild, recovery using settings retained after the failed proof, the invalid-memory-access theorem, and the integer opcode and narrow-storage matrices. The CLI group also passed separately against an isolated installation of the packaged .NET tool before the integer opcode extension.

The runner builds the independent assemblies and the CIL library, then creates a fresh source-only Lean build for verification. File-based C# apps provide the test runner, verifier and metadata fixture generator. Their only external package is the same pinned Mono.Cecil version used by the extractor.

The runner also accepts `--suite core`, `--suite cli`, `--suite integer` and `--suite narrow` after `--`. These partitions cover the same 36 check groups and can run concurrently in separate checkouts. Each partition builds its own prerequisites, retains fresh Lean proof checking and writes `artifacts/test-results-<suite>.json`; running without arguments still checks everything and writes `artifacts/test-results.json`.

| Coverage | Result |
| --- | --- |
| Library, scalar/SIMD semantics, allocation, permissions, initialization, lifetime and symbolic automation | Passed |
| Ten extracted arithmetic, branching, call, aliasing, aggregate and semantic-negative proofs, each with artifact checks | Passed |
| Compiled C# negation: universal modular additive-inverse contracts for 32- and 64-bit inputs | Both proofs passed |
| Exact `nop`, `neg`, `cgt`, `bgt`, `bgt.s`, `ble`, `ble.s`, `ble.un`, `ble.un.s` encodings in independent Cecil fixtures | 370 checked-execution boundary cases passed across 32- and 64-bit operands |
| Identity substituted for negation, with the unchanged universal contract | Both widths rejected by proof checking; no successful report retained |
| New scalar operations: stack underflow, mixed widths and reference operands; `nop` preserves arbitrary stacks | Semantic tests passed |
| Compiled C# unsigned-short conversion: universal result `x % 65536` for every 32-bit input | Proof passed |
| Narrow conversions, locals, arguments, returns, calls and fields, including aggregate snapshots | 744 checked-execution boundary cases passed, including 144 deliberate faults |
| Uninitialized narrow locals and 64-bit stores into narrow homes | Rejected with the expected located faults |
| Two-byte field overrun and forged narrow runtime type identity | Both rejected during extraction |
| Signed conversion substituted for unsigned conversion, with the unchanged universal contract | Rejected by proof checking; no successful report retained |
| Narrow access bounds, permissions and lifetime; generic typed store/load normalization | Semantic tests and universal roundtrip theorem passed |
| Short and full assembly selectors retain the same complete manifest identity | Passed |
| Explicit version, culture and public-key-token mismatches | Three intended identity rejections |
| Method selectors: aliases, optional returns, short declaring types, overloads, canonical artifact identity, malformed inputs and candidate diagnostics | 23 checks passed |
| Assembly inference from a renamed DLL, equivalent explicit identities, mismatched constraints, malformed options and stale outputs without `--assembly` | Passed |
| Directory-only checks: recorded profiles, moved DLL override, missing DLL, invalid profile and modified artifacts | Passed |
| Independent hardware-feature assembly built from a single C# file | Passed |
| CLI packaging smoke checks: build and publish `leancil.exe`, `dotnet run`, isolated .NET tool installation, installed `leancil extract` and `leancil check` | Passed separately |
| One-command worked example: `dotnet run --file Examples/Verify.cs` | Passed; `ExampleProof.correctness` verified |
| Installed `leancil verify`: explicit proof, printed theorem, portable settings, source mutation, failure/recovery, memory fault theorem and stdout/stderr | Four CLI regression stages passed |
| Method discovery includes canonical selectors and unsupported candidates without claiming support | Passed |
| Malformed settings, missing proof, unsupported CIL, changed assembly and missing Lake produce stage-specific guidance | Passed |
| Subtraction rejected by the unchanged universal addition contract | Passed; no successful report retained |
| Unsupported division | Explicit extraction rejection |
| Synchronized methods, wrong framework/identity, invalid field layout, unsupported locals, cyclic control flow, static initializer and forged runtime scope | Eight intended metadata rejections |
| Identity-bound static RVA data | Passed |
| Tampered Lean output, changed compiled assembly, changed assembly version with a short selector, changed proof and changed feature profile | Five intended stale-artifact rejections |

The addition theorem proves modular arithmetic correctness for arbitrary 64-bit inputs in the checked execution model. The unsigned-short theorem proves reduction modulo 65,536 for arbitrary 32-bit inputs. The invalid-access and expired-reference theorems classify faults and rule out successful execution for every fuel budget. The subtraction theorem independently refutes the intended addition result. Other example claims have the quantifiers and inputs displayed in their theorem statements; concrete examples do not establish universal method correctness.

All audited example theorems use only the permitted standard Lean axioms, if any. No new axioms, `sorry`, `admit`, native proof evaluation or unproved summaries were added. See [the trusted base](SOUNDNESS.md) for runtime and extraction assumptions.

Machine-readable results are written to `artifacts/test-results.json`; each successful proof produces an identity-bound `verified.json`. These generated files are reproducible outputs and are not committed. Consumer-project integration and broad .NET runtime coverage are outside these validation results.
