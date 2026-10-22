# Validation coverage

For checked-step and loop tactics, see [proof automation](#proof-automation).

The repository pins .NET SDK **10.0.402** and Lean **4.35.0**. The checks below cover semantic behavior, extracted contracts, artifact integrity and rejection cases.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The regression runner covers **54 check groups** across twenty-three test partitions. This includes initial CLI proof selection and theorem output, an actual addition-to-subtraction source edit and rebuild, recovery using settings retained after the failed proof, the invalid-memory-access theorem, and the integer opcode, narrow-storage and primitive-operation matrices. The CLI group also passed separately against an isolated installation of the packaged .NET tool before the integer opcode extension.

The runner builds the independent assemblies and the CIL library, then prepares a source-keyed, kernel-replayed library for verification. CI rebuilds from sources; local runs may reuse an integrity-checked cache. Every proof still compiles and undergoes kernel replay in a new private directory. File-based C# apps provide the test runner, verifier and metadata fixture generator. Metadata tooling uses the same pinned Mono.Cecil version as the extractor; the F# example assembly also uses pinned FSharp.Core.

The runner accepts `--suite <name>` after `--`, with names `core`, `cli`, `integer`, `narrow`, `primitive`, `division`, `checked`, `conversions`, `native`, `arguments`, `layout`, `copy`, `bits`, `enums`, `nested`, `instance`, `constructors`, `fsharp`, `math`, `unsafe`, `blocks`, `generics`, `loops`, `contracts`, `evidence`, `scaling`, `excluded`, `identity`, `labels`, `names`, `callers` and `outcomes`. These partitions cover the same check groups as the full command and can run concurrently in separate checkouts. Each partition builds its own prerequisites, retains fresh Lean proof checking and writes `artifacts/test-results-<suite>.json`; running without arguments checks everything and writes `artifacts/test-results.json`.

| Coverage | Result |
| --- | --- |
| Cyclic control flow and termination | Universal checked countdown proof for every `uint`, including zero and maximum value; 12 runtime comparisons; incorrect implementation rejected under the unchanged contract; infinite loop proved to exhaust every fuel budget; backward switch, native arithmetic and fixed-feature loops checked; eight malformed or unsupported fixtures rejected |
| Generic method specialization | 125 C#/F# runtime comparisons, six universal identity proofs, six reference checks, twelve metadata/recursion rejections, wrong-implementation rejection and provenance tamper detection |
| Block memory and alignment prefixes | 251 checks; ten malformed-prefix/type cases rejected; universal out-of-bounds fill rejection |
| Layout-based Unsafe helpers | 418 checks across 19 element types and all three managed offset overloads; ten malformed generic calls rejected |
| Integer Math helpers | 21,804 runtime comparisons across 40 overloads; universal signed-minimum proof; incorrect implementation and seven malformed calls rejected |
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
| Compiled C# `ref int` store/load: every 32-bit input returned unchanged | Universal proof passed |
| Primitive `ldobj`, `stobj`, `initobj`, indirect loads/stores, C# aliasing, `switch` and `sizeof`, including native integer storage | 534 cases passed, including memory faults, initialization and preservation of neighboring bytes |
| Empty/duplicate switch tables, out-of-range unsigned indices and switch-only managed dependencies | Passed |
| Corrupted switch target, unsupported arm, four forged type tokens and floating-point size | Seven intended extraction rejections |
| `sizeof` on pointers, managed references, objects, strings, arrays, double, auto layouts and malformed sequential field offsets, reference-containing structs and generic layouts | Eleven intended extraction rejections; no Lean extraction produced |
| Constant-zero write substituted for the input, with the unchanged universal store/load contract | Rejected by proof checking; no successful report retained |
| Scalar access operand/width checks, bounds and lifetime; arbitrary-memory 32-bit store/load roundtrip | Semantic tests and universal roundtrip theorem passed |
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
| Unsupported array allocation | Explicit extraction rejection |
| Integer `div`, `div.un`, `rem`, `rem.un`, both widths | 648 comparisons against actual .NET execution and corresponding Lean proofs passed, including divide-by-zero and signed overflow |
| Extracted unsigned quotient for arbitrary inputs with a nonzero divisor | Universal proofs passed for 32 and 64 bits; multiplication substituted for division rejected by the unchanged contract |
| Division with mixed widths, references, stack underflow or a zero divisor | Semantic rejection tests passed |
| Checked add/subtract/multiply, signed and unsigned at both widths | 2,028 comparisons against actual .NET results or overflow exceptions and corresponding Lean proofs passed |
| Checked addition with a sum that fits | Universal 32-/64-bit natural-number addition proofs passed; subtraction substituted for addition rejected |
| All 20 integer checked-conversion encodings, from both input widths | 762 comparisons against actual .NET execution and corresponding Lean proofs passed, including native destinations and overflow |
| Checked 64-to-32-bit unsigned narrowing with a representable input | Universal preservation proof passed; an eight-bit truncating implementation rejected |
| Native signatures, locals, calls, fields, references, arithmetic, shifts, casts and `sizeof`, plus exact mixed native/int32 operations in both operand orders | 2,511 comparisons against actual .NET results or arithmetic exceptions and corresponding Lean proofs passed; all 60 ambiguous mixed unsigned-branch forms rejected unless explicitly widened |
| Extracted native addition on the admitted 64-bit target | Universal modular-addition proof passed |
| Required-32-bit assembly, forged native type identity, native field overrun, native/int64 operands and 32-bit execution profile | Five intended extraction rejections |
| Native widening wrapper with memory instructions, nested wrappers or references | Semantic rejection tests passed; unsigned branch/comparison widening differences checked explicitly |
| Argument assignment/addressing, both full and short encodings, all admitted integer storage types, aliases, calls, byref reassignment and structs | 639 runtime/memory cases passed, including 636 actual .NET comparisons |
| Overwriting an argument with a replacement value | Universal proof passed for arbitrary inputs; assignment to the wrong parameter rejected |
| Returning an address into a parameter home | Lifetime fault proved for every input; successful execution ruled out for every fuel budget |
| Parameter setup with missing inputs or incompatible scalar/reference values, and narrow initialization | Semantic checks passed; taking the address of a byref parameter rejected during extraction |
| Ordinary and packed sequential structs, all admitted packing values, small/odd explicit sizes and empty structs | 187 runtime layout/execution cases passed; emitted sizes and field offsets agree with managed runtime probes |
| Sequential struct field store/load | Universal preservation proof passed for every 32-bit input |
| Invalid packing, oversized layout, auto layout, reference/float fields, inline arrays, generics, explicit offsets on sequential fields, nested reference-bearing and recursive fields | Ten intended metadata rejections |
| Synchronized methods, wrong framework/identity, invalid field layout, unsupported locals, static initializer and forged runtime scope | Seven intended metadata rejections |
| Identity-bound static RVA data | Passed |
| Static `ReadOnlySpan<uint>`/`<ulong>` tables | Indexed reads, length and first element compared with .NET, including negative and past-end indices faulting with `System.IndexOutOfRangeException`; forged receiver folds fail the feature certificate; tampered RVA bytes change the proved word; other span local uses, computed indices and branches into the fold rejected |
| Static `ReadOnlySpan<byte>` lookup tables | First and last byte proved; past-end read and write to immutable data rejected; tampered RVA bytes change the proved value; six intended span metadata rejections |
| Tampered Lean output, changed compiled assembly, changed assembly version with a short selector, changed proof and changed feature profile | Five intended stale-artifact rejections |

The addition theorem proves modular arithmetic correctness for arbitrary 64-bit inputs in the checked execution model. The unsigned-short theorem proves reduction modulo 65,536 for arbitrary 32-bit inputs. The invalid-access and expired-reference theorems classify faults and rule out successful execution for every fuel budget. The subtraction theorem independently refutes the intended addition result. Other example claims have the quantifiers and inputs displayed in their theorem statements; concrete examples do not establish universal method correctness.

All audited example theorems use only the permitted standard Lean axioms, if any. No new axioms, `sorry`, `admit`, native proof evaluation or unproved summaries were added. See [the trusted base](SOUNDNESS.md) for runtime and extraction assumptions.

Machine-readable results are written to `artifacts/test-results.json`; each successful proof produces an identity-bound `verified.json`. These generated files are reproducible outputs and are not committed. Consumer-project integration and broad .NET runtime coverage are outside these validation results.

Typed copy validation: 648 runtime result/byte-copy checks passed across 18 primitive, struct and vector types, including self-copies. The universal UInt64 copy contract passed and rejected reversed source/destination operands. Four unsupported/forged type-token cases were rejected during extraction. Ten semantic tests cover initialization, permissions, lifetime, GC-sensitive storage, bounds, null references and partial overlap. The generic copy snapshot theorem and the full Lean library/semantic/automation build passed.

Portable helper validation: 7,200 comparisons with actual .NET results passed, covering power-of-two boundaries, zero/all-ones values, signed boundaries and negative/oversized rotation counts. Universal 64-bit rotation round-trip and integer-logarithm proofs passed with only approved Lean axioms; incorrect implementations failed the unchanged contracts. Nine malformed/unsupported runtime calls were rejected before extraction. Semantic tests reject incorrect arity, widths and operand types.

Enum validation: 378 runtime comparisons passed across all eight underlying integer types, flags, calls, fields and typed storage. The universal flags proof passed and rejected an incorrect implementation. Eleven malformed metadata cases were rejected.

Nested struct validation: 123 runtime/layout comparisons passed, including sixteen packing combinations. A universal nested snapshot proof passed and rejected an incorrect implementation. Seven malformed layouts and seven semantic memory-fault cases were rejected.

Struct instance-call validation: 96 runtime comparisons passed, including short and full argument encodings, by-value copy isolation and direct constructor calls. A universal instance store/load proof passed and rejected an incorrect implementation. Four malformed metadata cases were rejected.

Struct construction validation: 56 runtime comparisons passed, covering packed and nested structs, chained and parameterless constructors, zero-initialized storage and checked arithmetic faults. A universal constructed-value proof passed for every 64-bit input; an incorrect constructor result failed the unchanged contract. Five malformed constructor cases were rejected. Semantic tests cover zero-sized construction, missing arguments, zero initialization and a non-void constructor result. The full 125-job Lean library, semantic and automation build passed.

F# validation: 324 comparisons with actual .NET execution passed for addition, unsigned branching, managed calls, mutable structs and by-reference stores. The existing addition, store/load and constructor contracts passed unchanged against the F# assembly. Subtraction failed the addition contract, and a list-returning function was rejected during extraction. These examples require no F#-specific CIL semantics or proof shortcuts.

## Contracts and extraction evidence

The core and universal-contract suites cover checked execution and memory preservation. Choose and GenericIdentity preserve arbitrary caller memory exactly; Struct preserves preexisting caller memory under its well-formedness hypothesis. Each unchanged contract rejects its incorrect compiled implementation. Countdown validation covers original instructions, inserted NOPs and reordered blocks, and rejects wrong results and nontermination.

Extraction evidence validation passed 74 Lean regressions, 34 compiled certificate fixtures, 29 generated-evidence mutation rejections, and mandatory-certificate positive/negative checks. All six CLI checks passed, including kernel replay of imported helpers and rejection of unchecked direct/transitive proofs. These tests do not establish full raw-CIL/runtime correspondence.

The native extraction suite passed 2,511 runtime comparisons and kernel proofs, its universal addition contract, 60 ambiguous mixed unsigned-branch rejections and five metadata/profile rejections. Separate pinned .NET 10.0.0 probes on x64 and ARM64 each passed 3,600 admitted cases; 500 rejected cases retain 38 historical model divergences. Full JIT optimization produced identical per-case results. See [native evidence](evidence/native/README.md) for exact provenance and reproduction commands.

Memory-view equivalence covers access, writes and subsequent checked execution, including calls, constructors and frame cleanup. At 128 alternating stores the benchmark retained one view rather than 129; median local kernel-reduction time was 5.6s versus 17.7s over three runs, including startup and shared-machine activity. These timings are illustrative, not a performance guarantee.

The initialized-types end-to-end test and four mandatory-certificate audit cases check that verification reports record both the schema-3 extraction audit and initialized-type assumptions.

## Proof automation

The checked proof APIs share execution traces, frame-setup effects and instruction
contracts. Their validity fields retain the required well-formedness and input
validity hypotheses. See [Writing checked proofs](PROOFS.md) for API locations
and examples.

`Tests.Automation` checks an eight-instruction arithmetic method with symbolic
inputs and arbitrary caller memory, using `cil_checked_steps`. Its instruction
sequence is `arg, arg, const32, shl, add, const32, gtu, ret`; the theorem's axiom
assertion permits only `propext` and `Quot.sound`. The same module checks both
paths of a symbolic branch using a supplied truth hypothesis, and verifies that
failed candidate summaries do not escape their transaction.

`Tests.MethodEmbedding` checks transport of checked executions to actual method
bodies with mapped program counters. `Tests.AggregateSetup` and `Tests.Semantics`
cover frame setup and interpreter behavior. The extracted-loop suite checks
universal countdown termination, NOP/reordered variants, runtime comparisons,
incorrect/nondecreasing loop rejection, feature selection, infinite-loop fuel
exhaustion, backward switch and malformed-input rejection.

`Tests.InterpreterEquations` checks that each shared equation lemma is stored by
its LeanCIL module rather than rebuilt by the importer, and that a tactic macro
naming `CIL.step.eq_def` elaborates.

Run the focused Lean targets and extracted-loop suite with:

```sh
lake build CIL Tests.Automation Tests.MethodEmbedding Tests.AggregateSetup Tests.Semantics Tests.InterpreterEquations Tests.MethodIdentity Tests.StructuralLabels Tests.DebugNames Tests.MethodContract Tests.OutcomeContract
dotnet run --file scripts/Test.cs -- --suite loops
```

The loop suite builds a fresh verification library and performs kernel replay
as part of extracted-loop verification. Use the full test command at the top
of this document for the complete verification suite.

When changing proof tactics or shared contracts, measure fresh elaboration of
the library and its consumers, compiled artifact size, CPU time, peak process
memory and kernel replay separately. Compile identical consumer sources against
both revisions and alternate serial runs with prebuilt dependencies on the same
machine. A smaller compiled proof alone does not establish a speed or memory
improvement. Preserve the kernel replay, axiom audits and negative regressions.

## Store view reuse

Stores reuse existing read permissions when they already cover the written range, including coverage spread across multiple views. The `write_run_equivalent` theorem proves that replacing the previous always-prepending write preserves any subsequent checked execution: returned values, exact faults, allocation state, bytes and permissions. `Memory.Equivalent.run` and `.invoke` cover branches, calls, constructors and frame cleanup.

Run `pwsh scripts/BenchmarkViews.ps1 -Stores 128 -Repetitions 3` to compare kernel reduction against the previous write implementation. In a local Windows run with Lean 4.35.0, 128 alternating stores retained 1 view instead of 129; median elapsed time was 5.6 seconds versus 17.7 seconds. These timings include process startup and shared-machine activity; view counts are checked by kernel reduction.
