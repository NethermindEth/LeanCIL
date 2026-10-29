# Validation

Run the smallest suite covering the changed behavior, then the checks required by `AGENTS.md`.
Concurrent suites need separate checkouts because they build and mutate `artifacts/`.

```sh
dotnet run --file scripts/Test.cs -- --suite core
dotnet run --file scripts/Test.cs -- --suite evidence
dotnet run --file scripts/Test.cs -- --suite loops
```

Omit `--suite` to run everything. The accepted names and fixture mapping are defined in
[scripts/Test.cs](../scripts/Test.cs); export partitions are defined in
[ExportVerificationSuites.cs](../scripts/ExportVerificationSuites.cs).

| Changed area | Relevant suites or checks |
| --- | --- |
| Extraction certificates and metadata | `evidence`, plus the affected opcode or runtime-helper suite |
| Arithmetic and representations | `integer`, `narrow`, `primitive`, `checked`, `conversions`, `native` |
| Memory and references | `unsafe`, `blocks`, `copy`, `arguments`, `layout` |
| Calls and contracts | `callers`, `contracts`, `outcomes`, `imports` |
| Loops and shared stepping tactics | `loops`, examples, and `Tests.Automation`, `Tests.StoreFacts`, `Tests.MethodContract`, `Tests.CodeAt` |
| CLI, artifact identity and theorem selection | `core`, `cli`, `failures`, `workspace`, `audit` |
| Exported interfaces and implementation checks | The affected export partition from `ExportVerificationSuites.cs` |

`lake build` builds only `CIL`. Changes under `CIL/` require building every library target in
`lakefile.toml` before pushing. C# changes require analyzer validation, including changed
file-based tests. Any `sorryAx`, unexpected diagnostic or failed proof is a failure.

## What the checks cover

Positive fixtures compare compiled .NET behavior with checked model execution or establish
universal theorems. Negative fixtures independently tamper with translation evidence, violate
memory premises, or change implementations while retaining their specifications. An unsupported
instruction must not satisfy a named-exception obligation.

- [Coverage reference](VALIDATION-COVERAGE.md): extraction, runtime comparisons, artifact binding
  and preparation infrastructure.
- [Proof automation regressions](VALIDATION-PROOFS.md): shared tactics, memory facts and composition.
- [Export and consumer checks](VALIDATION-EXPORTS.md): interface pins, audit and consumer packages.
- [CI operation](CI.md): job selection, prepared libraries and artifacts.

Use existing fixture batches for related cases. Measure producer work, proof compilation and
kernel replay separately; moving work between jobs or caches does not itself demonstrate a
reduction in total verification work.
