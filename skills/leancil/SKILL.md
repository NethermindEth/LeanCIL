---
name: leancil
description: Verify compiled .NET code (C#, F#) against Lean 4 theorems with the `leancil` tool and the `CIL` Lean library. Use when asked to prove or check a property of a .NET method or assembly, run or debug a `leancil` command (`extract`, `check`, `new-proof`, `verify`, `verify-batch`, `gates`, `workspace`, `watch`), connect existing Lean model proofs to a compiled method, write a new LeanCIL proof, verify many methods or profiles of a library, or diagnose a failed extraction or verification.
---

# Verifying compiled .NET code with LeanCIL

`leancil` extracts the CIL of a compiled method into Lean and checks a named Lean theorem about
it. A pass means that theorem holds for those compiled bytes under LeanCIL's CIL model and the
theorem's own hypotheses.

## Paths

Find out what the user has, then read only the matching reference.

| The user has | Task | Reference |
| --- | --- | --- |
| A Lean proof that imports `Extracted` and states a theorem about `Extracted.program` | Run it against the assembly | [references/check-existing-proof.md](references/check-existing-proof.md) |
| Lean definitions and theorems about a model or specification that never mention CIL | Write one bridge theorem, then verify | [references/bridge-model-proof.md](references/bridge-model-proof.md) |
| Only the code and an informal requirement | Write the specification and the proof | [references/write-new-proof.md](references/write-new-proof.md) |
| Proofs for many methods, profiles or assembly variants of one library | Run them as a catalog or a batch | [references/verify-library.md](references/verify-library.md) |
| A `leancil` command or a proof step that failed | Look up the message | [references/failures.md](references/failures.md) |

For a proof in another system (Coq, Dafny, F*, TLA+) or about C# source, restate the property as
Lean definitions and follow the model reference.

## Shared commands

`leancil` is the .NET tool `Nethermind.LeanCIL`. It needs the .NET SDK and Lean through elan, at
the toolchain `leancil --version` prints
([install](https://github.com/NethermindEth/LeanCIL/blob/main/docs/GETTING-STARTED.md#install)).
Build the assembly in Release before extracting.

```sh
leancil --version                              # tool, LeanCIL revision, Lean toolchain
leancil list path/to/Lib.dll                   # canonical selector of every method
leancil extract path/to/Lib.dll 'Type::Method(ulong,ulong)' artifacts/Method [profile]
                                               # writes Extracted.lean and identity.json
leancil check artifacts/Method                 # artifacts match the DLL; runs no Lean
leancil verify artifacts/Method --proof proofs/Method.lean --theorem MyProof.correctness
```

- A selector needs the parameter list. C# aliases (`ulong`), an optional return type and an
  unqualified type name work when the result is unique; `ulong&` is a `ref` or `out` parameter.
  An ambiguous selector fails with the candidate signatures.
- The profile is `scalar` (the default, no hardware intrinsics), `x64-sse2`, `x64-sse42`,
  `x64-v3`, `x64-v4`, `arm64-advsimd` or a custom `@profile.json`
  ([runtime profiles](https://github.com/NethermindEth/LeanCIL/blob/main/docs/RUNTIME-PROFILES.md#profile-selection)).
  A result holds for the extracted profile only, so extract and verify once per deployment
  profile; when the user names none, use `scalar` and say so. `check` and `verify` read the
  profile from `identity.json`.
- `--proof` defaults to `Proof.lean` in the output directory and `--theorem` to
  `ExampleProof.correctness`. The first `verify` saves both in `verification.json`, so later
  runs need only `leancil verify artifacts/Method`.
- A proof imports `Extracted` and the `CIL` modules; the tool does not ship LeanCIL's example
  and test modules. Importing the user's own modules needs `--proof-root`
  ([package setup](references/bridge-model-proof.md#package-setup)).
- After a rebuild of the assembly, `verify` extracts again by itself. `check` and `verify-batch`
  fail on the changed assembly as stale until `extract` runs again.
- The first `verify` on a machine builds and kernel-replays the framework library for several
  minutes, with progress on stderr. Later runs reuse it.
- A command exits with `0` on success and `1` on failure. A failure prints `Invalid:` or
  `Error:`, a `Stage:` line and a `Next:` line on stderr; a failed `verify` also removes any
  earlier `verified.json` and writes `failed.json` ([failures](references/failures.md)).

## Limits

State these limits to the user before promising a result.

- `extract` accepts Release, IL-only .NET 11 assemblies, and every profile is 64-bit
  little-endian. It validates the selected method and every method reachable from it, and rejects
  an unsupported instruction, call, type or signature by name at the stage
  `metadata and CIL validation`. `leancil list` validates nothing.
- Outside the supported subset are interface calls, virtual dispatch outside the extracted
  classes, type tests against interfaces, `System.Object` or value types, boxing, ordinary
  recursion, exception handlers, floating point, reading a string's characters and arbitrary
  external calls. Classes, arrays, spans, structs and SIMD intrinsics are supported
  with restrictions; look an instruction or call up in the
  [opcode table](https://github.com/NethermindEth/LeanCIL/blob/main/docs/OPCODES.md#unsupported-opcodes)
  and the [intrinsic tables](https://github.com/NethermindEth/LeanCIL/blob/main/docs/SIMD.md).
- A method on a type with a static constructor is rejected unless `extract` is given
  `--assume-initialized Namespace.Type`. The flag records an unproved caller precondition that
  the type initialized successfully before the call, and `verify` prints it with the theorem.

## Reporting a result

On success `verify` writes `verified.json` and prints `Verified: <theorem>`, `Subject:` (each
method the statement's conclusion is about), `Extraction entry:`, `Axioms:`, the elaborated
`Statement:` and, under `Specification:`, the proof file's definitions the statement names.
Before telling the user the code is verified, read the statement and specification and confirm
each point.

- `Subject:` names the method the user asked about. Several types can declare a method with the
  same name and parameters, and a theorem can concern a callee instead of the extraction entry.
- The statement quantifies over every input the user cares about. A theorem about fixed argument
  values is a test of those values.
- The caller memory is quantified, or is a fixed one such as `CIL.Safety.Memory.empty` (no
  allocations). A fixed memory is an assumption to state; it is harmless only for a method that
  takes and returns scalars and never touches caller memory.
- The statement asserts success with a result (`= .ok ...`, `Ensures` or a contract's `Holds`).
  A relation between two outcomes, such as "equal for both argument orders", also holds for a
  method that always fails.
- Callers guarantee every precondition, and the preconditions do not contradict each other.
- The profile, which `leancil check` prints, and each `--assume-initialized` type match the
  deployment.
- `Axioms:` lists only `propext`, `Quot.sound` and `Classical.choice`. `verify` rejects a
  theorem that depends on any other with `Unapproved proof axioms:` at the stage `theorem audit`.

Then quote the theorem name, the `Subject:` line and the profile, and say in plain words what the
theorem guarantees and what remains trusted: the CIL and memory model's correspondence to the
CLR, the extractor's metadata and token resolution and its translation of instructions outside the checked families, the modeled runtime helpers, the JIT, the runtime and the hardware
([soundness boundary](https://github.com/NethermindEth/LeanCIL/blob/main/docs/SOUNDNESS.md#trusted-components-and-deployment-assumptions)).
The theorem covers the compiled CIL; it says nothing about whether the specification is the one
the user needs.

## Rules

- Never weaken the theorem, add a precondition or change the method under test to make a proof
  pass. When the property does not hold or the code is outside the supported subset, report
  that; do not rewrite the user's code to avoid an unsupported construct without asking.
- Write no `sorry`, `admit`, custom `axiom` or `native_decide`: each adds an axiom the audit
  rejects.
- Report a result only from `leancil verify`, `leancil gates` or `leancil verify-batch` without
  `--check`. An editor check, `lake build`, `leancil workspace` and `--check` issue no
  certificate.
