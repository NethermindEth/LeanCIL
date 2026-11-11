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

LeanCIL checks Lean theorems about compiled CIL. For a proof in another system (Coq, Dafny, F*,
TLA+) or about C# source, restate the property as Lean definitions and follow the model reference.

## Shared commands

`leancil` is the .NET tool `Nethermind.LeanCIL`. It needs the .NET SDK and Lean through elan, at
the toolchain `leancil --version` prints. When `leancil` is not on `PATH`, install it as
[getting started](https://github.com/NethermindEth/LeanCIL/blob/main/docs/GETTING-STARTED.md#install)
describes. Build the assembly in Release before extracting.

```sh
leancil --version                              # tool, LeanCIL revision, Lean toolchain
leancil list path/to/Lib.dll                   # canonical selector of every method
leancil extract path/to/Lib.dll 'Type::Method(ulong,ulong)' artifacts/Method [profile]
leancil check artifacts/Method                 # artifacts match the DLL; runs no Lean
leancil verify artifacts/Method --proof proofs/Method.lean --theorem MyProof.correctness
```

- A selector needs the parameter list. C# aliases (`ulong`), an optional return type and an
  unqualified type name are accepted when the result is unique; use `ulong&` for `ref` and `out`.
  An ambiguous selector fails with the candidate signatures to copy.
- The profile is the fourth positional argument of `extract` and defaults to `scalar` (no
  hardware intrinsics). The built-in names are `scalar`, `x64-sse2`, `x64-sse42`, `x64-v3`,
  `x64-v4` and `arm64-advsimd`; `@profile.json` names a custom one
  ([runtime profiles](https://github.com/NethermindEth/LeanCIL/blob/main/docs/RUNTIME-PROFILES.md#profile-selection)).
  Use the profile of the deployment. When the user names none, use `scalar` and say so.
  `identity.json` records the profile, and `check` and `verify` read it from there.
- `extract` writes `Extracted.lean` and `identity.json` into the output directory. Keep that
  directory outside the Lake package that holds the proofs.
- `--theorem` defaults to `ExampleProof.correctness` and `--proof` to `Proof.lean` in the output
  directory. The first `verify` saves both in `verification.json`, so later runs need only
  `leancil verify artifacts/Method`.
- A proof imports `Extracted` (the generated program) and the framework's `CIL` modules. The
  tool does not ship LeanCIL's own example and test modules. A proof that imports the user's own
  Lean modules needs `--proof-root <Lake package root>`
  ([package setup](references/bridge-model-proof.md#package-setup)).
- After a rebuild of the assembly, `verify` extracts again from the recorded settings and prints
  `Re-extracted <directory>: the assembly changed since extraction.` `check` and `verify-batch`
  report the changed assembly as stale instead; run `extract` again for them.
- The first `verify` on a machine builds and kernel-replays the framework library, which takes
  several minutes and reports progress on stderr. Later runs reuse the cached library.
- `--fresh` bypasses reuse of earlier proof results. `--format json` prints one JSON report on
  stdout, `--goals` prints the open goals of an unfinished proof and `--trace` logs each step the
  proof takes ([failures](references/failures.md)).

Every command exits with `0` on success and `1` on failure. A failure prints `Invalid:` or
`Error:`, a `Stage:` line and a `Next:` line on stderr.

## Limits

State these limits to the user before promising a result.

- `extract` accepts Release, IL-only .NET 10 assemblies for 64-bit little-endian execution. It
  validates the selected method and every method reachable from it, and rejects an unsupported
  instruction, call, type or signature with the item named, at the stage
  `metadata and CIL validation`. `leancil list` prints methods without validating them.
- These are outside the supported subset: interface calls, virtual dispatch outside the
  extracted classes, type tests against interfaces, `System.Object` or value types, boxing,
  ordinary recursion, exception handlers, floating point, reading a string's characters and
  arbitrary external calls. Classes, arrays, spans, structs and SIMD intrinsics are supported with
  restrictions. Look an instruction or call up in the
  [opcode table](https://github.com/NethermindEth/LeanCIL/blob/main/docs/OPCODES.md#unsupported-opcodes)
  and the [intrinsic tables](https://github.com/NethermindEth/LeanCIL/blob/main/docs/SIMD.md).
- `leancil blockers assembly.dll --manifest blockers-manifest.json` reports every construct that
  blocks extraction of a list of methods, without stopping at the first
  ([blockers](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#report-extraction-blockers)).
  Run it before estimating work on a library.
- A method on a type with a static constructor is rejected unless `extract` is given
  `--assume-initialized Namespace.Type`. The flag records a caller precondition that the type
  initialized successfully before the call; LeanCIL does not prove it, and `verify` prints it
  with the theorem.
- A result holds for the extracted profile only. Extract and verify once per deployment profile.
- Report an unsupported construct to the user. Do not rewrite their code to avoid it without
  asking.

## Reporting a result

On success `verify` prints `Verified: <theorem>`, then `Subject:` (each method the statement's
conclusion is about), `Extraction entry:` (the method extraction started from), `Axioms:`, the
elaborated `Statement:` and, under `Specification:`, the proof file's definitions the statement
names, such as its precondition and postcondition. It writes `verified.json`. Before telling the
user the code is verified, read the printed statement and specification and confirm each point.

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
- The profile and each `--assume-initialized` type match the deployment. `leancil check` prints
  the profile.
- `Axioms:` lists only `propext`, `Quot.sound` and `Classical.choice`; `verify` rejects any other.

Then say in plain words what the theorem guarantees and what remains trusted: the CIL and memory
model's correspondence to the CLR, the extractor's decoding, the modeled runtime helpers, the
JIT, the runtime and the hardware
([soundness boundary](https://github.com/NethermindEth/LeanCIL/blob/main/docs/SOUNDNESS.md#trusted-components-and-deployment-assumptions)).
The theorem covers the compiled CIL; it says nothing about whether the specification is the one
the user needs.

On failure `verify` exits with `1`, removes any earlier `verified.json` and writes `failed.json`;
read [references/failures.md](references/failures.md).

## Rules

- Never weaken the theorem, add a precondition or change the method under test to make a proof
  pass. When the property does not hold or the code is outside the supported subset, report that.
- Write no `sorry`, `admit`, custom `axiom` or `native_decide`; `verify` rejects each.
- Report a result only from `leancil verify`, `leancil gates` or `leancil verify-batch` without
  `--check`. An editor check, `lake build`, `leancil workspace` and `--check` issue no
  certificate.
- Quote the verified theorem name, the `Subject:` line and the profile in the report to the user.
