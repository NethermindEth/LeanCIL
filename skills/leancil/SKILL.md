---
name: leancil
description: Check that compiled .NET code (C#, F#) satisfies Lean 4 proofs using LeanCIL. Use when someone wants to verify a .NET method or assembly against a Lean theorem, run or debug `leancil extract`, `leancil check` or `leancil verify`, connect existing Lean proofs about a model or specification to their compiled library, or write a new LeanCIL proof about a method's CIL.
---

# Verifying compiled .NET code with LeanCIL

LeanCIL extracts the CIL of a compiled method into Lean and checks a named Lean theorem about
it. A pass means exactly that theorem holds for those compiled bytes under LeanCIL's CIL model;
nothing more. Documentation: https://github.com/NethermindEth/LeanCIL/tree/main/docs

## Pick the path

Ask what the user already has, then read only the matching reference:

| The user has | Path | Reference |
| --- | --- | --- |
| A Lean proof written against LeanCIL's extracted code (`import Extracted`) | Run the check | [references/check-existing-proof.md](references/check-existing-proof.md) |
| Lean definitions and theorems about a model or spec that never mention CIL | Write one bridge theorem, then check | [references/bridge-model-proof.md](references/bridge-model-proof.md) |
| Only the code and an informal requirement | Write the proof | [references/write-new-proof.md](references/write-new-proof.md) |

Proofs in another system (Coq, Dafny, F*, TLA+) or about C# source cannot be checked directly:
restate the property as Lean definitions and take the model path.

## Commands every path uses

The tool is the `Nethermind.LeanCIL` .NET tool (`leancil`); it needs Lean through elan at the
version pinned in LeanCIL's `lean-toolchain`. Build the assembly in Release first.

```sh
leancil list path/to/Lib.dll                                   # canonical method selectors
leancil extract path/to/Lib.dll 'Type::Method(ulong,ulong)' artifacts/Method [profile]
leancil check artifacts/Method                                 # artifacts still match the DLL
leancil verify artifacts/Method --proof proofs/Method.lean --theorem MyProof.correctness
```

- The selector needs the parameter list. C# aliases (`ulong`) and an unqualified type name are
  accepted when unique; `leancil list` prints the full forms. Use `ulong&` for `ref`/`out`.
  Several types can declare a method with the same name and parameters: the `Entry:` line of
  `verify` shows the method actually checked; report it, and ask the user when the choice is unclear.
- The profile defaults to `scalar` (no hardware intrinsics). Built-in names are `scalar`,
  `x64-sse2`, `x64-sse42`, `x64-v3`, `x64-v4` and `arm64-advsimd`; custom ones are JSON
  ([runtime profiles](https://github.com/NethermindEth/LeanCIL/blob/main/docs/RUNTIME-PROFILES.md)).
  Pick the one matching the deployment; if the user does not say, use `scalar` and state it.
  The profile is recorded and `check`/`verify` reuse it.
- `--theorem` defaults to `ExampleProof.correctness`. The first `verify` saves proof and theorem
  in `verification.json`, so later runs need only `leancil verify artifacts/Method`.
- `Extracted` (the generated code) and `CIL.*` ship with the tool. `Examples.Support` (example
  caller memories such as `Examples.empty`) is available only to single-file proofs. Proofs that
  import the user's own Lean modules need `--proof-root <lake package root>`; see the model
  reference for the package setup.
- After changing the C# code, rebuild and re-run `extract` before `verify`; `check` reports a
  changed assembly.

## Report a result honestly

On success `verify` prints `Verified: <theorem>`, the axioms, and the elaborated `Statement:`,
and writes `verified.json`. Statements usually run the method with
`CIL.Safety.invoke program fuel methodIndex args memory`: the entry method is index `0`, `args`
are the argument values and `memory` is the caller memory. Before telling the user the code is
verified, read the printed statement and confirm:

- It quantifies over every input the user cares about, not a few concrete values.
- The caller memory is either quantified or a fixed one such as `Examples.empty` (no
  allocations). A fixed memory is an assumption to state; it is harmless only for methods that
  take and return scalars and never touch memory.
- It states success with a result (`= .ok ...` or `Ensures`), not only a relation between
  outcomes; "equal for both argument orders" also holds for a method that always fails.
- Its preconditions are ones callers actually guarantee, and none of them contradict each other.
- The profile matches the deployment. It is not part of the statement: `leancil check` prints it
  and `identity.json` records it. `--assume-initialized` types are printed with the statement as
  preconditions and must hold in the deployment too.
- Axioms are only `propext`, `Quot.sound` and `Classical.choice`; `verify` rejects anything else.

Say what the theorem guarantees in plain words, and name what it does not cover: the JIT,
runtime and hardware are trusted, not proved
([soundness boundary](https://github.com/NethermindEth/LeanCIL/blob/main/docs/SOUNDNESS.md)).

On failure `verify` exits nonzero, prints `Invalid:` with the Lean errors, and writes
`failed.json`, whose `kind` classifies the failure (`stale-input`, `unsupported-extraction`,
`unsolved-goal`, `resource-limit`, ...) and whose `rerun` repeats the request
([failure reports](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#failure-reports)).

## Rules

- Never weaken the theorem, add a precondition, or change the method under test to make a proof
  pass. If the property does not hold or the code is outside the supported subset, report that.
- No `sorry`, `admit`, custom `axiom`, or `native_decide`; the verifier rejects them anyway.
- Editor checks (`lake build`, `leancil workspace`) are not verification. Only `leancil verify`
  produces a result to report.
- A theorem about fixed argument values is a test, not a contract; say so.
- Unsupported features (class allocation, virtual dispatch, recursion, exception handlers,
  floating point, arbitrary external calls) fail at `extract` with the rejected item named;
  report it rather than rewriting the user's code without asking.
