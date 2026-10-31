# Check an existing LeanCIL proof

The user has a `.lean` file that imports `Extracted` and states a theorem about
`Extracted.program`. The job is to run it against their compiled assembly and report the result.

## Gather the inputs

1. The assembly: build it in Release and use that DLL, not a Debug or stale build.
2. The method selector: if the proof's author did not record it, run `leancil list Lib.dll` and
   match the signature the proof expects (parameter count and types in its `invoke` arguments).
3. The profile: the one the proof was written for. Profile names and what they assume are in
   [runtime profiles](https://github.com/NethermindEth/LeanCIL/blob/main/docs/RUNTIME-PROFILES.md).
4. The theorem name: the fully qualified name, such as `MyProof.correctness`.
5. Whether the proof imports the user's own modules. If it does, it needs `--proof-root` pointing
   at their Lake package (setup in [bridge-model-proof.md](bridge-model-proof.md#package-setup)).
6. Any `--assume-initialized` types the extraction needs (types with static constructors).

## Run

```sh
dotnet build path/to/Lib.csproj -c Release
leancil extract path/to/bin/Release/net10.0/Lib.dll 'Type::Method(ulong,ulong)' artifacts/Method [profile]
leancil verify artifacts/Method --proof proofs/Method.lean --theorem MyProof.correctness
```

Add `--proof-root .` for a Lake package and `--fresh` to bypass proof reuse. Later runs, such as
in CI after a rebuild, only need `extract` (to pick up the new DLL) and `leancil verify
artifacts/Method`.

## Read the outcome

Success: audit the printed `Statement:` as described in SKILL.md before reporting.

Failure: read `artifacts/Method/failed.json` and act on `kind`:

| `kind` | Meaning | Next step |
| --- | --- | --- |
| `stale-input` | The DLL or artifacts changed after extraction | Re-run `extract`, then `verify` |
| `unsupported-extraction` | The method or something it calls is outside the supported subset | Report the named item; see [opcodes](https://github.com/NethermindEth/LeanCIL/blob/main/docs/OPCODES.md) |
| `invalid-request` | Proof path or theorem name is wrong | Fix `--proof` / `--theorem` |
| `elaboration-error` | Any other Lean error: a failed tactic (`Tactic rfl failed`), missing import, renamed API | A failed tactic can mean the code is wrong; see below. Otherwise fix the proof |
| `unsolved-goal` | A tactic block left goals open | The code may not satisfy the theorem; see below |
| `resource-limit` | Heartbeats or recursion depth ran out | Report it; do not raise limits blindly |
| `replay-or-audit-rejected` | Kernel replay or the axiom audit failed | Treat as a failed proof; look for `sorry` or extra axioms |

LeanCIL does not tell "the code is wrong" apart from "the proof is broken": both surface as
`unsolved-goal` or as an `elaboration-error` whose first message is a failed tactic. A proof that
passed before a code change and fails after it usually means the code changed behavior, which is
the check doing its job. Compare the old and new C# before touching the proof. A proof written for
an older LeanCIL version may also fail because tactic or lemma names changed; that is a proof
maintenance task, not evidence about the code.

## Example

From a LeanCIL checkout, the shipped addition proof checks like this:

```sh
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

Running the same proof against `Arithmetic::WrongAdd(ulong,ulong)`, which subtracts, fails with
kind `elaboration-error` and the message ``Tactic `rfl` failed``.
