# Write a new LeanCIL proof

The user has code and an informal requirement. Write the specification first, then the proof.

## 1. State the property before looking at the CIL

Write what the method must do as ordinary Lean, independent of the instructions it compiles to:
a model function, a postcondition, or both. Make every input quantifier, precondition on the
inputs or caller memory, and permitted write explicit. If the user already has such definitions,
follow [bridge-model-proof.md](bridge-model-proof.md) instead.

Agree the statement with the user before proving it. A proof of the wrong statement is the most
expensive failure here, and LeanCIL cannot detect it.

## 2. Choose the smallest proof interface

| Method shape | Start from | Guide |
| --- | --- | --- |
| Straight-line arithmetic | [Add](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Add.lean) | [instruction composition](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md#compose-instructions) |
| Calls helper methods | [CountCalls](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/CountCalls.lean) | [contract composition](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#compose-calls-through-contracts) |
| Contains a loop | [Countdown](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/Countdown.lean) | [loop cutpoints](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#loop-heads-and-call-sites) |
| Writes a buffer or span | [FillWords](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/FillWords.lean) | [buffer predicates](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BUFFERS.md) |
| Can throw | [CountUntil](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/CountUntil.lean) | [outcome contracts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#name-exceptional-outcomes) |

The full table is in [writing proofs](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS.md).
Copy the closest example's structure and change the statement first.

## 3. Iterate in a workspace, then verify

`leancil workspace` builds an editable Lake workspace with `Extracted` available, so the Lean
language server shows goals:

```sh
leancil workspace path/to/Lib.dll 'Type::Method(ulong)' --profile scalar --proof proofs/Method.lean --proof-root .
```

Edit `LeanCILProofWorkspace.lean` there and check it with
`lake build +LeanCILProofWorkspace:olean`. When it builds, copy the proof back to
`proofs/Method.lean` and run `leancil extract` and `leancil verify`. Only `verify` counts.
Details: [editor workspace](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md#proof-authoring-workspace).

## 4. Keep the proof local

- Prove each helper's `MethodContract` once and use it at call sites instead of unfolding the
  helper; caller proofs then survive helper rewrites.
- Loop invariants describe the state at a checked cutpoint; continuing iterations must decrease
  an explicit measure. A finite sample does not prove termination.
- End each theorem with `#print axioms` and confirm it lists no `sorryAx`.
- If a step does not reduce, check that the method and profile are the ones extracted, then read
  [stepping and reduction](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-STEPPING.md)
  before writing manual unfolding.

When the property fails, that is a result: show the user the failing case, or prove a
counterexample (see [WrongAdd](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/WrongAdd.lean)),
rather than weakening the statement.
