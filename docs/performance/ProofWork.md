# Proof work measurements

<!-- audience: maintainers -->

This page describes how to time the elaboration of one `CIL/` module, and which proof forms keep
the slowest safety modules fast. Read it before changing a proof in `CIL/Safety/`, where one
module can take a minute to compile. For the cost of proofs in tests and extracted output, use
[proof cost](ProofCost.md) instead.

## Timing a module

Build the module and its imports once, then compile the source file alone:

```sh
lake build CIL.Safety.Embedding.Step
lake env lean -Dprofiler=true CIL/Safety/Embedding/Step.lean
```

The command recompiles the file and writes nothing. Its time covers process startup, imports,
elaboration and kernel checking of that file; it excludes Lake's dependency rebuilding, olean
serialization and independent replay. Add `-o <file>.olean` to include serialization.

To compare a change, time the base and the changed source against the same compiled imports, in
one session, with nothing else running:

- Discard the first run after a build; its imports are cold.
- Alternate the two versions and run each at least twice. Report the spread across runs.
- The profiler's cumulative counters (`simp`, `dsimp`, type checking) overlap. Use them to find
  where time goes, not as additive savings.
- Modules compile concurrently in a build. Do not add module savings to predict the time of a
  cold library build or of a CI job.

After a change, check that the theorem statements and the `#print axioms` reports of the module
are unchanged, and that the compiled module passes `leanchecker` replay.

## Reference figures

The figures were taken with Lean 4.35.0, warm imports and no concurrent benchmark. Compare only
with a time taken on the same machine class and with the same options.

| Module | Seconds | Machine and options |
| --- | ---: | --- |
| `CIL/Safety/Embedding/Step.lean` | 49.14 | Linux x86-64 under WSL on ext4, `-j2 -Dprofiler=true` |
| `CIL/Safety/Embedding/Step.lean`, writing its olean | 53.22 | as above |
| `CIL/Safety/StepFlow.lean` | 21.79 | Windows, AMD Ryzen 9 9950X |
| `CIL/Safety/Embedding/AppendLocals.lean` | 21.10 | Windows, AMD Ryzen 9 9950X |
| `CIL/Safety/InstructionRenaming.lean` | 10.31 | Windows, AMD Ryzen 9 9950X, `-Dprofiler=true` |
| `CIL/Safety/AllocatingStepRenaming.lean` | 7.30 | Windows, AMD Ryzen 9 9950X, `-Dprofiler=true` |

In the `Step.lean` run the cumulative `simp` counter is 12.7 s and `dsimp` 14.8 s.

## Instruction-family proofs

Close impossible operand cases before inspecting the next operand. A padding proof can apply
the dispatcher-tail theorem as soon as the first operand is invalid. When a bind succeeds,
extract its result so the remaining proof only covers the successful branch.

In `step_observers`, unfold `observerCount` with `dsimp`. The hypotheses produced by
`observer_ok` and `observer_thrown` already describe the result, so only the goal needs the
observer guard simplified.

Use a memory instruction's dispatch equation to rewrite its step directly. In
`instructionResult`, rewrite the outer guard and try the write correspondence first. Trying the
read lemma on a write forces the kernel to reduce the write while matching the lemma.
