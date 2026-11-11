# Proof work measurements

<!-- audience: maintainers -->

How to time the elaboration of one `CIL/` module, and which proof forms keep the slowest safety
modules fast. Read it before changing a proof in `CIL/Safety/`, where one module can take a
minute to compile. For the cost of proofs in tests and extracted output, use
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
- Run each side at least twice. On a one-minute module one pair measured a saving of 5.0 s and
  its repeat 3.4 s, so one pair does not resolve a difference of a few percent.
- The profiler's cumulative counters (`simp`, `dsimp`, type checking) overlap. Use them to find
  where time goes, not as additive savings.
- Modules compile concurrently in a build. Do not add module savings to predict the time of a
  cold library build or of a CI job.

After a change, check that the theorem statements and the `#print axioms` reports of the module
are unchanged, and that the compiled module passes `leanchecker` replay.

## Reference figures

Lean 4.35.0, warm imports, no concurrent benchmark. Compare only with a time taken on the same
machine class and with the same options.

| Module | Seconds | Machine and options |
| --- | ---: | --- |
| `CIL/Safety/Embedding/Step.lean` | 49.14 | Linux x86-64 under WSL on ext4, `-j2 -Dprofiler=true` |
| `CIL/Safety/Embedding/Step.lean`, writing its olean | 53.22 | as above |
| `CIL/Safety/StepFlow.lean` | 21.79 | Windows, AMD Ryzen 9 9950X |
| `CIL/Safety/Embedding/AppendLocals.lean` | 21.10 | Windows, AMD Ryzen 9 9950X |
| `CIL/Safety/InstructionRenaming.lean` | 10.31 | Windows, AMD Ryzen 9 9950X, `-Dprofiler=true` |
| `CIL/Safety/AllocatingStepRenaming.lean` | 7.30 | Windows, AMD Ryzen 9 9950X, `-Dprofiler=true` |

In the `Step.lean` run the cumulative `simp` counter is 12.7 s and `dsimp` 14.8 s.

## Proof forms that keep these modules fast

Each instruction-family proof in these modules traverses the full instruction dispatcher, so a
redundant traversal is paid once per family. The figures are the cost of the slower form on the
same module.

| Keep | Instead of | Cost of the slower form |
| --- | --- | --- |
| Close each operand-shape case before inspecting the next operand | Splitting all operands, then closing the impossible cases | These three together: `Step.lean` 55%, `StepFlow.lean` 43% and `AppendLocals.lean` 17% slower; the `Step.lean` olean 51% larger |
| Try the dispatcher-tail theorem first in padding proofs | Repeating that proof for every second-operand constructor when the first operand is invalid | included above |
| Extract the successful result of a bind | Expanding the bind's impossible error branch | included above |
| `dsimp` to unfold `observerCount` in `step_observers`, where definitional equality suffices | `simp`, which builds congruence proofs over the dispatcher | `Step.lean` 26% to 29% slower |
| Simplify the observer guard in the goal only; the hypothesis from `observer_ok` or `observer_thrown` does not contain it | Simplifying the normalized hypothesis as well | `Step.lean` 6% to 10% slower |
| Rewrite with `step_memory_eq` in `stepMemory` | Unfolding the instruction dispatcher | 5,451 heartbeats against 602 |
| Rewrite the outer guard directly and try the write correspondence before the read correspondence in `instructionResult` | The reverse order, which reduces a write while matching a read lemma that cannot apply | 264,632 heartbeats against 227,277 |
