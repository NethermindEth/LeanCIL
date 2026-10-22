# AGENTS instructions

LeanCIL extracts .NET CIL into Lean and proves properties of the compiled code. Start with
[README](./README.md); [PROOFS](./docs/PROOFS.md), [SOUNDNESS](./docs/SOUNDNESS.md) and
[VALIDATION](./docs/VALIDATION.md) describe the automation, the trust boundary and the suites.

## Building and testing

- `lake build` builds only `CIL`. Before pushing a change under `CIL/`, build every library:
  `lake build $(sed -n 's/^name = "\(.*\)"/\1/p' lakefile.toml | tail -n +2)`.
- Run one suite with `dotnet run --file scripts/Test.cs -- --suite <name>`; names are in VALIDATION.
  Run concurrent suites in separate checkouts, since they build and mutate `artifacts/`.
- Stepping, return and contract tactics are shared by `Tests/Automation`, `Tests/StoreFacts`,
  `Tests/MethodContract`, the `loops` suite and the examples. A tactic change must pass all of them.

## Proofs and tests

- Never weaken a contract, precondition or soundness check to make a proof go through. Report an
  unsupported extraction or composition as an issue instead.
- End each new theorem with `#print axioms`; `sorryAx` in any build output is a failure, even
  when the build succeeds. Wrap it in `#guard_msgs` where the axiom set is part of the contract.
- Pin an intermediate simp form in a test only when that form is what the test checks.

## Pull requests

- Use conventional commits with an area scope, such as `feat(safety):` or `fix(examples):`.
- PRs that touch the same files go in one stack: the bottom PR on the head of `main`, each child
  based on its parent's branch, linked with `gh stack link <bottom> ... <top>`.
- Land a stack by merging its top PR once every PR in it is green. Never merge a PR into a parent
  branch that has already landed; its changes would never reach `main`.
- `main` is squash-merged. Once a branch is pushed, bring in `main` or its parent by merging, not
  rebasing, so CI and reviewers keep their history.
- Label issues with an issue type and an `area:` label; label PRs with a kind (`feature`,
  `bugfix & reliability`, `performance`, `refactor & cleanup`, `documentation`, `ci & build`,
  `tests`) and an `area:` label. Add `consumer: <name>` when a downstream project drives the work.
