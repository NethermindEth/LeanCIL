# Check an existing LeanCIL proof

Read this when the user has a `.lean` file that imports `Extracted` and states a theorem about
`Extracted.program`. Run it against their compiled assembly and report the result.

## Inputs

1. Build the assembly in Release and use that DLL. When the user hands over only a DLL, say that
   its build configuration and source are unverified.
2. Find the method selector. When the proof's author did not record it, run
   `leancil list Lib.dll` and match the signature the proof expects: the parameter count and
   types in its `invoke` arguments, or the signature string of its `bind_method`. When several
   types declare a matching method, ask which one, or report the one you checked.
3. Use the profile the proof was written for; the author's `identity.json` records it. Otherwise
   ask, and without an answer use `scalar` and say so.
4. Take the fully qualified theorem name from the proof: its `namespace` followed by the theorem
   to certify, usually the last in the file, such as `MyProof.correctness`.
5. A proof that imports the user's own modules needs `--proof-root` pointing at their Lake
   package ([package setup](bridge-model-proof.md#package-setup)). A proof that imports a keyed
   module `Extracted.KEY` was written in a `leancil workspace` package; `verify` accepts that
   import for the matching extraction only.
6. `extract` names each type with a static constructor and the `--assume-initialized` flag it
   needs. Pass the flag only when every caller runs that constructor first.

## Commands

```sh
dotnet build path/to/Lib.csproj -c Release
leancil extract path/to/bin/Release/net11.0/Lib.dll 'Type::Method(ulong,ulong)' artifacts/Method [profile]
leancil verify artifacts/Method --proof proofs/Method.lean --theorem MyProof.correctness
```

Add `--proof-root .` for a Lake package and `--fresh` to bypass reuse of an earlier result. In CI
after a rebuild, `leancil verify artifacts/Method` is enough: the saved settings supply the proof
and theorem, and `verify` extracts again when the assembly changed.

## Outcome

On success, audit the printed statement as "Reporting a result" in SKILL.md describes before
telling the user. On failure, look the `kind` in `artifacts/Method/failed.json` and the `Stage:`
line up in [failures.md](failures.md).

Wrong code and a broken proof both end at `proof checking` with an unsolved goal or a failed
tactic. Decide which one it is before changing anything:

- When the proof passed before a code change and fails after it, the code probably changed
  behavior. Compare the old and new C# and report the difference. Leave the proof as it is.
- When the proof fails against unchanged code after a tool update, a tactic or lemma name it
  uses may differ in the installed framework. Updating those names is proof maintenance and says
  nothing about the code.
- `leancil verify artifacts/Method --goals` prints the goal before the failing tactic; read it to
  see what the proof could not establish about the compiled code.

## Example

From a LeanCIL checkout, the shipped addition proof checks like this:

```sh run
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

Running the same proof against `Arithmetic::WrongAdd(ulong,ulong)`, which subtracts, fails with
kind `elaboration-error` and the message ``Tactic `rfl` failed``.
