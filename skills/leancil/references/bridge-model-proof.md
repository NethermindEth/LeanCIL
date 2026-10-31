# Connect existing model proofs to compiled code

The user has Lean definitions (a model or reference implementation) and theorems about them that
never mention CIL. LeanCIL cannot check those against a DLL directly: nothing yet says the
compiled method computes the model. Add one bridge theorem, then derive the guarantees about the
compiled method from the bridge and the existing theorems, without re-proving them.

Worked example, verified in LeanCIL's CI:
[Examples/Proofs/AddModel.lean](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/AddModel.lean).

## The three pieces

1. **Model and its theorems** (already exist, unchanged):
   `def model (x y : W64) : W64 := x + y` and `theorem model_comm : model x y = model y x`.
2. **Bridge**: for every input, the extracted method succeeds and returns exactly the model's
   result.

   ```lean
   theorem refines (x y : W64) :
       (CIL.Safety.invoke Extracted.program 4 0
         [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
           .ok [.scalar (.i64 (model x y))] := rfl
   ```

3. **Transferred theorem**, the one passed to `--theorem`: a statement about the extracted
   method proved only by rewriting with the bridge and applying the model theorem. In the example,
   `correctness` states that both argument orders succeed with one shared result, proved by
   `refines` and `model_comm`.

Verify the transferred theorem. Because it depends on the bridge, the bridge is checked too; the
model theorems are checked as ordinary Lean.

## Writing the bridge

- `CIL.Safety.invoke program fuel methodIndex args memory` runs the method in the checked model.
  The entry method is index `0`. Fuel bounds the steps; choose enough for the method.
- Arguments are `CIL.Safety.Value`s: `.scalar (.i64 w)` for 64-bit and `.scalar (.i32 w)` for
  32-bit integers. For narrower integers, references and spans, copy the argument shape from the
  closest proof in
  [Examples/Proofs](https://github.com/NethermindEth/LeanCIL/tree/main/Examples/Proofs).
  `CIL.W64` and `CIL.W32` are `BitVec 64` and `BitVec 32`.
- If the model uses other types (`Nat`, `UInt64`, a structure), state the bridge through an
  explicit conversion, e.g. `.i64 (model' a b).toBitVec`, and keep the conversion in the
  statement where a reader can see it.
- `Examples.empty` (from `import Examples.Support`) is a caller memory with no allocations, enough
  for methods that take and return scalars. Methods reading caller memory need a memory and
  preconditions describing it; use `MethodContract`
  ([contracts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md)).
- Straight-line methods often close by `rfl`. Loops, calls and memory need the techniques in
  [write-new-proof.md](write-new-proof.md); the bridge is then the theorem being written.
- The bridge must cover every input the transferred theorem quantifies over. If it needs a
  precondition (such as `y != 0` for division), the transferred theorem carries it too.

## Package setup

Keep the model in the user's own Lake package with LeanCIL as a dependency. `lakefile.toml`:

```toml
name = "mylib_proofs"

[[require]]
name = "leancil"
git = "https://github.com/NethermindEth/LeanCIL.git"
rev = "<full commit of the LeanCIL version the installed leancil tool was built from>"

[[lean_lib]]
name = "MyLib"
```

- Copy LeanCIL's `lean-toolchain` into the package and run `lake update`.
- The pinned LeanCIL `CIL` sources must match the framework bundled with the installed tool;
  `verify` rejects a mismatch. Dependencies must be git packages pinned to full revisions.
- Put the model in a module such as `MyLib/Model.lean`, and the bridge proof in a file under the
  package that starts with `import Extracted`, `import Examples.Support` and `import MyLib.Model`.
  `Extracted` is supplied by `verify`; do not create it.
- Verify with the package root:

  ```sh
  leancil verify artifacts/Method --proof MyLib/AddBridge.lean --proof-root . --theorem MyLib.correctness
  ```

Package rules and the editor workspace are described in
[consumer packages](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md).

## Check the statement, not just the pass

The transferred theorem is what the user gets. Make sure it says the method *succeeds* with the
model's result. A purely relational statement ("both orders give equal outcomes") also holds
for a method that always fails, so the example keeps success in the statement.
