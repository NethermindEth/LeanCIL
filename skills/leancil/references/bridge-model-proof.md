# Connect existing model proofs to compiled code

The user has Lean definitions (a model or reference implementation) and theorems about them that
never mention CIL. LeanCIL cannot check those against a DLL directly: nothing yet says the
compiled method computes the model. Add one bridge theorem, then derive the guarantees about the
compiled method from the bridge and the existing theorems, without re-proving them.

Worked example, verified in LeanCIL's CI:
[Examples/Proofs/AddModel.lean](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/AddModel.lean).

## The three pieces

The snippets assume `open CIL` and the model's namespace.

1. **Model and its theorems**, already written and left unchanged. Here a `Nat` model:

   ```lean
   def addMod (a b : Nat) : Nat := (a + b) % 2 ^ 64
   theorem addMod_zero (a : Nat) (h : a < 2 ^ 64) : addMod a 0 = a
   ```

2. **Bridge**: for every input and caller memory, the extracted method succeeds and returns the
   model's result, converted to the CIL word type.

   ```lean
   theorem refines (x y : W64) (memory : Safety.Memory) :
       (Safety.invoke Extracted.program 4 0
         [.scalar (.i64 x), .scalar (.i64 y)] memory).map Prod.snd =
           .ok [.scalar (.i64 (BitVec.ofNat 64 (addMod x.toNat y.toNat)))] := by
     have model_eq : BitVec.ofNat 64 (addMod x.toNat y.toNat) = x + y := by
       apply BitVec.eq_of_toNat_eq
       simp [addMod, BitVec.toNat_add]
     rw [model_eq]
     rfl
   ```

3. **Transferred theorem**, the one passed to `--theorem`: a statement about the extracted
   method proved by rewriting with the bridge and applying the model theorem. A model hypothesis
   such as `a < 2 ^ 64` is discharged from the word type (`a.isLt`):

   ```lean
   theorem correctness (a : W64) (memory : Safety.Memory) :
       (Safety.invoke Extracted.program 4 0
         [.scalar (.i64 a), .scalar (.i64 0)] memory).map Prod.snd =
           .ok [.scalar (.i64 a)] := by
     rw [refines, show (0 : W64).toNat = 0 from rfl, addMod_zero a.toNat a.isLt,
       BitVec.ofNat_toNat, BitVec.setWidth_eq]
   ```

Verify the transferred theorem. It depends on the bridge, so the bridge is checked too, and the
model module is compiled and its hash recorded in `verified.json`.

## Writing the bridge

- `CIL.Safety.invoke program fuel methodIndex args memory` runs the method in the checked model.
  The entry method is index `0`. Fuel bounds the steps; the instruction count is enough for
  straight-line code.
- Arguments are `CIL.Safety.Value`s: `.scalar (.i64 w)` for 64-bit and `.scalar (.i32 w)` for
  32-bit integers. For narrower integers, references and spans, copy the argument shape from the
  closest proof in
  [Examples/Proofs](https://github.com/NethermindEth/LeanCIL/tree/main/Examples/Proofs).
  `CIL.W64` and `CIL.W32` are `BitVec 64` and `BitVec 32`.
- Convert the model's types explicitly in the statement where a reader can see them:
  `BitVec.ofNat 64 (model x.toNat ...)` for a `Nat` model, `(model ...).toBitVec` for `UInt64`.
  A conversion is usually not definitionally equal to the CIL result, so prove the model equals
  the word expression first (as `model_eq` above), rewrite, then close by `rfl`.
- Quantify over `memory : CIL.Safety.Memory` for methods that take and return scalars; it is the
  stronger statement and still closes by `rfl`. Methods reading or writing caller memory need
  preconditions describing it; use `MethodContract`
  ([contracts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md)).
- Do not import `Examples.Support` (for `Examples.empty`) in a package verified with
  `--proof-root`: the bundled library does not ship it there.
- Loops, calls and memory need the techniques in [write-new-proof.md](write-new-proof.md); the
  bridge is then the theorem being written.
- The bridge must cover every input the transferred theorem uses. If it needs a precondition
  (such as `y != 0` for division), the transferred theorem carries it too.
- Small rewriting traps: numeric literals elaborate as `OfNat` terms, so `BitVec.toNat_zero` may
  not match `(0 : W64).toNat`; `show (0 : W64).toNat = 0 from rfl` does.

## Package setup

Keep the model in the user's own Lake package with LeanCIL as a dependency. `lakefile.toml`:

```toml
name = "mylib_proofs"

[[require]]
name = "leancil"
git = "https://github.com/NethermindEth/LeanCIL.git"
rev = "<full commit of the LeanCIL release the installed leancil tool was built from>"

[[lean_lib]]
name = "MyLib"
```

- Use the `lean-toolchain` from that LeanCIL commit and run `lake update`.
- The pinned LeanCIL `CIL` sources must match the framework bundled with the installed tool;
  `verify` rejects a mismatch, so a wrong pin is caught rather than silently used.
- Put the model in `MyLib/Model.lean` and the bridge in `MyLib/AddBridge.lean`, starting with
  `import Extracted` and `import MyLib.Model`. Lean requires imports before the `/-! -/` module
  docstring.
- `Extracted` exists only inside `verify`, so `lake build` of the package cannot build the bridge.
  Build the model alone with `lake build MyLib.Model`; check the bridge with `verify`, or in a
  `leancil workspace` (see [write-new-proof.md](write-new-proof.md)).
- Verify with the package root:

  ```sh
  leancil verify artifacts/Method --proof MyLib/AddBridge.lean --proof-root . --theorem MyLib.correctness
  ```

- `verify` substitutes its bundled framework for the `leancil` dependency, so the warning
  `manifest out of date: source kind (git/path) of dependency 'leancil' changed` is expected; do
  not run `lake update leancil` because of it.
- `verification.json` stores the proof and `--proof-root` as paths relative to the artifact
  directory. After moving either, pass `--proof` and `--proof-root` again.

Package rules and the editor workspace are described in
[consumer packages](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md).

## Check the statement, not just the pass

The transferred theorem is what the user gets. Make sure it says the method *succeeds* with the
expected result. A purely relational statement ("both orders give equal outcomes") also holds
for a method that always fails, so the worked example keeps success in the statement. The
theorem compares returned values only; say so if the user also cares about memory effects.
