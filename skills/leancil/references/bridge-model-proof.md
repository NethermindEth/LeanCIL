# Connect existing model proofs to compiled code

Read this when the user has Lean definitions (a model or reference implementation) and theorems
about them that never mention CIL. Those theorems say nothing about a DLL until a bridge theorem
states that the compiled method computes the model. Add that one theorem, then derive the
guarantees about the compiled method from the bridge and the existing theorems, without
re-proving them.

[Examples/Proofs/AddModel.lean](https://github.com/NethermindEth/LeanCIL/blob/main/Examples/Proofs/AddModel.lean)
is a complete proof of this form.

## Model, bridge and transferred theorem

The snippets assume `open CIL` and the model's namespace.

1. Leave the model and its theorems unchanged. This one is a `Nat` model:

   ```lean
   def addMod (a b : Nat) : Nat := (a + b) % 2 ^ 64
   theorem addMod_zero (a : Nat) (h : a < 2 ^ 64) : addMod a 0 = a := by
     simp [addMod, Nat.mod_eq_of_lt h]
   ```

2. Write the bridge: for every input and caller memory, the extracted method succeeds and
   returns the model's result, converted to the CIL word type.

   ```lean extracted
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

3. Write the transferred theorem, the one passed to `--theorem`: a statement about the extracted
   method, proved by rewriting with the bridge and applying the model theorem. The word type
   discharges a model hypothesis such as `a < 2 ^ 64` (`a.isLt`):

   ```lean extracted
   theorem correctness (a : W64) (memory : Safety.Memory) :
       (Safety.invoke Extracted.program 4 0
         [.scalar (.i64 a), .scalar (.i64 0)] memory).map Prod.snd =
           .ok [.scalar (.i64 a)] := by
     rw [refines, show (0 : W64).toNat = 0 from rfl, addMod_zero a.toNat a.isLt,
       BitVec.ofNat_toNat, BitVec.setWidth_eq]
   ```

Verify the transferred theorem. It depends on the bridge, so the bridge is checked too. Under
`--proof-root` the model module is compiled from source and `verified.json` binds its hash.

## Writing the bridge

- `CIL.Safety.invoke program fuel methodIndex args memory` runs the method in the checked model.
  The entry method is index `0`. Fuel bounds the steps; the instruction count is enough for
  straight-line code.
- Arguments are `CIL.Safety.Value`s: `.scalar (.i64 w)` for 64-bit and `.scalar (.i32 w)` for
  32-bit integers. For narrower integers, references and spans, run
  `leancil new-proof artifacts/Method Proofs/Method.lean` and copy the argument list of the
  theorem it states, or copy it from the closest proof in
  [Examples/Proofs](https://github.com/NethermindEth/LeanCIL/tree/main/Examples/Proofs).
  `CIL.W64` and `CIL.W32` are `BitVec 64` and `BitVec 32`.
- Convert the model's types explicitly in the statement where a reader can see them:
  `BitVec.ofNat 64 (model x.toNat ...)` for a `Nat` model, `(model ...).toBitVec` for `UInt64`.
  A conversion is usually not definitionally equal to the CIL result, so prove the model equals
  the word expression first (as `model_eq` above), rewrite, then close by `rfl`.
- Quantify over `memory : CIL.Safety.Memory` for a method that takes and returns scalars; that
  statement is stronger than one at a fixed memory and still closes by `rfl`.
  `CIL.Safety.Memory.empty`, a caller memory with no allocations, is the fixed alternative.
- A method that reads or writes caller memory needs preconditions describing that memory. State
  the bridge as a `MethodContract` whose `post` names the model
  ([contracts](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-CONTRACTS.md#compose-calls-through-contracts)).
- A method with a loop, a call or locals does not close by `rfl`. Prove the bridge with the
  tactics in [write-new-proof.md](write-new-proof.md); the bridge is then the theorem being
  written, with the model in its postcondition.
- The bridge must cover every input the transferred theorem uses. When the bridge needs a
  precondition (such as `y != 0` for division), the transferred theorem carries it too.
- Numeric literals elaborate as `OfNat` terms, so `BitVec.toNat_zero` may not rewrite
  `(0 : W64).toNat`; `show (0 : W64).toNat = 0 from rfl` does.

## Package setup

Keep the model in the user's own Lake package with LeanCIL as a dependency. `lakefile.toml`:

```toml
name = "mylib_proofs"

[[require]]
name = "leancil"
git = "https://github.com/NethermindEth/LeanCIL.git"
rev = "<the revision leancil --version prints>"

[[lean_lib]]
name = "MyLib"
```

- `leancil --version` prints this `[[require]]` block with the matching revision, and the Lean
  toolchain to put in the package's `lean-toolchain`. Then run `lake update`, which writes the
  `lake-manifest.json` verification requires.
- The pinned `CIL` sources must match the framework bundled with the installed tool. `verify`
  rejects a mismatch with `Consumer leancil sources differ from the verifier's bundled
  framework` and names the revision to pin.
- Every dependency must be a Git package pinned to a full revision. Local path dependencies and
  symlinked sources are not supported.
- Put the model in `MyLib/Model.lean` and the bridge in `MyLib/AddBridge.lean`, starting with
  `import Extracted` and `import MyLib.Model`. Lean requires imports before the `/-! -/` module
  docstring.
- Keep the `extract` output directory outside the package, for example under `artifacts/`, and
  keep no file named `Extracted.lean` among the package sources.
- `lake build` of the package cannot build the bridge, because `Extracted` is supplied only
  during verification. Build the model alone with `lake build MyLib.Model` and check the bridge
  with `verify`. For live goals in an editor, run `leancil workspace` and import the keyed module
  `Extracted.KEY` it prints instead of `Extracted` ([write-new-proof.md](write-new-proof.md)).
- Verify with the package root:

  ```sh
  leancil verify artifacts/Method --proof MyLib/AddBridge.lean --proof-root . --theorem MyLib.correctness
  ```

- `verify` substitutes its bundled framework for the `leancil` dependency, so the warning
  `manifest out of date: source kind (git/path) of dependency 'leancil' changed` is expected; do
  not run `lake update leancil` because of it.
- `verification.json` stores the proof and `--proof-root` as paths relative to the artifact
  directory. After moving either, pass `--proof` and `--proof-root` again.

The package rules are in
[consumer packages](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md#consumer-proof-packages).

## Statement audit

The transferred theorem is what the user gets. Make sure it says the method succeeds with the
expected result. A purely relational statement ("both orders give equal outcomes") also holds
for a method that always fails, so `AddModel.lean` keeps success in its statement. A theorem
stated through `.map Prod.snd` compares returned values only; say so when the user also cares
about memory effects.
