# Examples

## Independent examples

- `Add`: universal modular arithmetic correctness in the specified empty initial memory.
- `CheckedArithmetic.Add64`: universal checked addition for every pair whose sum fits, over arbitrary caller memory, with exact memory preservation. The checked automation follows generated instruction lookups; the same contract is tested after inserting NOPs and rejected for subtraction.
- `Choose`: universal checked selection for both Boolean inputs and every pair of 64-bit values, preserving arbitrary caller memory exactly.
- `GenericIdentity`: universal identity through direct, repeated and nested generic calls in C#, and a compiled F# identity wrapper, preserving arbitrary caller memory exactly.
- `Loops.Countdown`: universal termination and a zero result for every `uint`, including zero and `UInt32.MaxValue`, using a decreasing natural-number measure over checked local storage.
- `Calls`: a managed-call chain with an address-taken mutable local.
- `IntegerOperations.Negate32` / `Negate64`: checked-execution proofs that negation returns the modular additive inverse for every input, including the signed minimum.
- `NarrowIntegers`: signed/unsigned casts, character values, calls and an eight-byte struct containing narrow fields. `UnsignedShort.lean` proves reduction modulo 65,536 for every 32-bit input.
- `PrimitiveOperations`: reads/writes through integer references, aliasing, switch tables and aggregate `sizeof`. `PrimitiveReadWrite.lean` proves that a store followed by a load returns every 32-bit input unchanged.
- `Alias`: two arguments naming the same caller storage.
- `Struct`: universal return of the input through a **12-byte explicit-layout struct**, initialization, two field stores and a byref helper call. For every well-formed caller memory, all earlier allocation metadata, bytes and access permissions are preserved; temporary frame allocations are expired on return. `StructCopy` separately checks by-value use of the same layout.
- `LargeStruct`: a **40-byte** explicit layout with a field at offset 32.
- `PastEnd`: a permitted end sentinel whose dereference is rejected as outside the allocation, for every fuel budget.
- `Escape`: a reference to an expired local is rejected on return, for every fuel budget.
- `WrongAdd`: a mathematical counterexample to the intended addition contract.
- A separate `Examples.Hardware` assembly, built from the file-based library `Examples/Hardware/Hardware.cs`, tests runtime capability extraction.
- A Cecil-generated independent fixture tests extraction-bound static RVA bytes.
- `StaticSpans` reads a 16-byte `ReadOnlySpan<byte>` lookup table; out-of-bounds reads, writes and tampered RVA bytes are checked.
- `SpanTables` indexes `ReadOnlySpan<uint>` and `ReadOnlySpan<ulong>` tables, reads a length and the first element, and faults with `System.IndexOutOfRangeException` out of range.

Concrete example proofs establish their displayed inputs. Only explicitly universally quantified theorems claim arbitrary-input correctness. `CheckedAdd64`, `Choose` and `GenericIdentity` quantify caller memory and prove it unchanged. `Struct` quantifies well-formed caller memory and proves `MemoryBelow` preservation of the caller's storage. Other examples may require `Examples.empty` or `Examples.caller`; argument quantification alone does not imply arbitrary caller memory. The allocating generic instance wrapper retains a separate fixed-memory check in `GenericInstance.lean`.

The `Examples.Bits` methods exercise these APIs, including universal proofs of the integer logarithm and of a rotation round trip. Incorrect implementations fail the same contracts. `Log2(0)` returns zero; rounding up returns zero for zero input or overflow; signed power-of-two checks reject negative values.

## Loop verification

Reachable backward branches and switch targets are admitted when control-flow targets and stack joins validate. Feature reachability uses a fixed point: a backedge that invalidates a constant fact causes affected instructions to be revisited. Recursive managed calls remain unsupported.

Extraction does not establish termination. [The countdown proof](../Examples/Proofs/Countdown.lean) uses `CIL.Safety.loop_terminates` with an invariant describing readable, writable counter storage and the measure `remaining.toNat`. The invariant location is found from the compiled branch instruction. `cil_loop_steps` checks the path between invariant locations and infers its execution cost; each iteration proves a strictly smaller measure; the zero case proves a successful return. `ensures_of_loop` lifts this to `CIL.Safety.Ensures`, so the theorem supplies successful finite execution for every input, including the maximum 32-bit unsigned value, without unrolling billions of iterations. Subtraction cannot underflow because it occurs only when the counter is positive.

The loop suite checks the unchanged universal proof after inserting NOPs and rearranging basic blocks. It also requires that proof to reject both an incorrect result and a loop whose counter never decreases.

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Loops::Countdown(uint)" artifacts/Countdown
leancil verify artifacts/Countdown --proof Examples/Proofs/Countdown.lean
dotnet run --file scripts/Test.cs -- --suite loops
```

Loop invariants and decreasing measures are supplied by the proof author. The suite rejects an incorrect loop under the unchanged contract, checks malformed stack joins and changing loop facts, and proves that an admitted infinite loop exhausts every fuel budget. Fuel exhaustion is never successful verification of total correctness.

## F# examples

The [F# examples](../Examples/FSharp/Examples.fs) demonstrate arithmetic, branching, real method calls, `byref` mutation and mutable structs with constructors. They use the same CIL semantics, extractor and Lean proof pipeline as the C# examples.

```fsharp
let Add (x: uint64) (y: uint64) = x + y
```

Verify the compiled F# addition with the existing language-independent [addition contract](../Examples/Proofs/Add.lean):

```sh
dotnet build Examples/FSharp -c Release
leancil extract Examples/FSharp/bin/Examples.FSharp.dll "Arithmetic::Add(ulong,ulong)" artifacts/FSharpAdd
leancil verify artifacts/FSharpAdd --proof Examples/Proofs/Add.lean
```

The theorem proves `(x + y) mod 2^64` for every pair of 64-bit inputs. The suite also checks universal store/load and constructor contracts, compares compiled F# results with checked CIL execution, and rejects subtraction under the unchanged addition contract:

```sh
dotnet run --file scripts/Test.cs -- --suite fsharp
```

These examples cover F# programs that compile into the supported CIL subset. F# lists, closures, discriminated unions and arbitrary FSharp.Core calls are not generally supported; the suite includes an explicitly rejected list example.

The `GenericMethods` module also demonstrates generic identity and selection functions. LeanCIL specializes their compiled CIL for the concrete value types used by reachable calls. In a specialized body, `typeof(T) == typeof(Marker)` and `!=` become constants when both types are closed and decided, as the JIT folds them, so a profile-dependent or marker-type branch is pruned like a feature check. Lean recomputes each folded constant from the raw closed body; see [type tests](OPCODES.md#type-tests) for the exact pattern. `Examples.TypeTests` exercises a matching and a non-matching type argument. The F# and C# identity examples share the same [universal Lean contract](../Examples/Proofs/GenericIdentity.lean):

```sh
leancil extract Examples/FSharp/bin/Examples.FSharp.dll "GenericMethods::Identity64(ulong)" artifacts/FSharpIdentity
leancil verify artifacts/FSharpIdentity --proof Examples/Proofs/GenericIdentity.lean
dotnet run --file scripts/Test.cs -- --suite generics
```
