using Mono.Cecil;

namespace Nethermind.LeanCIL;

// A method `(Span<T> target, T value)` whose body only stores `value` into `target[0]`: its run is the write
// `WritableSpan.write_head` makes, whether it is the outlined method or a callee of an outlined loop.
internal static partial class ProofOutline
{
    /// <summary>The element width and store of a static method `(Span&lt;T&gt; target, T value)` whose body only
    /// stores `value` into `target[0]`.</summary>
    static (int Width, Operation Op)? SpanStores(Extraction extraction, int index)
    {
        var method = extraction.Methods[index];
        var ops = extraction.Emitted[index].Operations.Where(op => !op.IsNop).ToArray();
        if (method.HasThis || method.ReturnType.FullName != "System.Void" || method.Parameters.Count != 2 ||
            WrittenSpanWidth(method.Parameters[0].ParameterType) is not { } width ||
            ElementWidth(method.Parameters[1].ParameterType) != width ||
            !extraction.Emitted[index].Frame.HasNoLocals) return null;
        if (ops is not [LocalAddress { Index: 0 }, Constant { Width: 32, Value: 0, Numeral: true },
                Memory { Operation: SpanItem item }, Arg { Index: 1, Narrow: null }, var store,
                Return { Narrow: null }] || item.Width != width)
            return null;
        var stores = width == 4 ? store is StoreScalar { Width: 4 }
            : store is StackOperation { Kind: StackOpcode.Store64 } or StoreScalar { Width: 8 };
        return stores ? (width, store) : null;
    }

    /// <summary>The element width of a writable span of words, or null for any other type.</summary>
    static int? WrittenSpanWidth(TypeReference type) =>
        type is GenericInstanceType { ElementType.FullName: "System.Span`1" } span
            ? ElementWidth(span.GenericArguments[0]) : null;

    /// <summary>The step lemma of a scalar store through an address whose write succeeds.</summary>
    static string StoreLemma(Operation op) => op switch
    {
        StackOperation { Kind: StackOpcode.Store64 } => "step_store64_of_write",
        StoreScalar { Width: 8 } => "step_storeScalar_i64_of_write",
        _ => "step_storeScalar_of_write"
    };

    /// <summary>The contract proof of a callee that stores its value into the first element of its span.</summary>
    static void SpanStoreContract(Writer lean, int index, string name, string pattern, string value,
        Operation op)
    {
        lean.Line($"  rintro {pattern} memory ⟨rest, span⟩");
        lean.Line($"  dsimp only [{name}Contract] at span");
        lean.Line($"  obtain ⟨item, after, address, found, wrote, confined, filled⟩ := span.write_head {value}");
        lean.Line("  refine MethodContract.Holds.intro after ()");
        lean.Line($"    ⟨CIL.executionBound Extracted.program {name}, ?_⟩ confined filled");
        // Frame entry below is proved by hand, so the goal names the contract's arguments outright.
        lean.Line($"  dsimp only [{name}Contract]");
        SpanStoreRun(lean, "  ", index, "span", "found", "wrote", "address", op);
    }

    /// <summary>The run of method `index` storing into the first element of the nonempty `WritableSpan` named
    /// `span`, given the facts `WritableSpan.write_head` names: entering the frame that homes the span, then
    /// stepping the body.</summary>
    static void SpanStoreRun(Writer lean, string indent, int index, string span, string found, string wrote,
        string address, Operation op)
    {
        lean.Line($"{indent}have valid := {span}.valid");
        lean.Line($"{indent}have width := {span}.elementWidth");
        lean.Line($"{indent}have mode := {span}.mode");
        lean.Line($"{indent}have nonempty := {span}.length_cons.2.1");
        lean.Line($"{indent}apply CIL.Safety.invoke_of_run");
        lean.Line($"{indent}· cil_lookup []");
        lean.Line($"{indent}· cil_checked_side [valid]");
        // Entering the frame homes the span in a local, which the stepping tactics do not set up.
        lean.Line($"{indent}· simp [enterFrame, Extracted.method{index}, makeLocals, " +
            "makeParameterHomes,");
        lean.Line($"{indent}    makeLocal, storeLocal, CIL.Safety.Value.hasUnspecified, width, mode, valid, " +
            "checkedAt,");
        lean.Line($"{indent}    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]");
        lean.Line($"{indent}  exact ⟨rfl, rfl⟩");
        lean.Line($"{indent}cil_checked_steps [{found}, {StoreLemma(op)} {wrote}, valid, width, mode, nonempty, " +
            $"{address}]");
    }

    /// <summary>The outline of a method that stores its value into the first element of its span: an empty span
    /// throws, which the precondition must rule out, and a nonempty one is stepped through the write.</summary>
    static string SpanStoreLine(Specification spec, Operation op, Writer lean)
    {
        var target = spec.Parameters[0];
        var value = spec.Parameters[1].Name;
        var name = target.Name;
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.SpanWrites"],
            "`postcondition`");
        spec.Placeholders(lean);
        spec.Footprint(lean);
        spec.Statement(lean);
        lean.Line($"  have {name}Checked : WritableSpan initial (footprint {spec.Arguments}) {name} " +
            $"{target.Width} {name}.length :=");
        lean.Line($"    ⟨{name}Valid, {target.Mode}, {name}Width, rfl, {name}Authority⟩");
        lean.Line($"  generalize {name}Count : {name}.length = count at {name}Checked");
        lean.Line("  cases count with");
        lean.Line("  | zero =>");
        lean.Line($"    -- `{name}[0]` throws on an empty span, which the precondition must rule out");
        lean.Line("    exfalso");
        lean.Noted("    ", "sorry", $"Precondition excludes an empty `{name}`");
        lean.Line($"  | succ {name}Rest =>");
        lean.Line($"    obtain ⟨{name}Item, {name}After, {name}Address, {name}Found, {name}Wrote, {name}Confined,");
        lean.Line($"      {name}Filled⟩ := {name}Checked.write_head {value}");
        lean.Line($"    refine ⟨CIL.executionBound Extracted.program 0, {name}After, [], ?_, rfl, ?postcondition⟩");
        SpanStoreRun(lean, "    ", 0, name + "Checked", name + "Found", name + "Wrote", name + "Address", op);
        lean.Noted("    ", "case postcondition => sorry",
            $"Postcondition, with `{name}Filled` the stored element and `{name}Confined` the rest kept");
        Footer(lean);
        return lean.ToString();
    }
}
