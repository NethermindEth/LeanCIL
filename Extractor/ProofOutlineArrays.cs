using System.Globalization;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// A straight-line method returning one element of an array argument, read with `ldelem` or through a helper that
// returns the element's address: stepped on the side where the index is in bounds, where the array's contents
// give the element; an index outside throws, which the precondition must rule out.
internal static partial class ProofOutline
{
    /// <summary>The array read and the index argument of a method returning `values[index]`, and the helper
    /// returning `ref values[index]` it calls instead of `ldelem`, if any.</summary>
    sealed record ArrayAccess(Parameter Array, Parameter Index, ElementHelper? Helper);

    /// <summary>A static method `(T[] values, int index)` whose body only returns `ref values[index]`.</summary>
    sealed record ElementHelper(int Index, MethodDefinition Method, string Name);

    /// <summary>The access of a body that loads an array argument and an `int` argument, reads that element and
    /// returns it, or null for any other body.</summary>
    static ArrayAccess? ArrayRead(Extraction extraction, Specification spec, string[] all)
    {
        var ops = all.Where(op => op != ".nop").ToArray();
        if (spec.Method.HasThis || spec.Result is not { Boolean: false, Object: false } || ops.Length < 4 ||
            Argument(ops[0]) is not { Shape: ParameterShape.WordArray } array ||
            Argument(ops[1]) is not { Shape: ParameterShape.Scalar, Width: 4 } index ||
            spec.Result.Lean != WordType(array.Width) || ops[^1] != ".ret")
            return null;
        if (ops.Length == 4 && ops[2] == $".memory (.arrayLoad {array.Width} false)") return new(array, index, null);
        // A helper's address is loaded with `ldind.i4`, the only indirect load whose step the outline gives.
        if (ops.Length != 5 || array.Width != 4 || ops[3] != ".loadScalar 4" ||
            Regex.Match(ops[2], @"\A\.call (\d+) 2\z") is not { Success: true } call)
            return null;
        var callee = int.Parse(call.Groups[1].Value, CultureInfo.InvariantCulture);
        return ElementAddress(extraction, callee, array.ArrayElement) is { } method
            ? new(array, index, new(callee, method, "")) : null;

        Parameter? Argument(string op) =>
            Regex.Match(op, @"\A\.arg (\d+)\z") is { Success: true } load
                ? spec.Parameters[int.Parse(load.Groups[1].Value, CultureInfo.InvariantCulture)] : null;
    }

    /// <summary>Method `index` when it is static `(T[] values, int index)` returning `ref values[index]` of
    /// arrays of `element`, and nothing else.</summary>
    static MethodDefinition? ElementAddress(Extraction extraction, int index, string element)
    {
        var method = extraction.Methods[index];
        var ops = extraction.Emitted[index].Ops.Where(op => op != ".nop").ToArray();
        return !method.HasThis && method.Parameters.Count == 2 && method.ReturnType is ByReferenceType &&
            method.Parameters[0].ParameterType is ArrayType { Rank: 1 } array &&
            WordArrayElement(array.ElementType) == element &&
            method.Parameters[1].ParameterType.FullName is "System.Int32" &&
            extraction.Emitted[index].Metadata.Contains("locals := [],") &&
            ops.SequenceEqual([".arg 0", ".arg 1", $".memory (.arrayAddress {element})", ".ret"])
            ? method : null;
    }

    /// <summary>The outline of a method returning one element of its array: a split on whether the index is in
    /// bounds, the in-bound side stepped through the element's load and the other a precondition hole.</summary>
    static string ArrayReadLine(Specification spec, ArrayAccess access, Writer lean)
    {
        var (array, index) = (access.Array, access.Index);
        var names = new Names();
        foreach (var binder in spec.Binders) names.Claim(binder.Name, binder.Name);
        var helper = access.Helper is { } called
            ? called with { Name = names.Claim(char.ToLowerInvariant(called.Method.Name[0]) + called.Method.Name[1..],
                "callee" + called.Index.ToString(CultureInfo.InvariantCulture)) }
            : null;
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.ArrayContents"],
            "`postcondition`");
        if (helper is not null) ElementContract(lean, helper, array);
        spec.Placeholders(lean);
        spec.Statement(lean);
        var (bound, item, element, loaded) = (array.Name + "Bound", array.Name + "Item", array.Name + "Found",
            array.Name + "Loaded");
        lean.Line($"  by_cases {bound} : {index.Name}.toNat < {array.ElementsName}.length");
        lean.Line($"  · obtain ⟨{item}, {element}, {loaded}⟩ :=");
        lean.Line($"      {array.Name}Contents.array_load {array.Name}Valid (by decide) {bound}");
        if (helper is null)
        {
            lean.Line("    refine ⟨CIL.executionBound Extracted.program 0, ?final, ?results, ?run, ?postcondition⟩");
            lean.Line("    case run =>");
            lean.Line($"      cil_checked_steps [step_arrayLoad_of_element (index := .i32 {index.Name}) rfl {element}");
            lean.Line($"        {loaded}, {array.Name}Valid]");
        }
        else
        {
            lean.Line($"    cil_contract_steps [{array.Name}Valid, {helper.Name}_holds, {helper.Name}Contract, " +
                "leaveFrame]");
            lean.Line("      with called1 output1 call1");
            lean.Line($"    case precondition => exact ⟨{array.Name}Valid, {array.Name}Type, {array.ElementsName}, " +
                $"{array.Name}Contents, {bound}⟩");
            lean.Line("    have post1 := call1.post");
            lean.Line($"    dsimp only [{helper.Name}Contract] at post1 ⊢");
            // The helper returns the address of the element the caller's contents name.
            lean.Line("    obtain ⟨rfl, found1⟩ := post1");
            lean.Line($"    cases {element}.symm.trans found1");
            lean.Line($"    cil_contract_steps [{loaded}]");
        }
        spec.Postcondition(lean, "    ", $"Postcondition of `{array.ElementsName}[{index.Name}.toNat]`");
        lean.Line($"  · -- `{array.Name}[{index.Name}]` throws outside the array, which the precondition must " +
            "rule out");
        lean.Line("    exfalso");
        lean.Noted("    ", "sorry", $"Precondition excludes an index outside `{array.Name}`");
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>The contract of a helper returning `ref values[index]`, and its proof: it needs element `index`
    /// of the array's contents, writes nothing and returns that element's address.</summary>
    static void ElementContract(Writer lean, ElementHelper helper, Parameter array)
    {
        var (name, width, word) = (helper.Name, array.Width, WordType(array.Width));
        var method = helper.Index.ToString(CultureInfo.InvariantCulture);
        lean.Doc($"`{helper.Method.Name}` as the outline reads its body: it needs element `index` of the " +
            "array's contents, writes nothing and returns that element's address.");
        lean.Line($"def {name}Contract : MethodContract (ArrayView × W32) Reference where");
        lean.Line("  args := fun (values, index) => [.array values, .scalar (.i32 index)]");
        lean.Line("  results result := [.reference (.address result)]");
        lean.Line("  pre := fun (values, index) memory =>");
        lean.Line($"    values.validate memory = .ok () ∧ values.elementType = {array.ArrayElement} ∧");
        lean.Line($"      ∃ elements : List {word}, SpanContents memory values.storage {width} elements ∧");
        lean.Line("        index.toNat < elements.length");
        lean.Line("  footprint := fun _ => []");
        lean.Line("  post := fun (values, index) initial final result =>");
        lean.Line($"    final = initial ∧ arrayElement initial values index.toNat {width} = .ok result");
        lean.Line();
        lean.Doc($"`{helper.Method.Name}` meets its contract; callers use only the contract.");
        lean.Line($"theorem {name}_holds : {name}Contract.Holds Extracted.program {method} := by");
        lean.Line("  rintro ⟨values, index⟩ initial ⟨valid, typed, elements, contents, bound⟩");
        lean.Line("  obtain ⟨item, found, _⟩ := contents.array_load valid (by decide) bound");
        lean.Line("  refine MethodContract.Holds.intro initial item ?_ (Confined.refl _ _) ⟨rfl, found⟩");
        lean.Line("  cil_checked_steps [step_arrayAddress_of_element (index := .i32 index) typed rfl found, " +
            "valid,");
        lean.Line("    arrayElement_formed found, leaveFrame]");
        lean.Line();
        lean.Line($"#print axioms {name}_holds");
        lean.Line();
    }
}
