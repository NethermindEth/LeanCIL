using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

partial class Program
{
    /// <summary>Filled word-array outlines compose class arguments, field stores and indexed loops.</summary>
    void WordArrayOutlines()
    {
        var assembly = At("Examples/Assembly/bin/Examples.dll");
        var root = At("artifacts/WordArrayOutlines");
        Directory.CreateDirectory(root);
        foreach (var name in new[] { "Sum", "RefillRead" })
        {
            var extraction = Path.Combine(root, name);
            var selector = $"SampleArrays::{name}(Examples.Samples,int[]{(name == "Sum" ? "" : ",int")})";
            Run(Extract("extract", assembly, "Examples", selector, extraction));
            var outline = Path.Combine(root, name + ".lean");
            File.Delete(outline);
            Run(["dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll"), "new-proof", extraction, outline]);
            var source = File.ReadAllText(outline);
            if (source.Contains("-- not outlined:", StringComparison.Ordinal))
                throw new InvalidOperationException($"The {name} word-array composition was not outlined:\n{source}");
            source = FillWordArrayDefinition(source, "Precondition",
                name == "Sum" ? "values1.reference ≠ .null" : "True");
            source = FillWordArrayDefinition(source, "Postcondition", name == "Sum"
                ? "result = values1Elements.foldl (· + ·) 0"
                : "Samples.Values.Holds final samples values1.reference ∧ " +
                    "values1Elements[index.toNat]? = some result");
            if (name == "Sum")
            {
                source = FillWordArrayDefinition(source, "invariant",
                    "state.values.2.toNat ≤ values1Elements.length ∧\n" +
                    "    state.values.1 = (values1Elements.take state.values.2.toNat).foldl (· + ·) 0");
                source = FillWordArrayDefinition(source, "measure", "values1Elements.length - state.values.2.toNat");
                source = source.Replace("sorry -- `values1` lies apart from the memory the loop writes",
                    "by simp [footprint]", StringComparison.Ordinal);
                source = source.Replace("case invariant => sorry -- invariant at the first loop head",
                    "case invariant => simp [invariant]", StringComparison.Ordinal);
                source = source.Replace("case invariant => sorry -- invariant again at the loop head", """
                    case invariant =>
                      have next : (index + 1).toNat = index.toNat + 1 := by
                        simp [BitVec.toNat_add]
                        omega
                      dsimp only [invariant] at holds ⊢
                      refine ⟨by omega, ?_⟩
                      rw [next, List.take_add_one, List.getElem?_eq_getElem values1Bound, List.foldl_append,
                        ← holds.2]
                      simp
                    """.Replace("\n", "\n    ", StringComparison.Ordinal), StringComparison.Ordinal);
                source = source.Replace("case measure => sorry -- measure decreases over this iteration", """
                    case measure =>
                      have next : (index + 1).toNat = index.toNat + 1 := by
                        simp [BitVec.toNat_add]
                        omega
                      simp only [measure]
                      omega
                    """.Replace("\n", "\n    ", StringComparison.Ordinal), StringComparison.Ordinal);
                source = Regex.Replace(source, @"sorry -- Postcondition at the return at [^\n]+", """
                    dsimp only [invariant] at holds
                          simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt, toInt_ofNat_of_lt] at guard
                          simp only [Postcondition, holds.2]
                          rw [List.take_of_length_le (by omega)]
                          exact ⟨exitConfined, rfl⟩
                    """);
            }
            else
                source = source.Replace("sorry -- Postcondition of the returned value, with `held1` the stored fields",
                    "exact ⟨values1Reference ▸ held1, by simp [numericOfWidth, BitVec.ofNat_toNat]⟩",
                    StringComparison.Ordinal);
            if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
                throw new InvalidOperationException($"The filled {name} proof has an unfilled obligation:\n{source}");
            var proof = Path.Combine(root, name + "Filled.lean");
            File.WriteAllText(proof, source);
            VerifyWordArrayOutline(extraction, proof, expected: true);
            if (name == "RefillRead")
            {
                var mismatched = Path.Combine(root, name + "WrongElement.lean");
                File.WriteAllText(mismatched, source.Replace("WholeArray initial .signed32",
                    "WholeArray initial .unsigned32", StringComparison.Ordinal));
                VerifyWordArrayOutline(extraction, mismatched, expected: false);
            }

            // The same theorem must reject subtraction in the sum or a changed index after the field store.
            var changed = Path.Combine(root, name + "Changed.dll");
            using (var module = ModuleDefinition.ReadModule(assembly))
            {
                var method = module.GetType("Examples.SampleArrays").Methods.Single(method => method.Name == name);
                if (name == "Sum")
                    method.Body.Instructions.First(instruction => instruction.OpCode == OpCodes.Add)
                        .OpCode = OpCodes.Sub;
                else
                {
                    var load = method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldelem_I4);
                    var il = method.Body.GetILProcessor();
                    il.InsertBefore(load, Instruction.Create(OpCodes.Ldc_I4_1));
                    il.InsertBefore(load, Instruction.Create(OpCodes.Add));
                }
                module.Write(changed);
            }
            var rejected = Path.Combine(root, name + "Changed");
            Run(Extract("extract", changed, "Examples", selector, rejected));
            VerifyWordArrayOutline(rejected, proof, expected: false);
        }
        Console.WriteLine("PASS class/word-array outlines verify indexed sums and field-store/element-read " +
            "composition; changed addition and changed indexes are rejected");
    }

    static string FillWordArrayDefinition(string source, string name, string body) => Regex.Replace(source,
        $@"(def {name}\b[\s\S]*?: (?:Prop|Nat) := )sorry", "$1" + body);

    static void VerifyWordArrayOutline(string extraction, string proof, bool expected)
    {
        var result = Execute(["dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll"), "verify", extraction,
            "--proof", proof]);
        if ((result.Code == 0) != expected ||
            expected && !result.Stdout.StartsWith("Verified:", StringComparison.Ordinal) ||
            !expected && !result.Output.Contains("Stage: proof checking", StringComparison.Ordinal))
            throw new InvalidOperationException(
                $"Unexpected outline verification result for {proof}:\n{result.Output}");
    }
}

