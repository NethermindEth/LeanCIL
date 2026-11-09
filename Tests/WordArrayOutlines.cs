using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

partial class Program
{
    /// <summary>Filled word-array outlines compose class arguments, slot stores, allocation and indexed loops.</summary>
    void WordArrayOutlines()
    {
        var assembly = At("Examples/Assembly/bin/Examples.dll");
        var root = At("artifacts/WordArrayOutlines");
        Directory.CreateDirectory(root);
        foreach (var name in new[]
            { "Sum", "RefillRead", "CountAfterDeposit", "CountAfterAllocation", "ReadAfterAllocation",
                "ReadAfterEcho" })
        {
            var extraction = Path.Combine(root, name);
            var owner = name is "CountAfterDeposit" or "ReadAfterEcho" ? "Account"
                : name.EndsWith("AfterAllocation", StringComparison.Ordinal) ? "Node" : "Samples";
            var indexed = name is "RefillRead" or "ReadAfterEcho";
            var selector = $"SampleArrays::{name}(Examples.{owner},int[]{(indexed ? ",int" : "")})";
            Run(Extract("extract", assembly, "Examples", selector, extraction));
            var outline = Path.Combine(root, name + ".lean");
            File.Delete(outline);
            Run(["dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll"), "new-proof", extraction, outline]);
            var source = File.ReadAllText(outline);
            if (source.Contains("-- not outlined:", StringComparison.Ordinal))
                throw new InvalidOperationException($"The {name} word-array composition was not outlined:\n{source}");
            if (name is "RefillRead" or "ReadAfterAllocation" &&
                source.Contains("SpanApart", StringComparison.Ordinal))
                throw new InvalidOperationException($"The {name} outline requires unnecessary byte separation");
            // The loop's outline states the null exclusion itself and leaves the rest of the precondition.
            const string nonNull = "  values1.reference ≠ .null ∧ ";
            if (name == "Sum" && !source.Contains(nonNull + "sorry", StringComparison.Ordinal))
                throw new InvalidOperationException($"The Sum outline does not exclude a null array:\n{source}");
            source = name == "Sum" ? source.Replace(nonNull + "sorry", nonNull + "True", StringComparison.Ordinal)
                : FillWordArrayDefinition(source, "Precondition", "True");
            source = FillWordArrayDefinition(source, "Postcondition", name == "Sum"
                ? "result = values1Elements.foldl (· + ·) 0"
                : name == "RefillRead" ? "Samples.Values.Holds final samples values1.reference ∧ " +
                    "values1Elements[index.toNat]? = some result"
                : name == "ReadAfterAllocation" ? "values1Elements[0]? = some result"
                : name == "ReadAfterEcho" ? "values1Elements[index.toNat]? = some result ∧ " +
                    "Account.Limit.Holds final account index"
                : "result = BitVec.ofNat 32 values1.length");
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
            else if (name == "RefillRead")
                source = source.Replace("sorry -- Postcondition of the returned value, with `held1` the stored fields",
                    "exact ⟨values1Reference ▸ held1, by simp [numericOfWidth, BitVec.ofNat_toNat]⟩",
                    StringComparison.Ordinal);
            else if (name == "ReadAfterEcho")
                source = source.Replace("sorry -- Postcondition of the returned value, with `held1` the stored fields",
                    "exact ⟨by simp [numericOfWidth, BitVec.ofNat_toNat], held1⟩", StringComparison.Ordinal);
            else
                source = Regex.Replace(source, @"sorry -- Postcondition of the returned value[^\n]*",
                    name == "ReadAfterAllocation"
                        ? "simp [Postcondition, numericOfWidth, BitVec.ofNat_toNat]" : "simp [Postcondition]");
            if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
                throw new InvalidOperationException($"The filled {name} proof has an unfilled obligation:\n{source}");
            var proof = Path.Combine(root, name + "Filled.lean");
            File.WriteAllText(proof, source);
            VerifyWordArrayOutline(extraction, proof, expected: true);
            if (name.StartsWith("Count", StringComparison.Ordinal)) continue;
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
                var target = name == "ReadAfterEcho" ? "RecordIndex" : name;
                var method = module.GetType("Examples.SampleArrays").Methods.Single(method => method.Name == target);
                if (name == "Sum")
                    method.Body.Instructions.First(instruction => instruction.OpCode == OpCodes.Add)
                        .OpCode = OpCodes.Sub;
                else
                {
                    var load = method.Body.Instructions.Single(instruction => instruction.OpCode ==
                        (name == "ReadAfterEcho" ? OpCodes.Ret : OpCodes.Ldelem_I4));
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
        Console.WriteLine("PASS class/word-array outlines verify indexed sums, slot-store reads and allocation " +
            "followed by element reads; changed addition and changed indexes are rejected");
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
