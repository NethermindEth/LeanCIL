using System.Text.RegularExpressions;

partial class Program
{
    static void VerifyWordReaderOutline(string extraction, string proof, bool expected)
    {
        File.Delete(Path.Combine(extraction, "verified.json"));
        var result = Execute(["dotnet", ExtractorPath, "verify", extraction, "--proof", proof]);
        if ((result.Code == 0) != expected ||
            expected && !result.Stdout.StartsWith("Verified:", StringComparison.Ordinal) ||
            !expected && !result.Output.Contains("Stage: proof checking", StringComparison.Ordinal) ||
            !expected && File.Exists(Path.Combine(extraction, "verified.json")))
            throw new InvalidOperationException($"Unexpected cursor verification result:\n{result.Output}");
    }

    static string FillWordReaderSpecification(string source, bool skip)
    {
        source = Regex.Replace(source, @"(def Precondition[\s\S]*?: Prop :=) sorry", """
            $1
              0 < (WordReader.Remaining.of initial wordReader).toNat ∧
              (WordReader.Position.of initial wordReader).toNat +
                (WordReader.Remaining.of initial wordReader).toNat = values1Elements.length ∧
              values1Elements.length < 2 ^ 32
            """);
        if (skip) source = source.Replace("0 < (WordReader.Remaining", "1 < (WordReader.Remaining",
            StringComparison.Ordinal);
        source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry", """
            $1
              values1Elements[(WordReader.Position.of initial wordReader).toNat]? = some result ∧
              (WordReader.Position.of final wordReader).toNat =
                (WordReader.Position.of initial wordReader).toNat + 1 ∧
              (WordReader.Remaining.of final wordReader).toNat + 1 =
                (WordReader.Remaining.of initial wordReader).toNat ∧
              (WordReader.Position.of final wordReader).toNat +
                (WordReader.Remaining.of final wordReader).toNat = values1Elements.length
            """);
        if (skip) source = source.Replace("values1Elements[(WordReader.Position.of initial wordReader).toNat]?",
            "values1Elements[(WordReader.Position.of initial wordReader).toNat + 1]?", StringComparison.Ordinal);
        return source;
    }

    static string FillWordReaderOutline(string source, bool skip)
    {
        source = FillWordReaderSpecification(source, skip);
        source = source.Replace("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            """
            have positionHeld : WordReader.Position.Holds stored2 wordReader
                (WordReader.Position.of initial wordReader + 1) :=
                  held1.after_confined framed2 (apart_of_entries rfl)
              have remainingBefore := (wordReaderRemaining.frame framed1 (apart_of_entries rfl)).2
              dsimp only [Precondition] at assumed
              have next : (WordReader.Position.of initial wordReader + 1).toNat =
                  (WordReader.Position.of initial wordReader).toNat + 1 := by
                simp [BitVec.toNat_add]
                omega
              have consumed : (WordReader.Remaining.of initial wordReader - 1).toNat + 1 =
                  (WordReader.Remaining.of initial wordReader).toNat := by
                simp [BitVec.toNat_sub]
                omega
              dsimp only [Postcondition, leaveFrame, List.foldl_nil]
              refine ⟨?_, ?_⟩
              · have index : (4294967295 + ((WordReader.Position.of initial wordReader).toNat + 1)) %
                    4294967296 = (WordReader.Position.of initial wordReader).toNat := by omega
                simp (disch := omega) [numericOfWidth, BitVec.ofNat_toNat, positionHeld.2, next, index,
                  List.getElem?_eq_getElem, Nat.mod_eq_of_lt]
              · rw [positionHeld.2, held2.2, remainingBefore]
                exact ⟨next, consumed, by omega⟩
            """, StringComparison.Ordinal);
        source = source.Replace("sorry -- the index in the current memory is within the supplied array", """
            have positionHeld : WordReader.Position.Holds stored2 wordReader
                  (WordReader.Position.of initial wordReader + 1) :=
                    held1.after_confined framed2 (apart_of_entries rfl)
                rw [positionHeld.2]
                dsimp only [Precondition] at assumed
                simp [BitVec.toNat_add, BitVec.toNat_sub]
                omega
            """, StringComparison.Ordinal);
        return source;
    }
}
