namespace Nethermind.LeanCIL;

/// <summary>The admission proof for live object instructions with named operand shape facts.</summary>
internal static class ObjectOperandProof
{
    internal static string Render(string method, IEnumerable<(int Opcode, string Type)> operands)
    {
        var sites = string.Join(", ", operands.Select(site =>
            $"⟨{site.Opcode}, {site.Type}, _, {site.Type}_shape (body := {method}) rfl⟩"));
        return $"Extraction.ObjectOperandsValid.of_sites [{sites}] rfl (by decide +kernel) (by decide +kernel)";
    }
}
