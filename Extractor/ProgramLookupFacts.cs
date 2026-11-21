using System.Text;

namespace Nethermind.LeanCIL;

/// <summary>The method equations of a program and their shared axiom report.</summary>
internal static class ProgramLookupFacts
{
    internal static void Append(StringBuilder source, string program, string methodPrefix, int count)
    {
        var facts = new List<string> { $"{program}Length_eq", $"{program}Index_eq", $"{program}Index_get?" };
        for (int index = 0; index < count; index++)
        {
            var fact = $"{program}_method{index}";
            source.AppendLine($$"""
                @[cil_code] theorem {{fact}} : {{program}}[{{index}}]? = some {{methodPrefix}}{{index}} :=
                  ({{program}}Index_get? {{index}}).symm.trans (by cil_kernel_rfl)
                """);
            facts.Add(fact);
        }
        source.AppendLine($$"""
            #print axioms [
              {{string.Join(",\n  ", facts)}}]
            """);
    }
}
