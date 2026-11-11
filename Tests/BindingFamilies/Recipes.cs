using LeanCIL;

namespace BindingFixtures;

/// <summary>Reviewed contract metadata, independent of the extracted implementation.</summary>
internal sealed record Family(string Name, int Width, bool Signed, bool Equality, bool Positive,
    string Operation, string SharedTheorem);

/// <summary>Explicit equality and bitwise recipes for the synthetic fixture.</summary>
internal static class FamilyRecipes
{
    internal static Family[] Reviewed =>
    [
        new("Equal", 32, false, true, true, "", "equal32"),
        new("Different", 64, true, true, false, "", "different64"),
        new("And", 32, true, false, true, "band", "and32"),
        new("Xor", 64, false, false, true, "bxor", "xor64")
    ];

    internal static ProofGate Gate(Family family, string profile)
    {
        var type = family.Width == 32 ? family.Signed ? "int" : "uint" : family.Signed ? "long" : "ulong";
        return new($"BindingMethods::{family.Name}({type},{type})", profile,
            $"{family.Name}_{profile.Replace('-', '_')}.lean", "Generated.correctness");
    }

    internal static ProofBinding Bind(Family family, ProofGate gate)
    {
        var type = $"System.{(family.Signed ? "Int" : "UInt")}{family.Width}";
        var returnType = family.Equality ? "System.Boolean" : type;
        var signature = $"{returnType} BindingMethods::{family.Name}({type},{type})";
        var body = family.Equality
            ? $"equalityBody Extracted.profile {family.Positive.ToString().ToLowerInvariant()}"
            : $"bitwiseBody Extracted.profile .{family.Operation}";
        var value = family.Equality
            ? $".i32 (if left {(family.Positive ? "=" : "≠")} right then 1 else 0)"
            : $".i{family.Width} (left {(family.Operation == "band" ? "&&&" : "^^^")} right)";
        var fuel = family.Equality && !family.Positive ? 7 : 5;
        return new(gate, $$"""
            import Extracted
            import Support
            /-! Exact extraction binding to a reviewed integer proof family. -/
            namespace Generated
            /-- The complete managed signature retains width and signedness. -/
            theorem signature : Extracted.method0Signature =
                "{{signature}}" := rfl
            #print axioms signature
            /-- The complete extracted body retains the reviewed operation and polarity. -/
            theorem binding : Extracted.program[0]? =
                some (BindingSupport.{{body}}) := rfl
            #print axioms binding
            /-- The reviewed family theorem instantiated at this exact extraction. -/
            theorem correctness (left right : CIL.W{{family.Width}}) (memory : CIL.Safety.Memory) :
                CIL.Safety.invoke Extracted.program {{fuel}} 0
                  [.scalar (.i{{family.Width}} left), .scalar (.i{{family.Width}} right)] memory =
                  .ok (memory, [.scalar ({{value}})]) :=
              BindingSupport.{{family.SharedTheorem}} Extracted.program Extracted.profile binding left right memory
            #print axioms correctness
            end Generated
            """ + "\n");
    }
}
