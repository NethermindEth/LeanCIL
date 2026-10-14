using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class MethodSelector
{
    static readonly Dictionary<string, string> Aliases = new(StringComparer.Ordinal)
    {
        ["bool"] = "System.Boolean", ["byte"] = "System.Byte", ["sbyte"] = "System.SByte",
        ["short"] = "System.Int16", ["ushort"] = "System.UInt16", ["int"] = "System.Int32",
        ["uint"] = "System.UInt32", ["long"] = "System.Int64", ["ulong"] = "System.UInt64",
        ["nint"] = "System.IntPtr", ["nuint"] = "System.UIntPtr", ["char"] = "System.Char",
        ["float"] = "System.Single", ["double"] = "System.Double", ["decimal"] = "System.Decimal",
        ["string"] = "System.String", ["object"] = "System.Object", ["void"] = "System.Void"
    };

    static string NormalizeType(string type)
    {
        var normalized = Regex.Replace(type.Trim(), @"[A-Za-z_][A-Za-z0-9_.`/]*",
            match => Aliases.GetValueOrDefault(match.Value, match.Value));
        normalized = Regex.Replace(normalized, @"`[0-9]+(?=\s*<)", "");
        return Regex.Replace(normalized, @"\s+", "");
    }

    static string[] Parameters(string text)
    {
        if (string.IsNullOrWhiteSpace(text)) return [];

        var parts = new List<string>();
        var delimiters = new Stack<char>();
        var start = 0;

        for (var i = 0; i < text.Length; i++)
        {
            var character = text[i];
            if (character is '<' or '[') delimiters.Push(character);
            else if (character is '>' or ']')
            {
                if (!delimiters.TryPop(out var opening) ||
                    (character == '>' ? opening != '<' : opening != '['))
                    throw new ArgumentException("Malformed method selector: unbalanced parameter type");
            }
            else if (character is '(' or ')')
                throw new ArgumentException("Malformed method selector: unexpected parenthesis");
            else if (character == ',' && delimiters.Count == 0)
            {
                parts.Add(text[start..i]);
                start = i + 1;
            }
        }

        parts.Add(text[start..]);
        if (delimiters.Count != 0 || parts.Any(string.IsNullOrWhiteSpace))
            throw new ArgumentException("Malformed method selector: invalid parameter list");

        return parts.Select(NormalizeType).ToArray();
    }

    internal static MethodDefinition Resolve(ModuleDefinition module, string selector)
    {
        var syntax = Regex.Match(selector.Trim(),
            @"\A(?:(?<return>.+)\s+)?(?<type>[^\s:]+)\s*::\s*(?<method>[^\s():]+)\s*\((?<parameters>.*)\)\z");
        if (!syntax.Success)
            throw new ArgumentException("Malformed method selector. Use [return-type ]Type::Method(parameter-types)");

        var declaringType = syntax.Groups["type"].Value;
        var methodName = syntax.Groups["method"].Value;
        var returnType = syntax.Groups["return"].Success ? NormalizeType(syntax.Groups["return"].Value) : null;
        var parameters = Parameters(syntax.Groups["parameters"].Value);

        // Resolve before checking supported metadata: unsupported candidates must not
        // disappear from an ambiguous selection. Matching does not grant runtime support.
        var matches = module.GetTypes()
            .Where(type => type.FullName == declaringType || type.Name == declaringType)
            .SelectMany(type => type.Methods)
            .Where(method => method.Name == methodName &&
                (returnType is null || NormalizeType(method.ReturnType.FullName) == returnType) &&
                method.Parameters.Select(parameter => NormalizeType(parameter.ParameterType.FullName)).SequenceEqual(parameters))
            .ToArray();

        return matches.Length switch
        {
            1 => matches[0],
            0 => throw new InvalidDataException($"No method matches selector '{selector}'"),
            _ => throw new InvalidDataException($"Ambiguous method selector '{selector}'. Candidates:\n" +
                string.Join("\n", matches.Select(method => "  " + method.FullName).Order(StringComparer.Ordinal)))
        };
    }
}
