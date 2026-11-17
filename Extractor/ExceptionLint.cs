using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml;
using System.Xml.Linq;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class ExceptionLint
{
    const string Usage = "Usage: leancil lint-exceptions output-directory --documentation assembly.xml";
    const string Notice = "Diagnostic only. Sites are potential model paths, not proved exceptions. XML comments are untrusted documentation, not evidence.";
    sealed record Site(string Method, int IlOffset, ExceptionType Exception, string Origin);
    sealed record Declaration(string Exception, string Text);

    internal static int Run(string[] args)
    {
        if (args is not [string directory, "--documentation", string documentation])
            throw new ArgumentException(Usage);
        string output = Path.GetFullPath(directory);
        string reportPath = Path.Combine(output, "exception-lint.json");
        documentation = Path.GetFullPath(documentation);
        if (string.Equals(documentation, reportPath, OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal))
            throw new ArgumentException("Documentation cannot be the lint report.");
        File.Delete(reportPath);
        if (Program.CheckExtraction(output) != 0)
            throw new InvalidDataException("Exception lint requires a current admitted extraction.");
        string identitySource = File.ReadAllText(Path.Combine(output, "identity.json"));
        JsonElement identity = JsonSerializer.Deserialize<JsonElement>(identitySource);
        string assemblyPath = Path.GetFullPath(identity.GetProperty("assemblyPath").GetString()!, output);
        byte[] assembly = File.ReadAllBytes(assemblyPath);
        using FileStream documentationStream = File.OpenRead(documentation);
        if (documentationStream.Length > 8 * 1024 * 1024) throw new InvalidDataException("Exception documentation exceeds the 8 MiB limit.");
        byte[] xml = new byte[checked((int)documentationStream.Length)];
        documentationStream.ReadExactly(xml);
        if (documentationStream.ReadByte() != -1) throw new InvalidDataException("Exception documentation changed while reading.");
        using PinnedAssemblies pinned = new(assembly, Hash(assembly), []);
        ModuleDefinition module = pinned.Selected;
        FeatureProfile profile = identity.GetProperty("profile").Deserialize<FeatureProfile>()
            ?? throw new InvalidDataException("Missing extraction profile.");
        SortedSet<string> initialized = new(identity.GetProperty("initializedTypes").Deserialize<string[]>() ?? [], StringComparer.Ordinal);
        MethodDefinition[] methods = MetadataValidation.Validate(module, identity.GetProperty("assemblyIdentity").GetString()!,
            identity.GetProperty("entry").GetString()!, profile, initialized);
        string generated = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
        string regeneratedHash = Hash(Encoding.UTF8.GetBytes(generated));
        if (Hash(assembly) != identity.GetProperty("assemblySha256").GetString() ||
            regeneratedHash != identity.GetProperty("generatedSha256").GetString())
            throw new InvalidDataException("Extraction changed during exception lint.");
        string member = DocumentationId(MethodSpecialization.Definition(methods[0]));
        Declaration[] declarations = ReadDocumentation(xml, module.Assembly.Name.Name, member);
        var methodIndices = methods.Select((method, index) => (method, index))
            .ToDictionary(pair => pair.method, pair => pair.index);
        List<Site> sites = [];
        for (int methodIndex = 0; methodIndex < methods.Length; methodIndex++)
        {
            MethodDefinition method = methods[methodIndex];
            var instructions = new InstructionIndex(method);
            var reachable = Reachability.Analyze(method, profile);
            var nativeOperands = NativeOperands.Certify(method, reachable, profile);
            var parameterHomes = ParameterStorage.IndexHomes(ParameterStorage.Analyze(method, reachable));
            Throws.Analysis folded = Throws.Analyze(method);
            foreach (Instruction instruction in reachable.OrderBy(value => value.Offset))
            {
                if (folded.Raises.TryGetValue(instruction, out ExceptionType exception))
                    sites.Add(new(method.FullName, instruction.Offset, exception, "folded throw"));
                Operation operation = InstructionTranslation.Translate(instruction, method, methodIndices,
                    methodIndex, instructions, profile, nativeOperands, parameterHomes);
                // A modelled call raises what the operation its model runs as raises.
                if (operation is ModelCall call) operation = call.Model;
                foreach (ExceptionType named in RuntimeExceptions(operation))
                    sites.Add(new(method.FullName, instruction.Offset, named,
                        "interpreter operation: " + operation.ToLean()));
            }
        }
        ExceptionType[] modeled = sites.Select(site => site.Exception).Distinct()
            .OrderBy(exception => exception.FullName(), StringComparer.Ordinal).ToArray();
        HashSet<ExceptionType> modeledSet = [.. modeled];
        string[] documented = declarations.Select(value => value.Exception).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        HashSet<ExceptionType> documentedMembers = [.. documented.Select(DocumentedMember).OfType<ExceptionType>()];
        string[] undocumented = modeled.Where(exception => !documentedMembers.Contains(exception))
            .Select(exception => exception.FullName()).ToArray();
        string[] absent = documented.Where(name => DocumentedMember(name) is not ExceptionType member ||
            !modeledSet.Contains(member)).ToArray();
        string report = JsonSerializer.Serialize(new
        {
            schema = 1, note = Notice,
            coverage = "Profile-reachable admitted methods; folded throws and named arithmetic/span faults. No path feasibility, preconditions, runtime-completeness or proof analysis. Invalid state, invalid operands/bounds, memory faults, unsupported operations and fuel exhaustion have no CLR mapping here.",
            documentationBinding = "XML assembly name and compiler member ID matched. The XML hash records supplied bytes; it does not establish that the XML came from this DLL build.",
            assemblyIdentity = module.Assembly.Name.FullName, assemblySha256 = Hash(assembly),
            documentationSha256 = Hash(xml), generatedSha256 = regeneratedHash,
            entry = methods[0].FullName, documentationMember = member, profile = profile.Name,
            potentialModeled = modeled.Select(exception => exception.FullName()),
            documented = declarations,
            sites = sites.Select(site =>
                new { site.Method, site.IlOffset, Exception = site.Exception.FullName(), site.Origin }),
            findings = undocumented.Select(exception => new { exception, message = "potential modelled exception not documented" })
                .Concat(absent.Select(exception => new { exception, message = "documented exception not found in the model" }))
        }, new JsonSerializerOptions { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase });
        if (File.ReadAllText(Path.Combine(output, "identity.json")) != identitySource ||
            Hash(File.ReadAllBytes(assemblyPath)) != Hash(assembly) ||
            File.ReadAllText(Path.Combine(output, "Extracted.lean")) != generated)
            throw new InvalidDataException("Extraction inputs changed during exception lint.");
        File.WriteAllText(reportPath, report + "\n", new UTF8Encoding(false));
        Console.WriteLine(Notice);
        foreach (string exception in undocumented) Console.WriteLine("potential modelled exception not documented: " + exception);
        foreach (string exception in absent) Console.WriteLine("documented exception not found in the model: " + exception);
        Console.WriteLine("Exception lint report: " + CliPaths.Display(reportPath));
        return 0;
    }

    static IEnumerable<ExceptionType> RuntimeExceptions(Operation operation)
    {
        if (operation is Divide divide)
        {
            yield return ExceptionType.DivideByZero;
            if (divide.Signed) yield return ExceptionType.Overflow;
        }
        else if (operation is CheckedArithmetic or CheckedConvert or ScalarIntrinsic { Function: ScalarFunction.Abs })
            yield return ExceptionType.Overflow;
        else if (operation is X86BaseDivRem64)
        {
            yield return ExceptionType.DivideByZero;
            yield return ExceptionType.Overflow;
        }
        else if (operation is Memory { Operation: SpanItem })
            yield return ExceptionType.IndexOutOfRange;
    }

    // The documentation boundary: a documented type name is the member of that full name, or none.
    static ExceptionType? DocumentedMember(string name)
    {
        foreach (ExceptionType exception in ExceptionTypeText.All)
            if (exception.FullName() == name) return exception;
        return null;
    }

    static Declaration[] ReadDocumentation(byte[] xml, string assembly, string member)
    {
        XmlReaderSettings settings = new() { DtdProcessing = DtdProcessing.Prohibit, XmlResolver = null, MaxCharactersInDocument = 8 * 1024 * 1024 };
        using XmlReader reader = XmlReader.Create(new MemoryStream(xml), settings);
        XDocument document = XDocument.Load(reader);
        if (document.Root?.Name != "doc" || document.Root.Element("assembly")?.Element("name")?.Value.Trim() != assembly)
            throw new InvalidDataException("Documentation assembly name does not match the extraction.");
        XElement[] matches = document.Root.Element("members")?.Elements("member").Where(element => (string?)element.Attribute("name") == member).ToArray() ?? [];
        if (matches.Length != 1) throw new InvalidDataException("Documentation must contain exactly one member: " + member);
        if (matches[0].Descendants().Any(element => element.Name.LocalName is "inheritdoc" or "include"))
            throw new InvalidDataException("Exception lint requires expanded documentation; include and inheritdoc are unsupported.");
        List<Declaration> result = [];
        foreach (XElement declaration in matches[0].Elements("exception"))
        {
            string? cref = (string?)declaration.Attribute("cref");
            if (cref is null || !Regex.IsMatch(cref, @"\AT:[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z"))
                throw new InvalidDataException("Exception documentation requires a resolved type cref, not prose or an unresolved reference.");
            result.Add(new(cref[2..], declaration.Value.Trim()));
        }
        return result.ToArray();
    }

    static string DocumentationId(MethodDefinition method)
    {
        string name = method.Name.Replace('.', '#');
        if (method.HasGenericParameters) name += "``" + method.GenericParameters.Count;
        string parameters = method.Parameters.Count == 0 ? "" : "(" + string.Join(",", method.Parameters.Select(parameter => DocumentationType(parameter.ParameterType))) + ")";
        string conversion = method.Name is "op_Implicit" or "op_Explicit" ? "~" + DocumentationType(method.ReturnType) : "";
        return "M:" + method.DeclaringType.FullName.Replace('/', '.') + "." + name + parameters + conversion;
    }

    static string DocumentationType(TypeReference type) => type switch
    {
        ByReferenceType reference => DocumentationType(reference.ElementType) + "@",
        PointerType pointer => DocumentationType(pointer.ElementType) + "*",
        ArrayType array => DocumentationType(array.ElementType) + (array.IsVector ? "[]" : "[" + string.Join(",", Enumerable.Repeat("0:", array.Rank)) + "]"),
        GenericParameter parameter => (parameter.Type == GenericParameterType.Method ? "``" : "`") + parameter.Position,
        GenericInstanceType generic => Regex.Replace(generic.ElementType.FullName.Replace('/', '.'), @"`[0-9]+", "") +
            "{" + string.Join(",", generic.GenericArguments.Select(DocumentationType)) + "}",
        RequiredModifierType modifier => DocumentationType(modifier.ElementType),
        OptionalModifierType modifier => DocumentationType(modifier.ElementType),
        TypeSpecification => throw new InvalidDataException("Unsupported XML documentation parameter type: " + type.FullName),
        _ => type.FullName.Replace('/', '.')
    };

    static string Hash(byte[] bytes) => Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
}
