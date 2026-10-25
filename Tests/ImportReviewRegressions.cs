using System.Collections;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;

internal static class ImportReviewRegressions
{
    internal static void FullStaging_WhenDependencyChangesLaterBundle_Rejects(string extractor, string directory)
    {
        var program = RequiredType(Assembly.LoadFrom(extractor), "Program");
        var snapshot = program.GetMethod("FullStagingFiles", PrivateStatic)!;
        var require = program.GetMethod("RequireFullStaging", PrivateStatic)!;
        Directory.CreateDirectory(directory);
        var proof = Path.Combine(directory, "Proof.lean");
        var framework = Path.Combine(directory, ".lake", "packages", "leancil", "CIL.lean");
        Directory.CreateDirectory(Path.GetDirectoryName(framework)!);
        File.WriteAllText(proof, "theorem original : True := True.intro\n");
        File.WriteAllText(framework, "-- pinned framework source\n");
        var accepted = snapshot.Invoke(null, [directory]);
        void Check() => require.Invoke(null, [directory, accepted]);
        var diagnostic = "Full-verification staged bundle changed before its build: " + directory;
        Check();
        File.AppendAllText(proof, "-- dependency changed a later proof\n");
        Reject(Check, diagnostic);
        File.WriteAllText(proof, "theorem original : True := True.intro\n");
        var added = Path.Combine(directory, "Shadow.lean");
        File.WriteAllText(added, "-- unexpected staged source\n");
        Reject(Check, diagnostic);
        File.Delete(added);
        File.Delete(framework);
        Reject(Check, diagnostic);
        File.WriteAllText(framework, "-- pinned framework source\n");
        Check();
        Console.WriteLine("PASS staged proof changes, added modules and removed framework sources reject before building");
    }

    const BindingFlags PrivateInstance = BindingFlags.Instance | BindingFlags.NonPublic;
    const BindingFlags PrivateStatic = BindingFlags.Static | BindingFlags.NonPublic;
    static readonly JsonSerializerOptions RecordJson = new() { PropertyNameCaseInsensitive = true };

    internal static void ValidateStatics_WhenApplicationCollidesWithImport_RejectsBothFields(
        string extractor, JsonObject application, JsonObject imported)
    {
        Assembly assembly = Assembly.LoadFrom(extractor);
        Type resolutionType = RequiredType(assembly, "Nethermind.LeanCIL.ImportResolution");
        Type sourceType = resolutionType.GetNestedType("Source", BindingFlags.NonPublic)!;
        Type recordType = RequiredType(assembly, "Nethermind.LeanCIL.StaticIdentityRecord");
        Type bindingType = resolutionType.GetNestedType("Binding", BindingFlags.NonPublic)!;
        using IDisposable resolution = (IDisposable)Construct(resolutionType, Array.CreateInstance(sourceType, 0));
        IList bindings = (IList)resolutionType.GetField("bindings", PrivateInstance)!.GetValue(resolution)!;
        JsonObject binding = new() { ["staticIdentities"] = new JsonArray(imported.DeepClone()) };
        bindings.Add(JsonSerializer.Deserialize(binding.ToJsonString(), bindingType, RecordJson)!);
        MethodInfo validate = resolutionType.GetMethod("ValidateStatics", PrivateInstance)!;
        Array applicationRecords = Records(recordType, application);
        validate.Invoke(resolution, [applicationRecords]);
        JsonObject collision = application.DeepClone().AsObject();
        collision["identity"] = imported["identity"]!.DeepClone();
        string expected = "Static identity collision " + imported["identity"]!.GetValue<string>() + ": " +
            application["assemblyIdentity"]!.GetValue<string>() + "::" + application["fieldName"]!.GetValue<string>() +
            " and " + imported["assemblyIdentity"]!.GetValue<string>() + "::" + imported["fieldName"]!.GetValue<string>();
        Reject(() => validate.Invoke(resolution, [Records(recordType, collision)]), expected);
    }

    internal static void ValidateGraph_WhenDuplicateImplementationHashDiffers_RejectsIdentity(
        string extractor, JsonObject published)
    {
        Assembly assembly = Assembly.LoadFrom(extractor);
        Type contractType = RequiredType(assembly, "Nethermind.LeanCIL.ContractInterface");
        MethodInfo validate = RequiredType(assembly, "Nethermind.LeanCIL.ContractDependencyGraph")
            .GetMethod("Validate", PrivateStatic)!;
        validate.Invoke(null, [Records(contractType, published, published)]);
        JsonObject conflicting = published.DeepClone().AsObject();
        string oldHash = published["implementationSha256"]!.GetValue<string>();
        conflicting["implementationSha256"] = new string(oldHash[0] == '0' ? '1' : '0', 64);
        Reject(() => validate.Invoke(null, [Records(contractType, published, conflicting)]),
            "Conflicting contract dependency implementation hashes: " + published["assemblyIdentity"]!.GetValue<string>());
    }

    internal static void ImportResolution_WhenTwoVersionsShareSimpleName_RejectsAmbiguity(
        string extractor, string sidecar, string implementation, string directory)
    {
        Directory.CreateDirectory(directory);
        string secondAssembly = Path.Combine(directory, "Second.dll");
        string secondSidecar = Path.Combine(directory, "Second.leancil.contracts");
        JsonObject original = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
        JsonObject second = original.DeepClone().AsObject();
        string name;
        using (ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(implementation))))
        {
            name = module.Assembly.Name.Name;
            Version version = module.Assembly.Name.Version;
            module.Assembly.Name.Version = new Version(version.Major + 1, version.Minor, version.Build, version.Revision);
            second["assemblyIdentity"] = module.Assembly.Name.FullName;
            module.Write(secondAssembly);
            second["mvid"] = module.Mvid.ToString();
        }
        second["implementationSha256"] = Hash(secondAssembly);
        JsonObject descriptor = new();
        foreach (string field in new[] { "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity",
            "targetFramework", "interfaceModules", "exports", "dependencies" })
            descriptor[field] = second[field]!.DeepClone();
        second["interfaceDigest"] = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            System.Text.Encoding.UTF8.GetBytes(descriptor.ToJsonString())));
        foreach (JsonNode? certification in second["certifications"]!.AsArray())
        {
            certification!["implementationSha256"] = second["implementationSha256"]!.DeepClone();
            certification["interfaceDigest"] = second["interfaceDigest"]!.DeepClone();
        }
        File.WriteAllText(secondSidecar, second.ToJsonString());
        Assembly assembly = Assembly.LoadFrom(extractor);
        Type resolutionType = RequiredType(assembly, "Nethermind.LeanCIL.ImportResolution");
        Type sourceType = resolutionType.GetNestedType("Source", BindingFlags.NonPublic)!;
        object firstSource = Construct(sourceType, sidecar, implementation, Hash(implementation),
            original["interfaceDigest"]!.GetValue<string>(), false);
        object secondSource = Construct(sourceType, secondSidecar, secondAssembly, Hash(secondAssembly),
            second["interfaceDigest"]!.GetValue<string>(), false);
        Array sources = Array.CreateInstance(sourceType, 2);
        sources.SetValue(firstSource, 0);
        sources.SetValue(secondSource, 1);
        object? savedBaseDirectory = AppContext.GetData("APP_CONTEXT_BASE_DIRECTORY");
        string previousBaseDirectory = AppContext.BaseDirectory;
        string extractorDirectory = Path.GetDirectoryName(Path.GetFullPath(extractor))!;
        try
        {
            AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", extractorDirectory + Path.DirectorySeparatorChar);
            if (Path.TrimEndingDirectorySeparator(AppContext.BaseDirectory) != extractorDirectory)
                throw new InvalidOperationException("The isolated ambiguity test did not select the actual CLI's framework directory.");
            Reject(() =>
            {
                using IDisposable resolution = (IDisposable)Construct(resolutionType, sources);
            }, "Ambiguous import assembly simple name: " + name);
        }
        finally
        {
            AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", savedBaseDirectory);
            if (AppContext.BaseDirectory != previousBaseDirectory)
                throw new InvalidOperationException("The ambiguity test did not restore its application base directory.");
        }
    }

    static string Hash(string path) => Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(path)));

    static Type RequiredType(Assembly assembly, string name) => assembly.GetType(name, throwOnError: true)!;

    static object Construct(Type type, params object[] arguments) => Activator.CreateInstance(type,
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic, null, arguments, null)!;

    static Array Records(Type type, params JsonObject[] values)
    {
        Array records = Array.CreateInstance(type, values.Length);
        for (int index = 0; index < values.Length; index++)
            records.SetValue(JsonSerializer.Deserialize(values[index].ToJsonString(), type, RecordJson), index);
        return records;
    }

    static void Reject(Action action, string expected)
    {
        try { action(); }
        catch (TargetInvocationException failure) when (failure.InnerException is InvalidDataException rejected && rejected.Message == expected)
        { return; }
        throw new InvalidOperationException("Expected the exact production rejection: " + expected);
    }
}
