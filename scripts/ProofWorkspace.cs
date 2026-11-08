using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
    /// <summary>A request to refresh the editor extraction of the Lake package `ProofRoot` holding `Proof`.</summary>
    sealed record WorkspaceSettings(string Assembly, string Method, string Profile, string Proof, string ProofRoot,
        string? AssemblyIdentity, string[] InitializedTypes, bool CreatedPackage);

    /// <summary>The method an editor library currently holds, so replacing it with another one is reported.</summary>
    sealed record EditorSelection(string Assembly, string Method, string Profile, string? AssemblyIdentity,
        string[] InitializedTypes);

    /// <summary>Where the framework's editor library reads its sources, relative to the framework package.</summary>
    const string EditorSourceDirectory = ".lake/leancil";
    const string EditorSelectionFile = "selection.json";
    const string WorkspaceUsage = "Usage: leancil workspace assembly.dll method --profile profile --proof proof.lean " +
        "[--proof-root package-directory] [--assembly identity] [--assume-initialized type]...";

    internal static void CreateProofWorkspace(string[] args) => RefreshEditorExtraction(ParseWorkspaceSettings(args));

    static WorkspaceSettings ParseWorkspaceSettings(string[] args)
    {
        if (args.Length < 2 || args[0].StartsWith("--", StringComparison.Ordinal) ||
            args[1].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(WorkspaceUsage);
        var options = new Dictionary<string, string>(StringComparer.Ordinal);
        var initialized = new SortedSet<string>(StringComparer.Ordinal);
        for (int index = 2; index < args.Length; index++)
        {
            var option = args[index];
            if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) ||
                args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option + ".");
            if (option == "--assume-initialized")
            {
                if (!initialized.Add(args[index]))
                    throw new ArgumentException("Duplicate initialization assumption: " + args[index]);
            }
            else if (option is not ("--profile" or "--proof" or "--proof-root" or "--assembly") ||
                !options.TryAdd(option, args[index]))
                throw new ArgumentException("Unknown or duplicate option: " + option);
        }
        if (!options.TryGetValue("--profile", out var profile) || !options.TryGetValue("--proof", out var proof))
            throw new ArgumentException(WorkspaceUsage);
        if (profile.StartsWith('@')) profile = "@" + Path.GetFullPath(profile[1..]);
        proof = Path.GetFullPath(proof);
        if (!File.Exists(proof)) throw new FileNotFoundException("Proof file not found: " + proof);
        var root = options.TryGetValue("--proof-root", out var selectedRoot)
            ? Path.GetFullPath(selectedRoot) : FindProofPackage(proof);
        var created = root is null;
        // A proof outside any Lake package becomes the root of a generated one, so it is edited in place.
        root ??= ScratchProofPackage(Path.GetDirectoryName(proof)!);
        if (IsScratchPackage(root)) ScratchProofPackage(root);
        Within(root, Path.GetRelativePath(root, proof));
        return new(Path.GetFullPath(args[0]), args[1], profile, proof, root, options.GetValueOrDefault("--assembly"),
            [.. initialized], created);
    }

    static string? FindProofPackage(string proof)
    {
        DirectoryInfo? directory = new(Path.GetDirectoryName(proof)!);
        while (directory is not null)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")) ||
                File.Exists(Path.Combine(directory.FullName, "lakefile.lean")))
                return directory.FullName;
            directory = directory.Parent;
        }
        return null;
    }

    const string ScratchPackageName = "leancil_scratch";

    static bool IsScratchPackage(string root) =>
        File.Exists(Path.Combine(root, "lakefile.toml")) && File.ReadAllText(Path.Combine(root, "lakefile.toml"))
            .StartsWith($"name = \"{ScratchPackageName}\"\n", StringComparison.Ordinal);

    /// <summary>
    /// Makes `package` a Lake package that requires, by path, a copy of the bundled framework below its `.lake`,
    /// refreshing the copy when the tool's framework changes. Nothing is fetched or committed, so the user's git
    /// configuration plays no part.
    /// </summary>
    static string ScratchProofPackage(string package)
    {
        var sources = LibrarySources(CommonInputs());
        // The key regenerates the framework copy when the tool's framework changes.
        var lakefile = $$"""
            name = "{{ScratchPackageName}}"
            # Bundled LeanCIL framework {{ContentKey(JsonSerializer.Serialize(sources))[..20]}}

            [[require]]
            name = "leancil"
            path = "{{BundledFrameworkDirectory}}"

            """;
        var lakefilePath = Path.Combine(package, "lakefile.toml");
        var toolchainPath = Path.Combine(package, "lean-toolchain");
        if (File.Exists(lakefilePath) && File.ReadAllText(lakefilePath) == lakefile &&
            File.Exists(Path.Combine(package, "lake-manifest.json")))
            return package;
        var toolchain = File.ReadAllText(At("lean-toolchain")).Trim();
        if (File.Exists(toolchainPath) && File.ReadAllText(toolchainPath).Trim() != toolchain)
            throw new InvalidDataException("A different lean-toolchain already pins " + package +
                "; pass --proof-root for a Lake package on the tool's toolchain.");
        var framework = Within(package, BundledFrameworkDirectory);
        var staging = framework + ".staging-" + Guid.NewGuid().ToString("N");
        try
        {
            foreach (var name in sources.Keys)
            {
                var destination = Path.Combine(staging, name);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(At(name), destination);
            }
            if (Directory.Exists(framework)) Directory.Delete(framework, true);
            Directory.Move(staging, framework);
        }
        finally
        {
            if (Directory.Exists(staging)) Directory.Delete(staging, true);
        }
        File.Copy(At("lean-toolchain"), toolchainPath, true);
        File.WriteAllText(lakefilePath, lakefile);
        Run(["lake", "update"], package);
        return package;
    }

    /// <summary>
    /// Writes the selected method's extraction as the framework's editor library in the proof's package and builds
    /// it there, so `import Extracted` resolves in the proof itself. Nothing here is or yields a certificate.
    /// </summary>
    static void RefreshEditorExtraction(WorkspaceSettings settings)
    {
        var root = settings.ProofRoot;
        var editor = Path.Combine(EditorFramework(root), EditorSourceDirectory);
        var extraction = Path.Combine(Path.GetTempPath(), "leancil-editor-" + Guid.NewGuid().ToString("N"));
        string[] modules;
        try
        {
            Run([.. Extract("extract", settings.Assembly, settings.AssemblyIdentity, settings.Method, extraction,
                    settings.Profile),
                .. settings.InitializedTypes.SelectMany(type => new[] { "--assume-initialized", type })]);
            // The command takes no --import, so an extraction never needs contract interface modules here.
            if (ExtractionIdentity.Read(extraction).Sources.Count > 0)
                throw new InvalidDataException("Editor extraction unexpectedly carries contract interface modules.");
            Directory.CreateDirectory(editor);
            var symbols = Path.Combine(extraction, "Symbols.lean");
            CopyIfChanged(Path.Combine(extraction, "Extracted.lean"), Path.Combine(editor, "Extracted.lean"));
            // Without a PDB the import fails at its source instead of loading names of an older build.
            if (File.Exists(symbols)) CopyIfChanged(symbols, Path.Combine(editor, "ExtractedSymbols.lean"));
            else File.Delete(Path.Combine(editor, "ExtractedSymbols.lean"));
            modules = File.Exists(symbols) ? ["Extracted", "ExtractedSymbols"] : ["Extracted"];
        }
        finally
        {
            if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
        }
        var selection = new EditorSelection(settings.Assembly, settings.Method, settings.Profile,
            settings.AssemblyIdentity, settings.InitializedTypes);
        var selectionPath = Path.Combine(editor, EditorSelectionFile);
        var previous = File.Exists(selectionPath)
            ? JsonSerializer.Deserialize<EditorSelection>(File.ReadAllText(selectionPath)) : null;
        var recorded = JsonSerializer.Serialize(selection, Json) + "\n";
        if (!File.Exists(selectionPath) || File.ReadAllText(selectionPath) != recorded)
            File.WriteAllText(selectionPath, recorded);
        Run(["lake", "build", .. modules.Select(module => "+" + module)], root,
            progress: "Building " + string.Join(" and ", modules) + " (the first build also builds the framework)");
        PrintEditorExtraction(settings, editor, modules, previous);
    }

    /// <summary>
    /// The framework package whose editor library serves `root`: the root itself in a LeanCIL checkout, otherwise its
    /// leancil dependency, after the same framework, toolchain and reserved-module checks as consumer verification.
    /// </summary>
    static string EditorFramework(string root)
    {
        var manifest = JsonSerializer.Deserialize<JsonElement>(
            File.ReadAllText(Path.Combine(root, "lake-manifest.json")));
        string framework;
        string[] packages = [root];
        if (manifest.GetProperty("name").GetString() == "leancil")
        {
            RequireBundledFramework(root, root);
            framework = root;
        }
        else
        {
            var dependencies = ConsumerDependencies(root, IsScratchPackage(root));
            ConsumerSnapshot(root, null, dependencies);
            framework = dependencies.Single(dependency => dependency.Name == "leancil").Source;
            packages = [root, .. dependencies.Select(dependency => dependency.Directory)];
        }
        var sources = packages.SelectMany(package => ConsumerSources(package)).Where(path =>
            Path.GetFileName(path) is "Extracted.lean" or "ExtractedSymbols.lean").ToArray();
        if (sources.Length > 0)
            throw new InvalidDataException("Extracted and ExtractedSymbols are reserved for the selected " +
                "extraction; remove " + CliPaths.Display(sources[0]) + ".");
        var lakefile = Path.Combine(framework, "lakefile.toml");
        if (!File.Exists(lakefile) || !File.ReadAllText(lakefile).ReplaceLineEndings("\n").Contains(
                $"[[lean_lib]]\nname = \"{EditorLibraryName}\"\nsrcDir = \"{EditorSourceDirectory}\"\n",
                StringComparison.Ordinal))
            throw new InvalidDataException("The leancil framework at " + CliPaths.Display(framework) +
                " declares no " + EditorLibraryName + " library, so an editor cannot resolve Extracted." +
                (SourceRevision is { } revision
                    ? $"\n  Pin leancil to rev \"{revision}\" (see leancil --version)." : ""));
        return framework;
    }

    // Unchanged bytes keep Lake's traces, so an unchanged method rebuilds nothing.
    static void CopyIfChanged(string source, string destination)
    {
        if (!File.Exists(destination) || Sha(destination) != Sha(source)) File.Copy(source, destination, true);
    }

    static void PrintEditorExtraction(WorkspaceSettings settings, string editor, string[] modules,
        EditorSelection? previous)
    {
        Console.WriteLine("Editor extraction: " + settings.Method + " (" + settings.Profile + ")");
        if (previous is not null && (previous.Assembly != settings.Assembly || previous.Method != settings.Method ||
                previous.Profile != settings.Profile))
            Console.WriteLine("  Replaced " + previous.Method + " (" + previous.Profile + "): a package holds one " +
                "extraction, so every proof in it now sees this one.");
        Console.WriteLine("  Modules: " + string.Join(", ", modules) + " in " + CliPaths.Display(editor));
        Console.WriteLine("  Proof: " + CliPaths.Display(settings.Proof));
        if (settings.CreatedPackage)
            Console.WriteLine("  Created a Lake package beside the proof (no lakefile above it): lakefile.toml, " +
                "lean-toolchain and lake-manifest.json, with the bundled framework in " + BundledFrameworkDirectory);
        Console.WriteLine("  Edit the proof in place. After rebuilding the assembly, run this command again and " +
            "restart the file in the editor to load the refreshed extraction.");
        Console.WriteLine("  Editor checking is not a certificate. Run ordinary leancil verify for certification.");
    }
}
