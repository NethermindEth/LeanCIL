using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
    /// <summary>A request to refresh the editor extraction of the Lake package `ProofRoot` holding `Proof`.</summary>
    sealed record WorkspaceSettings(string Assembly, string Method, string Profile, string Proof, string ProofRoot,
        string? AssemblyIdentity, string[] InitializedTypes, string? Theorem, bool CreatedPackage);

    /// <summary>
    /// One method extraction in the editor library, as `extract` takes it, and the proofs written against it.
    /// </summary>
    sealed record EditorSelection(string Assembly, string Method, string Profile, string? AssemblyIdentity,
        string[] InitializedTypes, EditorProof[] Proofs);

    /// <summary>A proof of a selection, relative to its package, and the theorem that verifies it, if named.</summary>
    sealed record EditorProof(string Proof, string? Theorem);

    /// <summary>Where the framework's editor library reads its sources, relative to the framework package.</summary>
    const string EditorSourceDirectory = ".lake/leancil";
    /// <summary>Below the editor sources: per key, the selection and the verification outputs of its proofs.</summary>
    const string EditorSelectionsDirectory = "selections";
    const string EditorSelectionFile = "selection.json";
    const string WorkspaceUsage = "Usage: leancil workspace assembly.dll method --profile profile --proof proof.lean " +
        "[--theorem name] [--proof-root package-directory] [--assembly identity] [--assume-initialized type]...";

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
            else if (option is not ("--profile" or "--proof" or "--proof-root" or "--assembly" or "--theorem") ||
                !options.TryAdd(option, args[index]))
                throw new ArgumentException("Unknown or duplicate option: " + option);
        }
        if (!options.TryGetValue("--profile", out var profile) || !options.TryGetValue("--proof", out var proof))
            throw new ArgumentException(WorkspaceUsage);
        if (profile.StartsWith('@')) profile = "@" + Path.GetFullPath(profile[1..]);
        var theorem = options.GetValueOrDefault("--theorem");
        if (theorem is not null &&
            !System.Text.RegularExpressions.Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
            throw new ArgumentException("Invalid theorem name: " + theorem);
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
            [.. initialized], theorem, created);
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
    /// Writes the selected method's extraction into the framework's editor library in the proof's package as
    /// `Extracted.KEY` (and `ExtractedSymbols.KEY`) and builds it there, so the proof resolves its own method's
    /// extraction in place beside other methods' ones. Nothing here is or yields a certificate.
    /// </summary>
    static void RefreshEditorExtraction(WorkspaceSettings settings)
    {
        var root = settings.ProofRoot;
        var editor = Path.Combine(EditorFramework(root), EditorSourceDirectory);
        var selection = new EditorSelection(settings.Assembly, settings.Method, settings.Profile,
            settings.AssemblyIdentity, settings.InitializedTypes, []);
        var extraction = ExtractEditorSelection(selection);
        try
        {
            var key = SelectionModules.Key(ExtractionIdentity.Read(extraction).Root);
            var proof = new EditorProof(Path.GetRelativePath(root, settings.Proof).Replace('\\', '/'),
                settings.Theorem);
            var previous = ReadEditorSelection(Path.Combine(editor, EditorSelectionsDirectory, key));
            selection = selection with
            {
                Proofs = [.. (previous?.Proofs ?? []).Where(other => other.Proof != proof.Proof).Append(proof)
                    .OrderBy(other => other.Proof, StringComparer.Ordinal)]
            };
            var modules = ApplyEditorExtraction(editor, key, extraction, selection);
            BuildEditorModules(root, modules);
            PrintEditorExtraction(settings, editor, key, modules);
        }
        finally
        {
            Directory.Delete(extraction, true);
        }
    }

    /// <summary>Extracts `selection` into a new scratch directory, which the caller deletes.</summary>
    static string ExtractEditorSelection(EditorSelection selection)
    {
        var extraction = Path.Combine(Path.GetTempPath(), "leancil-editor-" + Guid.NewGuid().ToString("N"));
        try
        {
            RunExtractor([.. Extract("extract", selection.Assembly, selection.AssemblyIdentity, selection.Method,
                    extraction, selection.Profile),
                .. selection.InitializedTypes.SelectMany(type => new[] { "--assume-initialized", type })]);
            // The command takes no --import, so an extraction never needs contract interface modules here.
            if (ExtractionIdentity.Read(extraction).Sources.Count > 0)
                throw new InvalidDataException("Editor extraction unexpectedly carries contract interface modules.");
            return extraction;
        }
        catch
        {
            if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
            throw;
        }
    }

    static EditorSelection? ReadEditorSelection(string directory) =>
        Path.Combine(directory, EditorSelectionFile) is var path && File.Exists(path)
            ? JsonSerializer.Deserialize<EditorSelection>(File.ReadAllText(path)) : null;

    /// <summary>Every selection recorded in the editor library at `editor`, by key.</summary>
    static SortedDictionary<string, EditorSelection> EditorSelections(string editor)
    {
        var selections = new SortedDictionary<string, EditorSelection>(StringComparer.Ordinal);
        var directory = Path.Combine(editor, EditorSelectionsDirectory);
        if (!Directory.Exists(directory)) return selections;
        foreach (var selection in Directory.EnumerateDirectories(directory))
            if (ReadEditorSelection(selection) is { } recorded) selections[Path.GetFileName(selection)] = recorded;
        return selections;
    }

    static string EditorModulePath(string editor, string module) =>
        Path.Combine(editor, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");

    /// <summary>
    /// The editor's copy of PDB names: the extraction's `Symbols.lean` without the PDB hash in its first line, so
    /// a rebuild that moves no line of this method leaves the module and its importers unbuilt.
    /// </summary>
    static string EditorSymbols(string symbols) => System.Text.RegularExpressions.Regex.Replace(symbols,
        @"\A-- Generated from the portable PDB with SHA-256 [0-9a-f]+\.", "-- Generated from the portable PDB.");

    /// <summary>Whether the editor modules of `key` differ from the extraction in `extraction`.</summary>
    static bool EditorModulesDiffer(string editor, string key, string extraction)
    {
        var module = EditorModulePath(editor, "Extracted." + key);
        var symbolsModule = EditorModulePath(editor, "ExtractedSymbols." + key);
        var symbols = Path.Combine(extraction, "Symbols.lean");
        return !File.Exists(module) || File.ReadAllText(module) != File.ReadAllText(Path.Combine(extraction,
                "Extracted.lean")) ||
            File.Exists(symbols) != File.Exists(symbolsModule) ||
            (File.Exists(symbols) && File.ReadAllText(symbolsModule) != EditorSymbols(File.ReadAllText(symbols)));
    }

    /// <summary>
    /// Records `selection` and the extraction in `extraction` under `key` and returns its editor modules. Unchanged
    /// bytes are not rewritten, which keeps Lake's traces, so an unchanged method rebuilds nothing.
    /// </summary>
    static string[] ApplyEditorExtraction(string editor, string key, string extraction, EditorSelection selection)
    {
        Directory.CreateDirectory(editor);
        // A plain module here would let a proof that names no method check against whichever method wrote it.
        File.Delete(Path.Combine(editor, "Extracted.lean"));
        File.Delete(Path.Combine(editor, "ExtractedSymbols.lean"));
        var directory = Path.Combine(editor, EditorSelectionsDirectory, key);
        Directory.CreateDirectory(directory);
        WriteIfChanged(Path.Combine(directory, EditorSelectionFile), JsonSerializer.Serialize(selection, Json) + "\n");
        var module = EditorModulePath(editor, "Extracted." + key);
        Directory.CreateDirectory(Path.GetDirectoryName(module)!);
        CopyIfChanged(Path.Combine(extraction, "Extracted.lean"), module);
        var symbols = Path.Combine(extraction, "Symbols.lean");
        var symbolsModule = EditorModulePath(editor, "ExtractedSymbols." + key);
        // Without a PDB the import fails at its source instead of loading names of an older build.
        if (!File.Exists(symbols))
        {
            File.Delete(symbolsModule);
            return ["Extracted." + key];
        }
        Directory.CreateDirectory(Path.GetDirectoryName(symbolsModule)!);
        WriteIfChanged(symbolsModule, EditorSymbols(File.ReadAllText(symbols)));
        return ["Extracted." + key, "ExtractedSymbols." + key];
    }

    /// <summary>Removes the editor modules of `key`, so a proof importing them fails at the import.</summary>
    static void RemoveEditorModules(string editor, string key)
    {
        File.Delete(EditorModulePath(editor, "Extracted." + key));
        File.Delete(EditorModulePath(editor, "ExtractedSymbols." + key));
    }

    static void BuildEditorModules(string root, IReadOnlyCollection<string> modules)
    {
        if (modules.Count > 0)
            Run(["lake", "build", .. modules.Select(module => "+" + module)], root,
                progress: "Building " + string.Join(", ", modules) + " (the first build also builds the framework)");
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
        // A source that a keyed import could resolve to would shadow the generated extraction.
        var sources = packages.SelectMany(package => ConsumerSources(package).Where(path =>
            Path.GetFileName(path) is "Extracted.lean" or "ExtractedSymbols.lean" ||
            Path.GetRelativePath(package, path).Split('/', '\\')[..^1]
                .Any(directory => directory is "Extracted" or "ExtractedSymbols"))).ToArray();
        if (sources.Length > 0)
            throw new InvalidDataException("Extracted and ExtractedSymbols are reserved for the selected " +
                "extractions; remove " + CliPaths.Display(sources[0]) + ".");
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

    static void PrintEditorExtraction(WorkspaceSettings settings, string editor, string key, string[] modules)
    {
        Console.WriteLine("Editor extraction: " + settings.Method + " (" + settings.Profile + ")");
        Console.WriteLine("  Import: " + string.Join(", ", modules.Select(module => "import " + module)));
        Console.WriteLine("  Modules in " + CliPaths.Display(editor));
        Console.WriteLine("  Proof: " + CliPaths.Display(settings.Proof));
        // The editor resolves no plain Extracted, so a proof still naming it, or another method, fails at its import.
        foreach (var import in SourceImport().Matches(File.ReadAllText(settings.Proof))
            .Select(match => match.Groups[1].Value).Distinct(StringComparer.Ordinal))
            if (import is "Extracted" or "ExtractedSymbols" ||
                (SelectionModules.Is(import) && !modules.Contains(import, StringComparer.Ordinal)))
                Console.WriteLine("  The proof imports " + import + ", which is not this method's extraction; " +
                    "replace it with import " + (import.StartsWith("ExtractedSymbols", StringComparison.Ordinal)
                        ? "ExtractedSymbols." : "Extracted.") + key + ".");
        var others = EditorSelections(editor).Count(pair => pair.Key != key);
        if (others > 0)
            Console.WriteLine($"  The package holds {others} other method extraction{(others == 1 ? "" : "s")}; " +
                "their modules are unchanged.");
        if (settings.CreatedPackage)
            Console.WriteLine("  Created a Lake package beside the proof (no lakefile above it): lakefile.toml, " +
                "lean-toolchain and lake-manifest.json, with the bundled framework in " + BundledFrameworkDirectory);
        Console.WriteLine("  Edit the proof in place. After rebuilding the assembly, run this command again and " +
            "restart the file in the editor to load the refreshed extraction.");
        Console.WriteLine("  Editor checking is not a certificate. Run ordinary leancil verify for certification.");
    }
}
