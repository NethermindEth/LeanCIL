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

    /// <summary>Where the editor library reads its sources, relative to the package that declares it.</summary>
    const string EditorSourceDirectory = ".lake/leancil";
    /// <summary>Below the editor sources: per key, the selection and the verification outputs of its proofs.</summary>
    const string EditorSelectionsDirectory = "selections";
    const string EditorSelectionFile = "selection.json";
    const string WorkspaceUsage = "Usage: leancil workspace assembly.dll method --profile profile --proof proof.lean " +
        "[--theorem name] [--proof-root package-directory] [--assembly identity] [--assume-initialized type]...\n" +
        "       leancil workspace --remove key-or-method [--profile profile] [--proof-root package-directory]";

    internal static void CreateProofWorkspace(string[] args)
    {
        if (args.Length > 0 && args[0] == "--remove") RemoveEditorSelection(args[1..]);
        else RefreshEditorExtraction(ParseWorkspaceSettings(args));
    }

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
        root ??= Path.GetDirectoryName(proof)!;
        Within(root, Path.GetRelativePath(root, proof));
        return new(Path.GetFullPath(args[0]), args[1], profile, proof, root, options.GetValueOrDefault("--assembly"),
            [.. initialized], theorem, created);
    }

    static string? FindProofPackage(string proof) => FindPackage(Path.GetDirectoryName(proof)!);

    /// <summary>The nearest directory at or above `start` holding a Lake package, if any.</summary>
    static string? FindPackage(string start)
    {
        DirectoryInfo? directory = new(start);
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
    /// Makes `package` a Lake package that declares the editor library and requires, by path, the certified
    /// library where it is cached, so it holds no framework sources or build of its own. A changed framework
    /// has another cache entry, which the requirement then names. Nothing is fetched or committed, so the
    /// user's git configuration plays no part.
    /// </summary>
    static void ScratchProofPackage(string package)
    {
        var toolchainPath = Path.Combine(package, "lean-toolchain");
        var toolchain = File.ReadAllText(At("lean-toolchain")).Trim();
        if (File.Exists(toolchainPath) && File.ReadAllText(toolchainPath).Trim() != toolchain)
            throw new InvalidDataException("A different lean-toolchain already pins " + package +
                "; pass --proof-root for a Lake package on the tool's toolchain.");
        // Lake reads a rewritten requirement on its next run, so pointing it at another library needs no update.
        var lakefile = $"name = \"{ScratchPackageName}\"\n" + FrameworkRequirement(package, EditorLibrary()) +
            EditorLibraryDeclaration(EditorSourceDirectory);
        var lakefilePath = Path.Combine(package, "lakefile.toml");
        if (File.Exists(lakefilePath) && File.ReadAllText(lakefilePath) == lakefile &&
            File.Exists(Path.Combine(package, "lake-manifest.json")))
            return;
        File.Copy(At("lean-toolchain"), toolchainPath, true);
        File.WriteAllText(lakefilePath, lakefile);
        Run(["lake", "update"], package);
    }

    /// <summary>The declaration of the editor library, whose sources are in `sources`.</summary>
    static string EditorLibraryDeclaration(string sources) => $"""

        [[lean_lib]]
        name = "{EditorLibraryName}"
        srcDir = "{sources}"
        roots = ["Extracted", "ExtractedSymbols"]
        defaultFacets = []

        """;

    /// <summary>Relative directory of the package declaring the editor library where leancil is pinned.</summary>
    const string PinnedEditorPackage = ".lake/leancil-editor";
    /// <summary>Lake reads these entries in place of the manifest's entries of the same names.</summary>
    const string PackageOverrides = ".lake/package-overrides.json";
    const string PinnedEditorPackageName = "leancil_editor";

    /// <summary>Whether `root` is a LeanCIL checkout, which is the framework and builds it itself.</summary>
    static bool IsCheckout(string root) => JsonSerializer.Deserialize<JsonElement>(
        File.ReadAllText(Path.Combine(root, "lake-manifest.json"))).GetProperty("name").GetString() == "leancil";

    /// <summary>
    /// Makes Lake resolve the pinned leancil requirement of the package at `root` to the cached certified
    /// library, read in place, which brings in a package below `.lake` that declares the editor library, so the
    /// package's editor builds compile no framework module. The pinned checkout and the manifest are left as
    /// they are, and verification reads neither this nor any `.lake` directory.
    /// </summary>
    static void PinnedProofPackage(string root)
    {
        var editorPackage = Path.Combine(root, PinnedEditorPackage);
        Directory.CreateDirectory(editorPackage);
        FrameworkPackage(root, EditorLibrary(),
            $"\n[[require]]\nname = \"{PinnedEditorPackageName}\"\npath = \"../leancil-editor\"\n");
        WriteIfChanged(Path.Combine(editorPackage, "lakefile.toml"),
            $"name = \"{PinnedEditorPackageName}\"\n" + EditorLibraryDeclaration("../leancil"));
        WriteIfChanged(Path.Combine(editorPackage, "lean-toolchain"), File.ReadAllText(At("lean-toolchain")));
        static object Entry(string name, string directory, bool inherited) => new
        {
            type = "path", scope = "", name, manifestFile = "lake-manifest.json", inherited, dir = directory,
            configFile = "lakefile.toml"
        };
        var overrides = JsonSerializer.Serialize(new
        {
            version = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(root,
                "lake-manifest.json"))).GetProperty("version").GetString(),
            packages = new[]
            {
                Entry("leancil", ".lake/leancil-framework", false),
                Entry(PinnedEditorPackageName, PinnedEditorPackage, true)
            }
        }, Json) + "\n";
        var path = Path.Combine(root, PackageOverrides);
        // Lake would apply another tool's overrides too; replacing them could change what the package builds.
        if (File.Exists(path) && !JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(path))
                .GetProperty("packages").EnumerateArray().Select(package => package.GetProperty("name").GetString())
                .SequenceEqual(["leancil", PinnedEditorPackageName]))
            throw new InvalidDataException(CliPaths.Display(path) + " already holds package overrides that leancil " +
                "workspace did not write. Remove it, then run this command again.");
        WriteIfChanged(path, overrides);
    }

    /// <summary>
    /// The package whose editor library serves `root`, after pointing a generated package or one that pins
    /// leancil at the certified library the tool's framework has in the cache.
    /// </summary>
    static string LinkedEditorPackage(string root, bool created = false)
    {
        if (created || IsScratchPackage(root)) ScratchProofPackage(root);
        var package = EditorPackage(root);
        if (!IsScratchPackage(root) && !IsCheckout(root)) PinnedProofPackage(root);
        return package;
    }

    /// <summary>Where Lake puts the compiled editor modules of the package at `root`.</summary>
    static string EditorBuildDirectory(string root) => IsScratchPackage(root) || IsCheckout(root)
        ? Path.Combine(root, ".lake", "build") : Path.Combine(root, PinnedEditorPackage, ".lake", "build");

    /// <summary>
    /// Writes the selected method's extraction into the editor library of the proof's package as
    /// `Extracted.KEY` (and `ExtractedSymbols.KEY`) and builds it there, so the proof resolves its own method's
    /// extraction in place beside other methods' ones. Nothing here is or yields a certificate.
    /// </summary>
    static void RefreshEditorExtraction(WorkspaceSettings settings)
    {
        var root = settings.ProofRoot;
        var editor = Path.Combine(LinkedEditorPackage(root, settings.CreatedPackage), EditorSourceDirectory);
        // The editor's `lake serve` starts Lean the same way; an oversized environment fails here, not as imports.
        RequireLeanEnvironmentFits(["lake", "serve"], root, new System.Diagnostics.ProcessStartInfo().Environment);
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
            ExtractEditorSelection(selection, extraction);
            return extraction;
        }
        catch
        {
            if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
            throw;
        }
    }

    /// <summary>
    /// Extracts `selection` into `extraction`. Its identity records the assembly relative to that directory, so an
    /// extraction is never copied elsewhere to be verified.
    /// </summary>
    static void ExtractEditorSelection(EditorSelection selection, string extraction)
    {
        RunExtractor([.. Extract("extract", selection.Assembly, selection.AssemblyIdentity, selection.Method,
                extraction, selection.Profile),
            .. selection.InitializedTypes.SelectMany(type => new[] { "--assume-initialized", type })]);
        // The command takes no --import, so an extraction never needs contract interface modules here.
        if (ExtractionIdentity.Read(extraction).Sources.Count > 0)
            throw new InvalidDataException("Editor extraction unexpectedly carries contract interface modules.");
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

    /// <summary>
    /// Drops one selection from the package's editor library: its record, the verification outputs of its proofs,
    /// both modules and their Lake outputs, so a proof importing them fails at the import. Nothing is rebuilt.
    /// </summary>
    static void RemoveEditorSelection(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(WorkspaceUsage);
        var options = new Dictionary<string, string>(StringComparer.Ordinal);
        for (int index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option + ".");
            if (option is not ("--profile" or "--proof-root") || !options.TryAdd(option, args[index]))
                throw new ArgumentException("Unknown or duplicate option: " + option);
        }
        var root = options.TryGetValue("--proof-root", out var selectedRoot) ? Path.GetFullPath(selectedRoot)
            : FindPackage(Environment.CurrentDirectory) ?? throw new InvalidDataException(
                "No Lake package holds the current directory; pass --proof-root.");
        var package = EditorPackage(root);
        var editor = Path.Combine(package, EditorSourceDirectory);
        var selections = EditorSelections(editor);
        var profile = options.GetValueOrDefault("--profile");
        // The key names one selection; a method selector names each profile of it that the package recorded.
        string[] matched = selections.ContainsKey(args[0]) ? [args[0]]
            : [.. selections.Where(pair => pair.Value.Method == args[0] &&
                (profile is null || pair.Value.Profile == profile)).Select(pair => pair.Key)];
        if (matched.Length != 1)
            throw new InvalidDataException((matched.Length == 0 ? "No recorded selection matches " + args[0]
                    : args[0] + " names " + matched.Length + " selections; pass its key or --profile") + ". " +
                (selections.Count == 0 ? "The package records no selection." : "Recorded: " + string.Join(", ",
                    selections.Select(pair => $"{pair.Key} ({pair.Value.Method}, {pair.Value.Profile})")) + "."));
        var key = matched[0];
        var selection = selections[key];
        RemoveEditorModules(editor, key);
        Directory.Delete(Path.Combine(editor, EditorSelectionsDirectory, key), true);
        var build = EditorBuildDirectory(root);
        if (Directory.Exists(build))
            foreach (var output in Directory.EnumerateFiles(build, key + ".*", SearchOption.AllDirectories)
                .Where(path => Path.GetFileName(Path.GetDirectoryName(path)) is "Extracted" or "ExtractedSymbols"))
                File.Delete(output);
        Console.WriteLine($"Removed editor extraction {key}: {selection.Method} ({selection.Profile})");
        foreach (var proof in selection.Proofs.Select(proof => Path.Combine(root, proof.Proof)).Where(File.Exists))
            if (SourceImport().Matches(File.ReadAllText(proof)).Any(import => import.Groups[1].Value.EndsWith(
                    "." + key, StringComparison.Ordinal) && SelectionModules.Is(import.Groups[1].Value)))
                Console.WriteLine("  " + CliPaths.Display(proof) + " imports it and now fails at that import.");
        Console.WriteLine("  Other methods' modules are unchanged and nothing was rebuilt.");
    }

    /// <summary>
    /// Builds the editor modules in the package at `root`. Outside a LeanCIL checkout the package requires the
    /// certified library by path, where Lake would rebuild a stale framework module, so the build must leave
    /// it unwritten.
    /// </summary>
    static void BuildEditorModules(string root, IReadOnlyCollection<string> modules)
    {
        if (modules.Count == 0) return;
        void Build() => Run(["lake", "build", .. modules.Select(module => "+" + module)], root,
            progress: "Building " + string.Join(", ", modules));
        if (!IsCheckout(root)) RequireUnwritten(EditorLibrary(), Build);
        else Build();
    }

    /// <summary>
    /// The package whose editor library serves `root`, which is `root` itself, after the same framework,
    /// toolchain and reserved-module checks as consumer verification.
    /// </summary>
    static string EditorPackage(string root)
    {
        RequireResolvedPackage(root);
        // A source that a keyed import could resolve to would shadow the generated extraction.
        void RequireNoReservedModule(string[] packages)
        {
            var sources = packages.SelectMany(package => ConsumerSources(package).Where(path =>
                Path.GetFileName(path) is "Extracted.lean" or "ExtractedSymbols.lean" ||
                Path.GetRelativePath(package, path).Split('/', '\\')[..^1]
                    .Any(directory => directory is "Extracted" or "ExtractedSymbols"))).ToArray();
            if (sources.Length > 0) throw ReservedModule(root, sources[0]);
        }
        if (IsScratchPackage(root))
        {
            // Its framework is the certified library, whose sources the cache manifest binds to the tool's.
            RequireNoReservedModule([root]);
            return root;
        }
        if (!IsCheckout(root))
        {
            var dependencies = ConsumerDependencies(root);
            // Before the snapshot, which refuses the same sources without saying which or what to do.
            RequireNoReservedModule([root, .. dependencies.Select(dependency => dependency.Directory)]);
            ConsumerSnapshot(root, null, dependencies);
            return root;
        }
        RequireBundledFramework(root, root);
        RequireNoReservedModule([root]);
        // A checkout is the framework package, so its own lakefile declares the editor library.
        if (!File.ReadAllText(Path.Combine(root, "lakefile.toml")).ReplaceLineEndings("\n").Contains(
                $"[[lean_lib]]\nname = \"{EditorLibraryName}\"\nsrcDir = \"{EditorSourceDirectory}\"\n",
                StringComparison.Ordinal))
            throw new InvalidDataException("The leancil checkout at " + CliPaths.Display(root) +
                " declares no " + EditorLibraryName + " library, so an editor cannot resolve Extracted.");
        return root;
    }

    /// <summary>
    /// Fails, naming the cause and its fix, unless `root` is a Lake package whose dependencies are resolved:
    /// the editor library is found through the package's manifest.
    /// </summary>
    static void RequireResolvedPackage(string root)
    {
        var shown = CliPaths.Display(root);
        const string generated = "for a proof outside any Lake package, omit --proof-root and leancil workspace " +
            "generates a package beside the proof";
        if (!File.Exists(Path.Combine(root, "lakefile.toml")) && !File.Exists(Path.Combine(root, "lakefile.lean")))
            throw CliDiagnostics.WithNext(new InvalidDataException(
                    $"The proof root {shown} is not a Lake package: it has no lakefile.toml or lakefile.lean."),
                $"Pass --proof-root the directory holding the lakefile of the proof's package; {generated}.");
        if (!File.Exists(Path.Combine(root, "lake-manifest.json")))
            throw CliDiagnostics.WithNext(new InvalidDataException(
                    $"The proof root {shown} has no lake-manifest.json, so its leancil dependency is not resolved."),
                $"Run `lake update` in {shown}, then run this command again; {generated}.");
    }

    /// <summary>
    /// The failure for `source`, a module of the package at `root` or of a dependency that a keyed
    /// `Extracted` import could resolve to: its cause and fix differ for an extraction directory.
    /// </summary>
    static InvalidDataException ReservedModule(string root, string source)
    {
        var directory = Path.GetDirectoryName(source)!;
        var extraction = Path.GetFileName(source) == "Extracted.lean" &&
            File.Exists(Path.Combine(directory, "identity.json"));
        if (extraction)
            return CliDiagnostics.WithNext(new InvalidDataException(
                    $"The extraction directory {CliPaths.Display(directory)} is inside the proof package " +
                    $"{CliPaths.Display(root)}: its Extracted.lean would shadow the extraction leancil workspace " +
                    "generates for the editor."),
                $"Extract to a directory outside {CliPaths.Display(root)} and delete " +
                $"{CliPaths.Display(directory)}, then run this command again.");
        return CliDiagnostics.WithNext(new InvalidDataException(
                $"{CliPaths.Display(source)} is in the proof package or a dependency under the name Extracted or " +
                "ExtractedSymbols, which are reserved for the extractions leancil workspace generates for the editor."),
            "Rename or remove that module or directory, then run this command again.");
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
                "lean-toolchain and lake-manifest.json. It requires the cached certified library by path.");
        Console.WriteLine("  Edit the proof in place. After rebuilding the assembly, run this command again, or keep " +
            "leancil watch running, and restart the file in the editor to load the refreshed extraction.");
        Console.WriteLine("  Editor checking is not a certificate. Run ordinary leancil verify for certification.");
    }
}
