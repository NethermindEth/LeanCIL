using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record WorkspaceSettings(string Assembly, string Method, string Profile, string Proof, string ProofRoot,
        string Output, string? AssemblyIdentity, string[] InitializedTypes);
    sealed record EditorWorkspace(int Schema, bool EditorOnly, WorkspaceSettings Settings,
        SortedDictionary<string, string> Inputs, SortedDictionary<string, string> ManagedFiles);

    const string WorkspaceProof = "LeanCILProofWorkspace";
    const string WorkspaceManifest = "leancil-workspace.json";
    const string WorkspaceUsage = "Usage: leancil workspace assembly.dll method --profile profile --proof proof.lean " +
        "[--proof-root package-directory] [--output workspace-directory] [--assembly identity] [--assume-initialized type]...";

    internal static void CreateProofWorkspace(string[] args)
    {
        var settings = ParseWorkspaceSettings(args);
        using var verification = new Program();
        verification.MaterializeProofWorkspace(settings);
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
            if (++index == args.Length || string.IsNullOrWhiteSpace(args[index]) || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException("Missing value for " + option + ".");
            if (option == "--assume-initialized")
            {
                if (!initialized.Add(args[index])) throw new ArgumentException("Duplicate initialization assumption: " + args[index]);
            }
            else if (option is not ("--profile" or "--proof" or "--proof-root" or "--output" or "--assembly") ||
                !options.TryAdd(option, args[index]))
                throw new ArgumentException("Unknown or duplicate option: " + option);
        }
        if (!options.TryGetValue("--profile", out var profile) || !options.TryGetValue("--proof", out var proof))
            throw new ArgumentException(WorkspaceUsage);
        if (profile.StartsWith('@')) profile = "@" + Path.GetFullPath(profile[1..]);
        var assembly = Path.GetFullPath(args[0]);
        proof = Path.GetFullPath(proof);
        var root = options.TryGetValue("--proof-root", out var selectedRoot)
            ? Path.GetFullPath(selectedRoot) : FindProofPackage(proof);
        Within(root, Path.GetRelativePath(root, proof));
        var output = options.TryGetValue("--output", out var selectedOutput) ? Path.GetFullPath(selectedOutput)
            : Path.Combine(root, ".work", "leancil", ContentKey(assembly + "\n" + args[1] + "\n" + profile)[..20]);
        var back = Path.GetRelativePath(output, root);
        if (!Path.IsPathRooted(back) && back != ".." && !back.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new ArgumentException("Workspace output must not contain the source consumer package.");
        var relativeOutput = Path.GetRelativePath(root, output);
        if (!Path.IsPathRooted(relativeOutput) && relativeOutput != ".." &&
            !relativeOutput.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal) &&
            relativeOutput.Split(Path.DirectorySeparatorChar)[0] is not (".work" or "artifacts" or "generated" or "bin" or "obj"))
            throw new ArgumentException("Place a workspace outside the consumer package or under its .work or artifacts directory.");
        return new(assembly, args[1], profile, proof, root, output, options.GetValueOrDefault("--assembly"), [.. initialized]);
    }

    static string FindProofPackage(string proof)
    {
        DirectoryInfo? directory = new(Path.GetDirectoryName(proof)!);
        while (directory is not null)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")) || File.Exists(Path.Combine(directory.FullName, "lakefile.lean")))
                return directory.FullName;
            directory = directory.Parent;
        }
        throw new InvalidDataException("No consumer Lake package found. Supply --proof-root and run lake update there first.");
    }

    static SortedDictionary<string, string> WorkspaceInputs(WorkspaceSettings settings)
    {
        var inputs = ConsumerSnapshot(settings.ProofRoot, settings.Output);
        foreach (var (path, hash) in LibrarySources(CommonInputs()))
            inputs["framework:" + path] = hash;
        inputs["assembly:" + settings.Assembly] = Sha(settings.Assembly);
        var pdb = Path.ChangeExtension(settings.Assembly, ".pdb");
        inputs["pdb:" + pdb] = File.Exists(pdb) ? Sha(pdb) : "absent";
        inputs["extractor"] = Sha(ExtractorPath);
        inputs["settings"] = ContentKey(JsonSerializer.Serialize(settings));
        if (settings.Profile.StartsWith('@'))
        {
            var profilePath = Path.GetFullPath(settings.Profile[1..]);
            inputs["profile:" + profilePath] = Sha(profilePath);
        }
        return inputs;
    }

    void MaterializeProofWorkspace(WorkspaceSettings settings)
    {
        var inputs = WorkspaceInputs(settings);
        var manifestPath = Path.Combine(settings.Output, WorkspaceManifest);
        if (Directory.Exists(settings.Output))
        {
            if (!File.Exists(manifestPath)) throw new InvalidDataException("Workspace output already exists without an editor workspace manifest.");
            var existing = JsonSerializer.Deserialize<EditorWorkspace>(File.ReadAllText(manifestPath))
                ?? throw new InvalidDataException("Invalid editor workspace manifest.");
            if (existing.Schema != 1 || !existing.EditorOnly || existing.Inputs is null || existing.ManagedFiles is null ||
                !Same(inputs, existing.Inputs))
                throw new InvalidDataException("Stale editor workspace: assembly, profile, PDB, toolchain, framework or consumer dependencies changed. Preserve your proof edits and select a new --output directory.");
            foreach ((string relative, string hash) in existing.ManagedFiles)
            {
                var path = Within(settings.Output, relative);
                if (!File.Exists(path) || Sha(path) != hash)
                    throw new InvalidDataException("Editor workspace generated or support source changed: " + relative + ". Select a new --output directory.");
            }
            var sources = ConsumerSources(settings.Output).Concat(ConsumerDependencies(settings.Output)
                .SelectMany(dependency => ConsumerSources(dependency.Directory)));
            foreach (var path in sources)
            {
                var relative = Path.GetRelativePath(settings.Output, path).Replace('\\', '/');
                if (relative != WorkspaceManifest && relative != WorkspaceProof + ".lean" && !existing.ManagedFiles.ContainsKey(relative))
                    throw new InvalidDataException("Editor workspace contains an unrecorded source: " + relative + ". Select a new --output directory.");
            }
            if (!File.Exists(Path.Combine(settings.Output, WorkspaceProof + ".lean")))
                throw new InvalidDataException("Editor workspace proof is missing. Select a new --output directory.");
            PrintWorkspace(settings);
            return;
        }

        var staging = settings.Output + ".staging-" + Guid.NewGuid().ToString("N");
        var extraction = Path.Combine(staging, ".work", "extraction");
        Directory.CreateDirectory(staging);
        try
        {
            Run([.. Extract("extract", settings.Assembly, settings.AssemblyIdentity, settings.Method, extraction, settings.Profile),
                .. settings.InitializedTypes.SelectMany(type => new[] { "--assume-initialized", type })]);
            var dependencies = ConsumerDependencies(settings.ProofRoot);
            var symbols = File.Exists(Path.Combine(extraction, "Symbols.lean")) ? Sha(Path.Combine(extraction, "Symbols.lean")) : null;
            var prepared = PrepareConsumerSession(staging, settings.ProofRoot, dependencies, inputs, null,
                ExtractionIdentity.Read(extraction), [(WorkspaceProof, settings.Proof, extraction)], symbols,
                purpose: ConsumerSessionPurpose.Editor);
            if (!Same(inputs, WorkspaceInputs(settings))) throw new InvalidDataException("Workspace inputs changed during generation.");
            var managed = new SortedDictionary<string, string>(StringComparer.Ordinal);
            foreach (var path in prepared.Copied.Keys.Where(path => path != Path.Combine(staging, WorkspaceProof + ".lean")))
                managed[Path.GetRelativePath(staging, path).Replace('\\', '/')] = Sha(path);
            foreach (var path in Directory.EnumerateFiles(extraction))
                managed[Path.GetRelativePath(staging, path).Replace('\\', '/')] = Sha(path);
            var manifest = new EditorWorkspace(1, true, settings, inputs, managed);
            File.WriteAllText(Path.Combine(staging, WorkspaceManifest), JsonSerializer.Serialize(manifest, Json) + "\n");
            File.WriteAllText(Path.Combine(staging, "LEANCIL-WORKSPACE.md"),
                "# LeanCIL editor workspace\n\nEditor checking is not a certificate. This workspace publishes no verification report or trusted receipt.\n\n" +
                "Edit " + WorkspaceProof + ".lean. Open this directory with the Lean language server, or run `lake build +" + WorkspaceProof + ":olean`.\n\n" +
                "Re-run the workspace command before checking after source changes. Changed inputs or generated sources cause an explicit rejection. " +
                "Keep proof edits and choose a new output directory to refresh.\n\n" +
                "Copy only the edited proof source back to the original consumer proof path, then run ordinary `leancil verify` with the original package as --proof-root. " +
                "Do not copy workspace caches, generated modules, manifests or build artifacts into the source package.\n");
            Directory.CreateDirectory(Path.GetDirectoryName(settings.Output)!);
            Directory.Move(staging, settings.Output);
            PrintWorkspace(settings);
        }
        finally
        {
            if (Directory.Exists(staging)) Directory.Delete(staging, true);
        }
    }

    static void PrintWorkspace(WorkspaceSettings settings)
    {
        Console.WriteLine("Editor workspace: " + CliPaths.Display(settings.Output));
        Console.WriteLine("  Proof: " + WorkspaceProof + ".lean");
        Console.WriteLine("  Source proof: " + CliPaths.Display(settings.Proof));
        Console.WriteLine("  Editor checking is not a certificate. Run ordinary leancil verify for certification.");
    }
}
