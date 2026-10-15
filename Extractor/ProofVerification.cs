using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

// Share the same fresh-build and theorem-audit implementation as the test scripts.
partial class Program
{
    sealed record VerificationSettings(int schema, string proof, string theorem, string? proofRoot = null);

    internal static void VerifyArtifacts(string[] args)
    {
        if (args.Length == 0 || args[0].StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException("Usage: leancil verify output-directory [--proof proof.lean] [--theorem name] [--fresh] [--proof-root package-directory]");

        var output = Path.GetFullPath(args[0]);
        string? proof = null;
        string? theorem = null;
        var fresh = false;
        string? proofRoot = null;

        for (var index = 1; index < args.Length; index++)
        {
            var option = args[index];
            if (option == "--fresh" && !fresh)
            {
                fresh = true;
                continue;
            }
            if (++index == args.Length || args[index].StartsWith("--", StringComparison.Ordinal))
                throw new ArgumentException($"Missing value for {option}.");

            switch (option)
            {
                case "--proof-root" when proofRoot is null:
                    proofRoot = Path.GetFullPath(args[index]);
                    break;
                case "--proof" when proof is null:
                    proof = Path.GetFullPath(args[index]);
                    break;
                case "--theorem" when theorem is null:
                    theorem = args[index];
                    break;
                default:
                    throw new ArgumentException($"Unknown or duplicate option: {option}");
            }
        }

        var reportPath = Path.Combine(output, "verified.json");
        var settingsPath = Path.Combine(output, "verification.json");
        var stage = "proof selection";
        try
        {
            if (File.Exists(settingsPath))
            {
                var saved = JsonSerializer.Deserialize<VerificationSettings>(File.ReadAllText(settingsPath),
                    new JsonSerializerOptions { UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow })
                    ?? throw new InvalidDataException("Missing verification settings.");
                if (saved.schema != 1 || string.IsNullOrWhiteSpace(saved.proof) || string.IsNullOrWhiteSpace(saved.theorem))
                    throw new InvalidDataException("Invalid verification.json: expected schema 1, proof and theorem.");
                proof ??= Path.GetFullPath(saved.proof, output);
                theorem ??= saved.theorem;
                if (saved.proofRoot is not null) proofRoot ??= Path.GetFullPath(saved.proofRoot, output);
            }
            else if (proof is null && File.Exists(reportPath))
            {
                // Migrate proof selection from reports created before settings were separate.
                var previous = JsonSerializer.Deserialize<Report>(File.ReadAllText(reportPath))
                    ?? throw new InvalidDataException("Missing verification report.");
                proof = previous.inputs.Keys.Single(key => key.StartsWith("proof:", StringComparison.Ordinal))[6..];
                theorem ??= previous.theorem;
            }

            File.Delete(reportPath);
            proof ??= Path.Combine(output, "Proof.lean");
            theorem ??= "ExampleProof.correctness";
            if (!Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
                throw new ArgumentException("Invalid theorem name");
            if (!File.Exists(proof))
                throw new FileNotFoundException($"Proof file not found: {CliPaths.Display(proof)}", proof);

            // Settings are reusable inputs and survive both successful and failed proofs.
            Directory.CreateDirectory(output);
            var settings = new VerificationSettings(1, Path.GetRelativePath(output, proof).Replace('\\', '/'), theorem,
                proofRoot is null ? null : Path.GetRelativePath(output, proofRoot).Replace('\\', '/'));
            File.WriteAllText(settingsPath, JsonSerializer.Serialize(settings, Json) + "\n");
            stage = "extraction integrity";
            var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
            var assembly = Path.GetFullPath(manifest.GetProperty("assemblyPath").GetString()!, output);
            var identity = manifest.GetProperty("assemblyIdentity").GetString()!;
            var entry = manifest.GetProperty("entry").GetString()!;

            using var verification = new Program { freshLibrary = fresh };
            var report = proofRoot is null
                ? verification.Verify(assembly, identity, entry, proof, output,
                    theorem: theorem, existingArtifacts: true, settings: settingsPath, stage: value => stage = value)
                : verification.VerifyConsumer(assembly, proof, output, theorem, proofRoot, settingsPath, value => stage = value);

            Console.WriteLine($"Verified: {report.theorem}");
            Console.WriteLine($"  Assembly: {identity}");
            Console.WriteLine($"  Entry: {entry}");
            if (manifest.TryGetProperty("initializedTypes", out var initializedTypes))
                foreach (var name in initializedTypes.EnumerateArray())
                    Console.WriteLine($"  Caller assumption: {name.GetString()} initialization completed successfully before invocation.");
            Console.WriteLine($"  Proof: {CliPaths.Display(proof)}");
            Console.WriteLine($"  Axioms: {(report.axioms.Length == 0 ? "none" : string.Join(", ", report.axioms))}");
            Console.WriteLine($"  Settings: {CliPaths.Display(settingsPath)}");
            Console.WriteLine($"  Report: {CliPaths.Display(reportPath)}");
            Console.WriteLine("  Statement:");
            var statement = report.theoremAudit.Split("'" + report.theorem + "'", 2)[0].Trim();
            foreach (var line in statement.Split('\n'))
                Console.WriteLine("    " + line.TrimEnd());
        }
        catch (Exception error)
        {
            File.Delete(reportPath);
            throw new CliFailure(stage, error);
        }
    }
}
