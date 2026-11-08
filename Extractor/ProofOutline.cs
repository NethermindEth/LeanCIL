using System.Runtime.ExceptionServices;
using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// `new-proof`: a starting Lean proof for a checked extraction's entry method. Every hole is a
// `sorry`, so the file elaborates but `verify` rejects it until each hole is filled.
internal static partial class ProofOutline
{
    /// <summary>A checked extraction: its methods while still loaded, their emitted operations and
    /// the layout identities in emission order, and the checked `Extracted.lean` source.</summary>
    internal sealed record Extraction(MethodDefinition[] Methods, TemplateEmitter.Method[] Emitted,
        string[] LayoutIdentities, string Source, ClassViews.View[] Views);

    const string Usage = "Usage: leancil new-proof extraction-directory proof.lean";

    internal static void Run(string[] args, Action<string, Action<Extraction>> read)
    {
        if (args.Length != 2 || args.Any(argument => argument.StartsWith("--", StringComparison.Ordinal)))
            throw new ArgumentException(Usage);
        var directory = Path.GetFullPath(args[0]);
        var proof = Path.GetFullPath(args[1]);
        if (File.Exists(proof) || Directory.Exists(proof))
            throw new IOException($"{CliPaths.Display(proof)} already exists; new-proof never overwrites a proof. " +
                "Choose another path or remove it first.");
        Outline? outline = null;
        Exception? generation = null;
        try
        {
            read(directory, extraction =>
            {
                try { outline = Generate(extraction); }
                catch (Exception error) { generation = error; }
            });
        }
        catch (Exception error) { throw new CliFailure("extraction integrity", error); }
        if (generation is not null) ExceptionDispatchInfo.Throw(generation);
        if (outline is null) throw new InvalidDataException("The extraction check produced no methods.");
        Directory.CreateDirectory(Path.GetDirectoryName(proof)!);
        using (var stream = new FileStream(proof, FileMode.CreateNew, FileAccess.Write))
        {
            var bytes = new UTF8Encoding(false).GetBytes(outline.Source);
            stream.Write(bytes);
        }
        Console.WriteLine($"Wrote {CliPaths.Display(proof)}: a starting proof of {outline.Signature}");
        var paths = outline.Paths == 1 ? "path" : "paths";
        Console.WriteLine($"  Holes: {outline.Obligations} obligations, {outline.Paths} {paths} not outlined " +
            "(each `sorry`; verify rejects the file until none remain)");
        Console.WriteLine($"  Next: fill the holes, then run leancil verify {CliPaths.Display(directory)} " +
            $"--proof {CliPaths.Display(proof)}");
    }

    /// <summary>A generated proof: its obligations are holes for the author's argument, its paths
    /// holes where the outline could not step the method.</summary>
    sealed record Outline(string Signature, string Source, int Obligations, int Paths);
}
