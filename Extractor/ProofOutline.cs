using System.Runtime.ExceptionServices;
using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// `new-proof`: a starting Lean proof for a checked extraction's entry method. Every hole is a
// `sorry`, so the file elaborates but `verify` rejects it until each hole is filled. It imports
// the extraction's keyed module, which resolves both in the editor workspace and under verify.
internal static partial class ProofOutline
{
    /// <summary>A checked extraction: its methods while still loaded, their emitted operations and
    /// its computed layouts in emission order, each with its identity, its named class fields, and
    /// the architecture that sizes its struct array elements.</summary>
    internal sealed record Extraction(MethodDefinition[] Methods, TemplateEmitter.Method[] Emitted,
        ClassViews.View[] Views, string Architecture,
        ComputedLayout[] Layouts);

    /// <summary>The shape fact `cil_resolution_facts` declares for each element type method `index` names, by the
    /// element term its operations carry, numbered in order of first appearance as that command numbers the raw
    /// operands; none when an element instruction carries no term, as the numbering is then unknown.</summary>
    /// <remarks>An operand with an element storage renders as the raw operand does; one without, such as a class
    /// element the raw code names unlike its array, leaves the numbering unknown.</remarks>
    internal static Func<string, string?> ShapeFacts(Extraction extraction, int index)
    {
        var emitted = extraction.Emitted[index];
        var order = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var pc = 0; pc < emitted.Opcodes.Length; pc++)
        {
            if (emitted.Opcodes[pc] is not (0x8D or 0x8F or 0xA3 or 0xA4)) continue;
            if (emitted.Operations[pc] switch
                {
                    NewArray allocation => allocation.Element,
                    TypedElementAccess { Storage: not null } access => access.Element,
                    ElementAddress address => address.Element,
                    _ => null
                } is not { } element)
                return _ => null;
            order.TryAdd(element, order.Count);
        }
        return element => order.TryGetValue(element, out var shape)
            ? $"Extracted.method{index}_elementShape{shape}" : null;
    }

    /// <summary>The emitted operations as the outline reads them, over frame slots: a homed argument's load, store and
    /// address are those of its home's slot, which follows the declared locals, as the step equations state. Each
    /// such operation still renders as the argument instruction the body holds.</summary>
    internal static Operation[] SlotOperations(TemplateEmitter.Method emitted)
    {
        var frame = emitted.Frame;
        var slots = new Dictionary<int, int>();
        for (var position = 0; position < frame.ParameterHomes.Count; position++)
            slots.TryAdd(frame.ParameterHomes[position].Argument, frame.Locals.Count + position);
        int Home(int argument) => slots.TryGetValue(argument, out var slot) ? slot
            : throw new InvalidDataException($"Argument {argument} is stored or addressed without a home");
        return [.. emitted.Operations.Select(operation => operation switch
        {
            Arg load when slots.ContainsKey(load.Index) => new Local(Home(load.Index)) { Argument = load },
            Starg store => new SetLocal(Home(store.Index)) { Argument = store },
            Ldarga address => new LocalAddress(Home(address.Index)) { Argument = address },
            _ => operation
        })];
    }

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<ComputedLayout[],
        Dictionary<string, int>> LayoutIndices = new();

    /// <summary>The index of the first computed layout with this identity, or -1 when none has it.</summary>
    internal static int LayoutIndex(Extraction extraction, string identity) =>
        LayoutIndices.GetValue(extraction.Layouts, static layouts =>
        {
            var indices = new Dictionary<string, int>(StringComparer.Ordinal);
            for (var index = 0; index < layouts.Length; index++) indices.TryAdd(layouts[index].Identity, index);
            return indices;
        }).GetValueOrDefault(identity, -1);

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
                var module = "Extracted." + global::Program.SelectionModules.Key(
                    global::Program.ExtractionIdentity.Read(directory).Root);
                try { outline = Generate(extraction, module); }
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
        var verify = $"leancil verify {CliPaths.Display(directory)} --proof {CliPaths.Display(proof)}";
        Console.WriteLine($"  Next: {verify} --goals prints the goal at each hole; fill them, then verify " +
            "without --goals");
    }

    /// <summary>A generated proof: its obligations are holes for the author's argument, its paths
    /// holes where the outline could not step the method.</summary>
    sealed record Outline(string Signature, string Source, int Obligations, int Paths);
}
