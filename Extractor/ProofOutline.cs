using System.Runtime.ExceptionServices;
using ILOpCode = System.Reflection.Metadata.ILOpCode;
using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// `new-proof`: a starting Lean proof for a checked extraction's entry method. Every hole is a
// `sorry`, so the file elaborates but `verify` rejects it until each hole is filled. It imports
// the extraction's keyed module, which resolves both in the editor workspace and under verify.
internal static partial class ProofOutline
{
    /// <summary>The frame and instruction descriptors used to outline a proof of this method.</summary>
    internal sealed class Method(FrameMetadata frame, Operation[] operations, MethodDefinition source,
        IReadOnlySet<Instruction> reachable, IReadOnlyDictionary<int, int> parameterHomes,
        FeatureProfile profile, MetadataValidation.LayoutContext layouts, InstructionIndex instructions,
        ResolvedCallSites calls, IReadOnlyDictionary<MethodDefinition, int> methodIndices, ImportResolution? imports)
    {
        internal FrameMetadata Frame { get; } = frame;
        internal Operation[] Operations { get; } = operations;

        /// <summary>The argument read directly at a reachable site. Addressed and assigned arguments use a frame slot.</summary>
        internal int? ArgumentAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            return Operations[pc] is Unoutlined && reachable.Contains(site) &&
                MethodArguments.LoadIndex(source, site) is int index && !parameterHomes.ContainsKey(index)
                ? index : null;
        }

        /// <summary>The callee selected by the original reachable call and its binding.</summary>
        internal (CallKind Kind, int Method, int Arguments)? CallAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            return Operations[pc] is Unoutlined && reachable.Contains(site)
                ? calls.OutlineTarget(site, methodIndices, imports) : null;
        }

        /// <summary>The normalized opcode and instruction index of the branch's original destination.</summary>
        internal (ILOpCode Kind, int Target)? BranchAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            if (Operations[pc] is not Unoutlined || site.Operand is not Instruction target ||
                site.OpCode.OperandType is not (OperandType.InlineBrTarget or OperandType.ShortInlineBrTarget) ||
                site.OpCode.Code is Code.Leave or Code.Leave_S || !reachable.Contains(site)) return null;
            int opcode = site.OpCode.Value;
            // ECMA-335 assigns both branch families in the same order.
            if (opcode is >= (int)ILOpCode.Br_s and <= (int)ILOpCode.Blt_un_s)
                opcode += (int)ILOpCode.Br - (int)ILOpCode.Br_s;
            return ((ILOpCode)opcode, instructions.Position(target));
        }

        /// <summary>The storage shape of a reachable CIL type operand with the requested opcode.</summary>
        internal (int? Bytes, int? ScalarWidth, bool Signed)? ObjectAt(int pc, Code opcode)
        {
            var site = source.Body.Instructions[pc];
            if (site.OpCode.Code != opcode || Operations[pc] is not Unoutlined ||
                !reachable.Contains(site) || site.Operand is not TypeReference operand) return null;
            return InstructionOperands.ObjectStorage(source, site, operand, instructions, layouts, profile);
        }

        /// <summary>The word pushed by a literal, a modelled call or the size of a closed type.</summary>
        internal (int Width, long Value, bool Numeral)? ConstantAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            if (Operations[pc] is not Unoutlined || !reachable.Contains(site)) return null;
            var code = site.OpCode.Code;
            return code switch
            {
                Code.Ldc_I4_M1 => (32, -1, false),
                >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8 => (32, code - Code.Ldc_I4_0, true),
                Code.Ldc_I4 or Code.Ldc_I4_S => (32, Convert.ToInt64(site.Operand), false),
                Code.Ldc_I8 => (64, (long)site.Operand, false),
                Code.Sizeof when ObjectAt(pc, code)?.Bytes is int size => (32, size, true),
                Code.Ldsfld when site.Operand is FieldReference field &&
                    FeatureProfile.PlatformField(field) is int value => (32, value, true),
                Code.Call when calls.IsModel(site) && site.Operand is MethodReference member &&
                    (FeatureProfile.PlatformConstant(member) ??
                     ReferenceQueries.Constant(member, profile.Architecture) ??
                     UnsafeModels.SizeOf(member, profile.Architecture)) is int value => (32, value, true),
                _ => null
            };
        }

        /// <summary>The result width of a reachable bit-count call bound to its runtime declaration.</summary>
        internal int? BitCountWidthAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            return Operations[pc] is Unoutlined && site.OpCode.Code == Code.Call &&
                site.Operand is MethodReference member && reachable.Contains(site) && calls.IsModel(site)
                ? BitModels.CountWidth(member, profile) : null;
        }

        /// <summary>Whether one checked, straight-line word step suffices for this site.</summary>
        internal bool PureAt(int pc, bool plainReturn) => Operations[pc] switch
        {
            StackOperation { Kind: Code.Ret } => plainReturn,
            Unoutlined when ArgumentAt(pc) is int argument => MethodArguments.Plain(source, argument),
            var operation => ConstantAt(pc) is { Width: 32 or 64 } ||
                BitCountWidthAt(pc) is not null || operation is StackOperation { Kind:
                    Code.Add or Code.Sub or Code.Mul or Code.And or Code.Or or Code.Xor or Code.Nop or
                    Code.Conv_I8 or Code.Conv_I or Code.Conv_U8 or Code.Conv_U4 or Code.Conv_I4 }
        };

        /// <summary>The admitted struct field at this instruction, using the extraction's layout context.</summary>
        internal (Code Opcode, int Offset, int Width, bool Signed, bool IsAggregate)? StructFieldAt(int pc)
        {
            var site = source.Body.Instructions[pc];
            if (site.OpCode.Code is not (Code.Ldfld or Code.Ldflda or Code.Stfld) ||
                !reachable.Contains(site) || site.Operand is not FieldReference field ||
                ObjectTypes.Candidate(field.DeclaringType)) return null;
            var definition = field.Resolve() ?? throw new InvalidDataException("Unresolved field");
            return InstructionOperands.StructField(field, definition, site.OpCode.Code, source, profile, layouts);
        }
    }

    /// <summary>A checked extraction: its methods while still loaded, their emitted operations and
    /// its computed layouts in emission order, each with its identity, its named class fields, and
    /// the architecture that sizes its struct array elements.</summary>
    internal sealed record Extraction(MethodDefinition[] Methods, Method[] Emitted,
        ClassViews.View[] Views, IReadOnlyDictionary<(int Method, int Pc), ClassViews.FieldOperation> ClassFields,
        string Architecture,
        ComputedLayout[] Layouts);

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
