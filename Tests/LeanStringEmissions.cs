extern alias IdentityExtractor;

using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;
using Verification = IdentityExtractor::Program;

partial class Program
{
    static void CheckLeanStringEmissions()
    {
        string directory = At($"artifacts/LeanStrings-\U00010401-{Guid.NewGuid():N}");
        Directory.CreateDirectory(directory);
        string build = Run(["lake", "build", "+StrictBinding.Image", "+CIL.Interface.FullTransfer"], Root);
        if (build.Contains("sorryAx", StringComparison.Ordinal)) throw new InvalidOperationException(build);
        string leanPath = string.Join(Path.PathSeparator, directory, At(".lake/build/lib/lean"));
        var checks = new EmissionChecks(directory, leanPath);
        checks.Callees();
        checks.Assumptions();
        checks.SymbolValues();
        checks.Capture();
        checks.LakeArguments();
        checks.ImageIdentity();
    }

    sealed class EmissionChecks(string directory, string leanPath)
    {
        const string Unusual = "X\U00010400\"\\n\b\r\n";

        void Elaborate(string module, string source, bool compile = false)
        {
            string path = Path.Combine(directory, module.Replace('.', '/') + ".lean");
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, source);
            string[] output = compile ? ["-o", Path.ChangeExtension(path, ".olean")] : [];
            Run(["lean", "--root", directory, .. output, path], directory, leanPath);
        }

        // The expected Lean string is constructed from decimal scalar values independently of all source escapers.
        static string Expected(string value) =>
            $"""(String.ofList ([{string.Join(",", value.EnumerateRunes().Select(r => r.Value))}].map Char.ofNat))""";

        internal void Callees()
        {
            string shortName = $"A::{Unusual}()";
            string longName = $"A::{Unusual}(Int32,  {new string('T', 96)})";
            string shortLiteral = ProofOutline.CalleeLiteral(shortName, 20);
            string wrapped = ProofOutline.CalleeLiteral(longName, 20);
            if (shortLiteral.Contains('\n') || !wrapped.Contains("\\\n", StringComparison.Ordinal))
                throw new InvalidOperationException("Expected both single-line and continued callee signatures.");
            Elaborate("Callees", $"""
                #guard {shortLiteral} == {Expected(shortName)}
                #guard {wrapped} == {Expected(longName)}
                """);
            Console.WriteLine("PASS short and wrapped loop callee signatures");
        }

        internal void Assumptions()
        {
            string assembly = Path.Combine(directory, "Assumptions.dll");
            string owner;
            string[] fields;
            using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
            {
                var type = module.GetType("Examples.SeededHash");
                type.Name += "\U00010400";
                owner = type.FullName;
                var seeds = type.Fields.Where(field => field.Name is "Seed0" or "Seed1").ToArray();
                foreach (var field in seeds) field.Name += "\b\U00010401";
                fields = seeds.Select(field => field.FullName).Order(StringComparer.Ordinal).ToArray();
                module.Write(assembly);
            }
            string extraction = Path.Combine(directory, "Assumptions");
            Run(["dotnet", ExtractorPath, "extract", assembly, $"{owner}::Hash(ulong)", extraction,
                "--assume-initialized", owner]);
            string[] names = ["initializedTypes", "staticValues", "opaqueStaticValues"];
            var definitions = File.ReadLines(Path.Combine(extraction, "Extracted.lean")).Where(line =>
                names.Any(name => line.StartsWith($"def Extracted.{name} :", StringComparison.Ordinal)));
            string expectedFields = string.Join(", ", fields.Select(Expected));
            Elaborate("Assumptions", $"""
                {string.Join('\n', definitions)}
                #guard Extracted.initializedTypes == [{Expected(owner)}]
                #guard Extracted.staticValues == [{expectedFields}]
                #guard Extracted.opaqueStaticValues == [{expectedFields}]
                """);
            Console.WriteLine("PASS initialized type and both static field declarations");
        }

        internal void SymbolValues()
        {
            using var pdb = ModuleDefinition.CreateModule("Symbols", ModuleKind.Dll);
            var method = new MethodDefinition("Read", MethodAttributes.Static, pdb.TypeSystem.Void);
            pdb.Types[0].Methods.Add(method);
            var instruction = Instruction.Create(OpCodes.Ret);
            method.Body.Instructions.Add(instruction);
            var local = new VariableDefinition(pdb.TypeSystem.Int32);
            method.Body.Variables.Add(local);
            var scope = new ScopeDebugInformation(instruction, null);
            scope.Variables.Add(new VariableDebugInformation(local, Unusual));
            method.DebugInformation.Scope = scope;
            const string document = "Source\U00010401\"\b.cs";
            method.DebugInformation.SequencePoints.Add(new SequencePoint(instruction, new Document($"src/{document}"))
                { StartLine = 2, StartColumn = 3 });
            string symbols = Symbols.Emit([method], "embedded");
            File.WriteAllText(Path.Combine(directory, "Symbols.lean"), symbols);
            File.WriteAllText(Path.Combine(directory, "identity.json"), """{"methods":[{"signature":"Read"}]}""");
            if (IdentityExtractor::VerifyReports.Methods(directory) is not [{ Points: [{ File: document, Pc: 0,
                    Line: 2, Column: 3 }] }])
                throw new InvalidOperationException("The reported sequence point differs from the PDB.");
            Elaborate("SymbolValues", $"""
                {symbols}
                #guard ExtractedSymbols.locals == [[(0, 0, 1, {Expected(Unusual)})]]
                #guard ExtractedSymbols.points == [[(0, {Expected(document)}, 2, 3)]]
                """);
            Console.WriteLine("PASS PDB local, relative source path and C# symbol report");
        }

        internal void Capture()
        {
            const string shared = "Shared\U0001D49C";
            Elaborate(shared, """
                /-- The root of the term capture belongs to the shared module. -/
                theorem LeanCILExportAudit.certified : True := True.intro
                #print axioms LeanCILExportAudit.certified
                """, compile: true);
            using var verifier = new Verification();
            string captured = verifier.CaptureFullTerms(directory, shared, "Transferred", [new(shared, "")], leanPath);
            if (!captured.Split('\n').Any(line => line == $"import {shared}"))
                throw new InvalidOperationException($"Captured terms lost their shared module: {captured}");
            Console.WriteLine("PASS shared module name and capture path");
        }

        internal void LakeArguments()
        {
            string lakefile = Path.Combine(directory, "lakefile.lean");
            File.WriteAllText(lakefile, "import Lake\nopen Lake DSL\npackage fixture\n");
            Verification.AddConsumerLibrary(directory, "Strings", [Unusual]);
            File.AppendAllText(lakefile, $"\n#guard Strings.config.moreLeanArgs == #[{Expected(Unusual)}]\n");
            Run(["lake", "env", "lean", "--version"], directory);
            Console.WriteLine("PASS lakefile Lean arguments");
        }

        internal void ImageIdentity()
        {
            var image = new BindingImagePin(Unusual, Sha256Digest.Of([]), []);
            Elaborate(image.Module, $$"""
                import StrictBinding.Image
                /-- The empty pinned file. -/
                def {{image.Module}}.image : StrictBinding.ImageBytes := { length := 0, pages := [] }
                """, compile: true);
            string images = ImagesModuleSource(new(directory, [image], 0));
            Elaborate("Images", $"""
                {images}
                #guard BindingAudit.images.map StrictBinding.PinnedImage.identity == [{Expected(Unusual)}]
                """);
            Console.WriteLine("PASS deep binding assembly identity including CRLF");
        }
    }
}
