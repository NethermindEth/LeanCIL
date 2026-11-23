#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs
#:include DeepBinding.cs

using System.Buffers.Binary;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text.Json;

using Program preparation = new();
preparation.EnsureExtractorBuilt();
MultiAssemblyFixture fixture = new("DeepCli");
var cli = args is [var executable] && !executable.StartsWith("--", StringComparison.Ordinal)
    ? new[] { Path.GetFullPath(executable) } : fixture.Cli;
if (args is ["--constraints"])
{
    CheckGenericConstraints();
    return;
}
if (args is ["--layouts"])
{
    CheckLayoutContent();
    return;
}
if (args is ["--dispatch"])
{
    CheckDispatchCatalogs();
    return;
}
if (args is ["--enums"])
{
    CheckEnumStorage();
    return;
}

const string libName = "DeepCli.Library";
var lib = fixture.Build("Library", libName,
    "namespace MultiFixture; public static class Mix { public static ulong Step(ulong x) => x * 3 + 1; }");
var app = fixture.Build("Application", "DeepCli.Application",
    "namespace MultiFixture; public static class Application { " +
        "public static ulong Direct(ulong x) => Mix.Step(x) + 1; }",
    references: $"<Reference Include=\"{libName}\"><HintPath>{lib}</HintPath></Reference>");
var output = fixture.Artifact("Direct");
Run([.. cli, "extract", app, "MultiFixture.Application::Direct(System.UInt64)", output, "--reference", lib]);
var proof = At("Tests/MultiAssembly/Direct.lean");
string[] verify = [.. cli, "verify", output, "--proof", proof, "--theorem", "MultiAssemblyProof.correctness"];
var digestFile = Path.Combine(fixture.Root, "inputs.sha256");
var digests = Sha(app) + "  " + Path.GetRelativePath(fixture.Root, app) + "\n" +
    Sha(lib) + "  " + Path.GetRelativePath(fixture.Root, lib) + "\n";
File.WriteAllText(digestFile, digests);

// Each fixture carries the actual platform identity and public key. A forwarded object has an
// ExportedType and an AssemblyRef. A defined object has one physical Field row.
static void WritePlatformImage(string path, AssemblyName name, FieldAttributes field, AssemblyName? forward = null,
    AssemblyName? pairForward = null, bool definePair = false, bool reverseSlots = false,
    bool definitionKeyFlag = true, bool mathInterface = false)
{
    var rows = new MetadataBuilder();
    rows.AddModule(0, rows.GetOrAddString(name.Name + ".dll"), rows.GetOrAddGuid(Guid.Empty), default, default);
    rows.AddAssembly(rows.GetOrAddString(name.Name!), name.Version!, default,
        rows.GetOrAddBlob(name.GetPublicKey()!), definitionKeyFlag ? AssemblyFlags.PublicKey : 0,
        AssemblyHashAlgorithm.Sha1);
    var firstField = MetadataTokens.FieldDefinitionHandle(1);
    var firstMethod = MetadataTokens.MethodDefinitionHandle(1);
    rows.AddTypeDefinition(default, default, rows.GetOrAddString("<Module>"), default, firstField, firstMethod);
    var system = rows.GetOrAddString("System");
    var objectName = rows.GetOrAddString("Object");
    if (forward is null)
    {
        rows.AddTypeDefinition(TypeAttributes.Public, system, objectName, default, firstField, firstMethod);
        var signature = new BlobBuilder();
        new BlobEncoder(signature).Field().Type().Int32();
        rows.AddFieldDefinition(field, rows.GetOrAddString("Value"), rows.GetOrAddBlob(signature));
    }
    else
    {
        var target = rows.AddAssemblyReference(rows.GetOrAddString(forward.Name!), forward.Version!, default,
            rows.GetOrAddBlob(forward.GetPublicKeyToken()!), default, default);
        const TypeAttributes forwarder = (TypeAttributes)0x00200000;
        rows.AddExportedType(forwarder, system, objectName, target, 0);
    }
    if (pairForward is not null)
    {
        var mathFlags = mathInterface ? TypeAttributes.Interface | TypeAttributes.Abstract :
            TypeAttributes.Abstract | TypeAttributes.Sealed;
        var mathBase = mathInterface ? default : MetadataTokens.TypeDefinitionHandle(2);
        rows.AddTypeDefinition(TypeAttributes.Public | mathFlags, system, rows.GetOrAddString("Math"), mathBase,
            MetadataTokens.FieldDefinitionHandle(rows.GetRowCount(TableIndex.Field) + 1), firstMethod);
        var target = rows.AddAssemblyReference(rows.GetOrAddString(pairForward.Name!), pairForward.Version!, default,
            rows.GetOrAddBlob(pairForward.GetPublicKeyToken()!), default, default);
        rows.AddExportedType((TypeAttributes)0x00200000, system, rows.GetOrAddString("ValueTuple`2"), target, 0);
    }
    if (definePair)
    {
        var start = MetadataTokens.FieldDefinitionHandle(rows.GetRowCount(TableIndex.Field) + 1);
        var valueType = rows.AddTypeDefinition(TypeAttributes.Public, system, rows.GetOrAddString("ValueType"),
            MetadataTokens.TypeDefinitionHandle(2), start, firstMethod);
        var pair = rows.AddTypeDefinition(TypeAttributes.Public | TypeAttributes.Sealed, system,
            rows.GetOrAddString("ValueTuple`2"), valueType, start, firstMethod);
        for (var slot = 0; slot < 2; slot++)
        {
            var signature = new BlobBuilder();
            new BlobEncoder(signature).Field().Type().GenericTypeParameter(reverseSlots ? 1 - slot : slot);
            rows.AddFieldDefinition(FieldAttributes.Public, rows.GetOrAddString("Item" + (slot + 1)),
                rows.GetOrAddBlob(signature));
            rows.AddGenericParameter(pair, default, rows.GetOrAddString("T" + (slot + 1)), slot);
        }
    }
    var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(),
        new MetadataRootBuilder(rows), new BlobBuilder());
    var bytes = new BlobBuilder();
    builder.Serialize(bytes);
    File.WriteAllBytes(path, bytes.ToArray());
}

void CheckPlatformObject()
{
    var runtime = Assembly.Load("System.Runtime").GetName();
    var core = typeof(object).Assembly.GetName();
    var reference = Path.Combine(fixture.Root, "reference-image.dll");
    var definition = Path.Combine(fixture.Root, "definition.dll");
    var previous = Path.Combine(fixture.Root, "previous-version.dll");

    void Check(string expected, params (string File, AssemblyName Name)[] platforms)
    {
        var extra = File.Exists(previous) ? Sha(previous) + "  " + Path.GetFileName(previous) + "\n" : "";
        File.WriteAllText(digestFile, digests + extra + string.Concat(platforms.Select(p =>
            Sha(p.File) + "  " + Path.GetFileName(p.File) + "\n")));
        var result = Execute([.. verify, "--deep-checks", digestFile, "--format", "json"]);
        if (expected == "failed")
        {
            if (result.Code == 0 || File.Exists(Path.Combine(output, "verified.json")))
                throw new InvalidOperationException("The changed platform definition was certified.");
            var failure = JsonSerializer.Deserialize<JsonElement>(result.Stdout).GetProperty("binding");
            var rejected = failure.GetProperty("facts").EnumerateArray()
                .Single(f => f.GetProperty("id").GetString() == "object-fields");
            if (rejected.GetProperty("status").GetString() != "failed" ||
                !rejected.GetProperty("reason").GetString()!.Contains("instance field 0x04000001", StringComparison.Ordinal))
                throw new InvalidOperationException("Expected the physical field diagnostic: " + result.Output);
            return;
        }
        if (result.Code != 0) throw new InvalidOperationException(result.Output);
        var binding = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")))
            .GetProperty("binding");
        var facts = binding.GetProperty("facts").EnumerateArray().ToArray();
        var keyFact = facts.Single(f => f.GetProperty("id").GetString() == "public-key-tokens");
        if (keyFact.GetProperty("status").GetString() != "reconfirmed" ||
            keyFact.GetProperty("theorem").GetString() != "BindingAudit.publicKeyTokens")
            throw new InvalidOperationException("Signed and unsigned AssemblyRefs were not checked: " + keyFact);
        var fact = facts.Single(f => f.GetProperty("id").GetString() == "object-fields");
        if (fact.GetProperty("status").GetString() != expected ||
            fact.GetProperty("theorem").GetString() != (expected == "reconfirmed" ? "BindingAudit.objectFields" : null))
            throw new InvalidOperationException("Incorrect object-fields certificate: " + fact);
        if (File.Exists(previous))
        {
            var unused = binding.GetProperty("images").EnumerateArray()
                .Single(i => i.GetProperty("sha256").GetString() == Sha(previous));
            if (unused.GetProperty("role").GetString() != "unused")
                throw new InvalidOperationException("The facade selected the wrong version: " + unused);
        }
        foreach (var (file, assembly) in platforms)
        {
            var image = binding.GetProperty("images").EnumerateArray()
                .Single(i => i.GetProperty("identity").GetString() == assembly.FullName);
            if (image.GetProperty("role").GetString() != "platform" ||
                image.GetProperty("sha256").GetString() != Sha(file) ||
                image.GetProperty("status").GetString() != "reconfirmed")
                throw new InvalidOperationException("Incorrect platform image: " + image);
        }
    }

    WritePlatformImage(reference, runtime, FieldAttributes.Static);
    Check("reconfirmed", (reference, runtime));
    Console.WriteLine("PASS the exact platform reference permits a static field on System.Object");
    WritePlatformImage(reference, runtime, default, core);
    var older = typeof(object).Assembly.GetName();
    older.Version = new Version(core.Version!.Major - 1, 0, 0, 0);
    WritePlatformImage(previous, older, FieldAttributes.Public);
    Check("not covered", (reference, runtime));
    Console.WriteLine("PASS a facade with only an older destination leaves System.Object fields uncovered");
    WritePlatformImage(definition, core, FieldAttributes.Static);
    Check("reconfirmed", (reference, runtime), (definition, core));
    Console.WriteLine("PASS the platform facade resolves System.Object in its exact destination");
    WritePlatformImage(definition, core, FieldAttributes.Public);
    Check("failed", (reference, runtime), (definition, core));
    Console.WriteLine("PASS a rehashed instance field in the forwarded definition fails the object-fields check");
    File.WriteAllText(digestFile, digests);
}

void CheckPlatformPair()
{
    var pairApp = fixture.Build("Pair", "DeepCli.Pair",
        "public static class Pair { public static int Quotient(int x, int y) => System.Math.DivRem(x, y).Quotient; }");
    var pairOutput = fixture.Artifact("PairExtraction");
    Run([.. cli, "extract", pairApp, "Pair::Quotient(int,int)", pairOutput]);
    var runtime = Assembly.Load("System.Runtime").GetName();
    var core = typeof(object).Assembly.GetName();
    var facade = Path.Combine(fixture.Root, "pair-facade.dll");
    var destination = Path.Combine(fixture.Root, "pair-definition.dll");
    var pairPins = Path.Combine(fixture.Root, "pair.sha256");
    var pairProof = At("Examples/Proofs/MathDivRemQuotient.lean");

    void Check(string expected, string[] images, bool wrongMathKind = false)
    {
        File.WriteAllLines(pairPins, images.Prepend(pairApp).Select(path => Sha(path) + "  " + path));
        var result = Execute([.. cli, "verify", pairOutput, "--proof", pairProof, "--deep-checks", pairPins,
            "--format", "json"]);
        var certificate = Path.Combine(pairOutput, "verified.json");
        if (expected == "failed" ? result.Code == 0 || File.Exists(certificate) : result.Code != 0)
            throw new InvalidOperationException("Unexpected pair verification outcome: " + result.Output);
        var report = expected == "failed"
            ? JsonSerializer.Deserialize<JsonElement>(result.Stdout)
            : JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(certificate));
        var facts = report.GetProperty("binding").GetProperty("facts").EnumerateArray().ToArray();
        var kind = facts.Single(f => f.GetProperty("id").GetString() == "platform-type-kinds");
        if (wrongMathKind)
        {
            if (kind.GetProperty("status").GetString() != "failed")
                throw new InvalidOperationException("Expected the physical System.Math kind rejection: " + kind);
            return;
        }
        if (expected != "failed" && (kind.GetProperty("status").GetString() != expected ||
            kind.GetProperty("theorem").GetString() != (expected == "reconfirmed" ? "BindingAudit.platformKinds" : null)))
            throw new InvalidOperationException("Wrong platform kind coverage: " + kind);
        var pair = facts.Single(f => f.GetProperty("id").GetString() == "value-tuple-field-order");
        if (pair.GetProperty("status").GetString() != expected ||
            expected == "reconfirmed" && pair.GetProperty("theorem").GetString() != "BindingAudit.tupleFields")
            throw new InvalidOperationException("Incorrect tuple field-order report: " + pair);
        var count = facts.Count(fact => fact.GetProperty("status").GetString() == "reconfirmed");
        var publicKeys = facts.Single(f => f.GetProperty("id").GetString() == "public-key-tokens");
        if (expected != "failed" && (publicKeys.GetProperty("status").GetString() != "reconfirmed" ||
            publicKeys.GetProperty("theorem").GetString() != "BindingAudit.publicKeyTokens"))
            throw new InvalidOperationException("Missing publisher token proof for the pair assembly: " + publicKeys);
        if (expected == "reconfirmed" && count != 7 || expected == "not covered" && count != 5)
            throw new InvalidOperationException($"Unexpected number of reconfirmed facts: {count} ({expected}).");
        if (expected == "failed" &&
            !pair.GetProperty("reason").GetString()!.Contains("Item1, signature 061301", StringComparison.Ordinal))
            throw new InvalidOperationException("Missing physical tuple signature in the rejection: " + pair);
        if (expected == "not covered" && report.GetProperty("binding").GetProperty("images").EnumerateArray()
                .Single(image => image.GetProperty("sha256").GetString() == Sha(destination))
                .GetProperty("role").GetString() != "unused")
            throw new InvalidOperationException("The tuple forwarder selected a different assembly version.");
        if (expected != "failed" && facts.Single(f => f.GetProperty("id").GetString() == "object-fields")
                .GetProperty("status").GetString() != "reconfirmed")
            throw new InvalidOperationException("The supplied facade defines System.Object.");
    }

    WritePlatformImage(facade, runtime, FieldAttributes.Static, pairForward: core);
    var previousCore = typeof(object).Assembly.GetName();
    previousCore.Version = new Version(core.Version!.Major - 1, 0, 0, 0);
    WritePlatformImage(destination, previousCore, FieldAttributes.Static, definePair: true);
    Check("not covered", [facade, destination]);
    WritePlatformImage(destination, core, FieldAttributes.Static, definePair: true, definitionKeyFlag: false);
    Check("reconfirmed", [facade, destination]);
    WritePlatformImage(destination, core, FieldAttributes.Static, definePair: true, reverseSlots: true);
    Check("failed", [facade, destination]);
    WritePlatformImage(destination, core, FieldAttributes.Static, definePair: true);
    WritePlatformImage(facade, runtime, FieldAttributes.Static, pairForward: core, mathInterface: true);
    Check("failed", [facade, destination], wrongMathKind: true);
    Console.WriteLine("PASS a rehashed System.Math interface fails the platform kind check");
    Console.WriteLine("PASS tuple forwarding, missing destination and swapped physical generic field signatures");
}

void CheckGenericConstraints()
{
    var assembly = fixture.Build("Constraints", "DeepCli.Constraints", """
        namespace Gates;
        public interface IClosed<T> { }
        public class Box<T> { }
        public struct Both : IClosed<int>, IClosed<long>, IClosed<Box<int>> { public int Value; }
        public struct Pair<S, T> : IClosed<T> where S : unmanaged where T : unmanaged
        {
            public S First;
            public T Second;
        }
        public static class Counter
        {
            public static int Read<T>(int n) where T : struct, IClosed<int> => n + 1;
            public static int ReadWide<T>(int n) where T : struct, IClosed<long> => n + 1;
            public static int Identity<T, U>(int n) where T : struct, IClosed<U> where U : unmanaged => n;
            public static int Nested<T, U>(int n) where T : struct, IClosed<Box<U>> where U : unmanaged => n;
            public static int Entry(int n) =>
                ReadWide<Pair<int, long>>(Read<Both>(Identity<Both, int>(Nested<Both, int>(n))));
        }
        """);
    var extracted = fixture.Artifact("GenericExtraction");
    Run([.. cli, "extract", assembly, "Gates.Counter::Entry(System.Int32)", extracted]);
    var pins = Path.Combine(fixture.Root, "constraints.sha256");
    File.WriteAllText(pins, Sha(assembly) + "  " + assembly + Environment.NewLine);
    var proof = Path.Combine(fixture.Root, "Constraints.lean");
    File.WriteAllText(proof, """
        import Extracted
        open CIL
        set_option maxRecDepth 16384 in
        theorem twice (value : W32) (memory : Safety.Memory) :
            Safety.invoke Extracted.program 32 0 [.scalar (.i32 value)] memory =
              .ok (memory, [.scalar (.i32 ((value + 1) + 1))]) := rfl
        #print axioms twice
        """);
    Run([.. cli, "verify", extracted, "--proof", proof, "--theorem", "twice",
        "--deep-checks", pins, "--format", "json"]);
    using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(extracted, "verified.json")));
    var fact = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
        .Single(item => item.GetProperty("id").GetString() == "generic-constraints");
    if (fact.GetProperty("status").GetString() != "reconfirmed" ||
        fact.GetProperty("theorem").GetString() != "BindingAudit.genericConstraints")
        throw new InvalidOperationException("Incorrect generic constraint report: " + fact);
    var layout = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
        .Single(item => item.GetProperty("id").GetString() == "layout-content");
    if (layout.GetProperty("status").GetString() != "not covered")
        throw new InvalidOperationException("Generic layouts incorrectly reconfirmed: " + layout);
}

void CheckDispatchCatalogs()
{
    foreach (bool changed in new[] { false, true })
    {
        var build = changed ? "FiveFaces" : "SixFaces";
        var assembly = fixture.Build(build, "DeepCli.Dispatch", $$"""
            namespace Geometry;
            public interface IShapeTag { int Tag(); int OtherTag(); }
            public interface IScale<T, U> { }
            public interface IColour { }
            public abstract class Shape { public abstract int Sides(); }
            public class Triangle : Shape, IShapeTag, IColour {
                public override int Sides() => 3;
                public int ReadScale(ref int scale) => scale;
                public T Load<T>(ref T value) => value;
                public static U Pick<T, U>(T first, U second)
                    where T : class, IScale<U, T>, new() where U : struct => second;
                int IShapeTag.Tag() => 1;
                int IShapeTag.OtherTag() => 2;
            }
            public static class Polygons { public sealed class Equilateral : Triangle { } }
            public abstract class Solid { public abstract int Faces(); }
            public sealed class Cube : Solid, IColour { public override int Faces() => {{(changed ? 5 : 6)}}; }
            public sealed class TagOnly : IShapeTag { public int Tag() => 1; public int OtherTag() => 2; }
            public sealed class UnrelatedResource : System.IDisposable { void System.IDisposable.Dispose() { } }
            public static class Reader {
                public static int Total(Shape shape, Solid solid) => shape.Sides() + solid.Faces() + shape.Sides();
                public static Triangle Select(Shape shape, bool strict) =>
                    strict ? ({{(changed ? "Polygons.Equilateral" : "Triangle")}})shape :
                        shape as {{(changed ? "Polygons.Equilateral" : "Triangle")}};
            }
            """);
        var pins = Path.Combine(fixture.Root, build + ".sha256");
        var output = fixture.Artifact(build + "Total");
        const string selector = "Geometry.Reader::Total(Geometry.Shape,Geometry.Solid)";
        var neighbour = changed ? null : fixture.Build("LocalParent", "DeepCli.Neighbour", """
            namespace Neighbours;
            public class LocalBase { }
            public sealed class LocalChild : LocalBase { }
            """);
        string[] images = neighbour is null ? [assembly] : [assembly, neighbour];
        File.WriteAllLines(pins, images.Select(path => Sha(path) + "  " + path));
        string[] references = neighbour is null ? [] : MultiAssemblyFixture.Reference(neighbour);
        Run([.. cli, "extract", assembly, selector, output, .. references]);
        var proof = Path.Combine(output, "Proof.lean");
        var template = File.ReadAllText(At("Tests/StrictBinding/DispatchTotal.lean.in"));
        var claim = changed ? "Refuted" : "Holds";
        var evidence = changed ? "refuted rfl" : "holds (by intro shape; cases shape <;> rfl)";
        File.WriteAllText(proof, template +
            $"\ntheorem correctness : contract.{claim} Extracted.program 0 := {evidence}\n" +
            "#print axioms correctness\nend DispatchGate\n");
        string[] binding = changed ? [] : ["--deep-checks", pins];
        Run([.. cli, "verify", output, "--proof", proof, "--theorem", "DispatchGate.correctness", .. binding]);
        CheckClassTests(assembly, build, changed);
        using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "verified.json")));
        if (changed)
        {
            var method = report.RootElement.GetProperty("refutation").GetProperty("method");
            if (method.GetProperty("assemblySha256").GetString() != Sha(assembly) ||
                !method.GetProperty("signature").GetString()!.Contains(selector, StringComparison.Ordinal))
                throw new InvalidOperationException("Wrong dispatch counterexample: " + method);
            continue;
        }
        var fact = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
            .Single(item => item.GetProperty("id").GetString() == "dispatch-catalogs");
        if (fact.GetProperty("status").GetString() != "reconfirmed" ||
            fact.GetProperty("theorem").GetString() != "BindingAudit.dispatchCatalogs")
            throw new InvalidOperationException("Incorrect dispatch binding report: " + fact);
        var derived = fixture.Build("ExternalParent", "DeepCli.Neighbour", """
            namespace Neighbours;
            public sealed class NewShape : Geometry.Shape { public override int Sides() => 7; }
            """, references: """<ProjectReference Include="../SixFaces/SixFaces.csproj" />""");
        fixture.RejectedExtract("foreign descendant", "Neighbours.NewShape overrides from another assembly",
            assembly, selector, MultiAssemblyFixture.Reference(derived));
        ReplayImageCases(output, assembly, "DispatchImage", At("Tests/StrictBinding/DispatchOverrideCases.lean"),
            ["StrictBinding.DispatchCatalogs", "Tests.StrictBinding.Mutation"],
            ("NeighbourImage", neighbour!), ("DerivedImage", derived));
        Console.WriteLine("PASS physical dispatch binds nested owners, byrefs and other pinned images");
    }
    CheckTwoAssemblyCatalogs();
}

void CheckTwoAssemblyCatalogs()
{
    var library = fixture.Build("LocalClassLibrary", "Classes.Library", """
        namespace Far;
        public class Shape { }
        public class Second : Shape {
            public static T Keep<T, U>(T value) where T : IScale<T, U> => value;
            public static string Label(ref string text, object tag) => text;
        }
        public static class Family { public sealed class Child : Second { } }
        public static class Reader { public static int Test(Shape value) => value is Second ? 2 : 0; }
        public interface IScale<T, U> { }
        public class Box<T> { }
        """);
    var app = fixture.Build("LocalClassApp", "Classes.App", """
        namespace Near;
        public class Shape { }
        public sealed class First : Shape {
            public static U Pick<T, U>(T first, U second)
                where T : class, Far.IScale<Far.Box<Far.IScale<U, int>>, Far.IScale<T, string>>, new() => second;
            public static object Tag(string text) => text;
        }
        public static class Reader {
            public static int Both(Shape local, Far.Shape other) => Far.Reader.Test(other) +
                (local is First ? 4 : 0) + (other is Far.Second ? 8 : 0) + (other is Far.Family.Child ? 16 : 0);
        }
        """, references: $"<Reference Include=\"Classes.Library\"><HintPath>{library}</HintPath></Reference>");
    const string selector = "Near.Reader::Both(Near.Shape,Far.Shape)";
    var changedLibrary = fixture.Artifact("ChangedClassLibrary");
    Directory.CreateDirectory(changedLibrary);
    var changed = Path.Combine(changedLibrary, Path.GetFileName(library));
    RetargetForeignClassTest(library, changed);
    var template = File.ReadAllText(At("Tests/StrictBinding/TwoClassTests.lean.in"));
    foreach (var image in new[] { library, changed })
    {
        var original = image == library;
        var output = fixture.Artifact(original ? "TwoAssemblyCatalogs" : "ChangedTwoAssemblyCatalogs");
        Run([.. cli, "extract", app, selector, output, .. MultiAssemblyFixture.Reference(image)]);
        var proof = Path.Combine(output, "Proof.lean");
        var claim = original ? "Holds" : "Refuted";
        var evidence = original
            ? "holds (by rintro ⟨localMatch, other⟩; cases localMatch <;> cases other <;> rfl)"
            : "refuted rfl";
        File.WriteAllText(proof, template +
            $"\ntheorem correctness : contract.{claim} Extracted.program 0 := {evidence}\n" +
            "#print axioms correctness\nend BothCatalogs\n");
        var pins = Path.Combine(output, "inputs.sha256");
        File.WriteAllLines(pins, new[] { app, image }.Select(path => Sha(path) + "  " + path));
        string[] binding = original ? ["--deep-checks", pins] : [];
        Run([.. cli, "verify", output, "--proof", proof, "--theorem", "BothCatalogs.correctness", .. binding]);
        using var receipt = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "verified.json")));
        if (!original)
        {
            var method = receipt.RootElement.GetProperty("refutation").GetProperty("method");
            if (method.GetProperty("assemblySha256").GetString() != Sha(app) ||
                method.GetProperty("signature").GetString() != "System.Int32 " + selector)
                throw new InvalidOperationException("Unexpected two-assembly refutation: " + method);
            continue;
        }
        var fact = receipt.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
            .Single(item => item.GetProperty("id").GetString() == "dispatch-catalogs");
        if (fact.GetProperty("status").GetString() != "reconfirmed" ||
            fact.GetProperty("theorem").GetString() != "BindingAudit.dispatchCatalogs")
            throw new InvalidOperationException("Expected both methods' physical class catalogs: " + fact);
        ReplayImageCases(output, app, "AppImage", At("Tests/StrictBinding/TwoCatalogCases.lean"),
            ["StrictBinding.DispatchCatalogs", "Tests.StrictBinding.Mutation"], ("LibImage", library));
    }
    Console.WriteLine("PASS changing the foreign class token refutes the unchanged caller's return contract");
}

// The fixture's tiny method begins with ldarg.0 and isinst Far.Second. Change just its TypeDef token.
static void RetargetForeignClassTest(string source, string destination)
{
    var bytes = File.ReadAllBytes(source);
    using var pe = new PEReader(new MemoryStream(bytes));
    var metadata = pe.GetMetadataReader();
    TypeDefinitionHandle FarType(string name) => metadata.TypeDefinitions.Single(handle =>
    {
        var type = metadata.GetTypeDefinition(handle);
        return metadata.StringComparer.Equals(type.Namespace, "Far") && metadata.StringComparer.Equals(type.Name, name);
    });
    var reader = metadata.GetTypeDefinition(FarType("Reader"));
    var method = reader.GetMethods().Select(metadata.GetMethodDefinition)
        .Single(definition => metadata.StringComparer.Equals(definition.Name, "Test"));
    var body = pe.GetMethodBody(method.RelativeVirtualAddress);
    if (!pe.PEHeaders.TryGetDirectoryOffset(new DirectoryEntry(method.RelativeVirtualAddress, body.Size), out var start)
        || (bytes[start] & 3) != 2 || bytes[start + 1] != 0x02 || bytes[start + 2] != 0x75)
        throw new InvalidDataException("Expected the tiny Far.Reader.Test body to start with ldarg.0; isinst.");
    var operand = bytes.AsSpan(start + 3, sizeof(int));
    if (BinaryPrimitives.ReadInt32LittleEndian(operand) != MetadataTokens.GetToken(FarType("Second")))
        throw new InvalidDataException("Expected isinst Far.Second.");
    BinaryPrimitives.WriteInt32LittleEndian(operand, MetadataTokens.GetToken(FarType("Shape")));
    File.WriteAllBytes(destination, bytes);
}

void CheckClassTests(string assembly, string build, bool changed)
{
    const string selector = "Geometry.Reader::Select(Geometry.Shape,System.Boolean)";
    var output = fixture.Artifact(build + "Select");
    Run([.. cli, "extract", assembly, selector, output]);
    var proof = Path.Combine(output, "Proof.lean");
    var template = File.ReadAllText(At("Tests/StrictBinding/ClassTest.lean.in"));
    var claim = changed ? "Refuted" : "Holds";
    var evidence = changed ? "refuted rfl" :
        "holds (by rintro ⟨present, strict⟩; cases present <;> cases strict <;> rfl)";
    var strictCast = changed
        ? "\ntheorem strictCast : contract.Refuted Extracted.program 0 := refutedCast rfl\n#print axioms strictCast\n"
        : "";
    File.WriteAllText(proof, template + strictCast +
        $"\ntheorem correctness : contract.{claim} Extracted.program 0 := {evidence}\n" +
        "#print axioms correctness\nend ClassTest\n");
    var pins = Path.Combine(output, "inputs.sha256");
    File.WriteAllText(pins, Sha(assembly) + "  " + assembly + "\n");
    string[] binding = changed ? [] : ["--deep-checks", pins];
    Run([.. cli, "verify", output, "--proof", proof, "--theorem", "ClassTest.correctness", .. binding]);
    using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (changed)
    {
        var method = report.RootElement.GetProperty("refutation").GetProperty("method");
        if (method.GetProperty("assemblySha256").GetString() != Sha(assembly) ||
            !method.GetProperty("signature").GetString()!.Contains(selector, StringComparison.Ordinal))
            throw new InvalidOperationException("Unexpected class-test counterexample: " + method);
        return;
    }
    var fact = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
        .Single(item => item.GetProperty("id").GetString() == "dispatch-catalogs");
    if (fact.GetProperty("status").GetString() != "reconfirmed" ||
        fact.GetProperty("theorem").GetString() != "BindingAudit.dispatchCatalogs")
        throw new InvalidOperationException("Incorrect class-test binding: " + fact);
    ReplayImageCases(output, assembly, "TypeTestImage", At("Tests/StrictBinding/ClassTestCases.lean"),
        ["StrictBinding.DispatchCatalogs", "Tests.StrictBinding.Mutation"]);
}

void CheckLayoutContent()
{
    var assemblies = new List<string>();
    foreach (bool changed in new[] { false, true })
    {
        var build = changed ? "RelocatedFields" : "OriginalFields";
        var assembly = fixture.Build(build, "DeepCli.Layouts", $$"""
            using System.Runtime.InteropServices;
            namespace Gates;
            [StructLayout(LayoutKind.Explicit, Pack = 2, Size = 24)]
            public struct Overlay {
                [FieldOffset(0)] public uint Tag;
                [FieldOffset({{(changed ? 4 : 8)}})] public int Value;
                [FieldOffset(16)] public long Stamp;
                public static int Outside;
            }
            [StructLayout(LayoutKind.Sequential, Pack = {{(changed ? 8 : 1)}})]
            public struct Packed { public short Flag; public uint Count; }
            public static class Reader {
                public static int Read(ref Overlay row) => row.Value;
                public static uint ReadPacked(ref Packed row) => row.Count;
            }
            """);
        assemblies.Add(assembly);
        var pins = Path.Combine(fixture.Root, build + ".sha256");
        File.WriteAllText(pins, Sha(assembly) + "  " + assembly + Environment.NewLine);
        foreach (var (method, type, offset) in new[] { ("Read", "Overlay", "8"), ("ReadPacked", "Packed", "2") })
        {
            var output = fixture.Artifact(build + method);
            Run([.. cli, "extract", assembly, $"Gates.Reader::{method}(Gates.{type}&)", output]);
            var proof = Path.Combine(output, "Proof.lean");
            var (claim, lemma, evidence) = changed
                ? ("Refuted", "refuted", "readAtOffset (Extracted.fieldRef0_shape rfl) witness")
                : ("Holds", "holds", "readAtOffset (Extracted.fieldRef0_shape rfl)");
            var template = File.ReadAllText(At("Tests/StrictBinding/LayoutRead.lean.in"));
            File.WriteAllText(proof, template.Replace("FIELD_OFFSET", offset, StringComparison.Ordinal)
                .Replace("READ_OFFSET", changed ? "4" : offset, StringComparison.Ordinal) +
                $"\ntheorem correctness : contract.{claim} Extracted.program 0 := {lemma} ({evidence})\n" +
                "#print axioms correctness\nend LayoutGate\n");
            string[] binding = changed ? [] : ["--deep-checks", pins];
            Run([.. cli, "verify", output, "--proof", proof, "--theorem", "LayoutGate.correctness", .. binding]);
            using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "verified.json")));
            if (changed)
            {
                var counter = report.RootElement.GetProperty("refutation").GetProperty("method");
                var signature = counter.GetProperty("signature").GetString()!;
                if (counter.GetProperty("assemblySha256").GetString() != Sha(assembly) ||
                    !signature.Contains("::" + method + "(", StringComparison.Ordinal))
                    throw new InvalidOperationException("Wrong layout counterexample: " + counter);
                continue;
            }
            var fact = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
                .Single(item => item.GetProperty("id").GetString() == "layout-content");
            if (fact.GetProperty("status").GetString() != "reconfirmed" ||
                fact.GetProperty("theorem").GetString() != "BindingAudit.layoutContent")
                throw new InvalidOperationException("Incorrect layout binding report: " + fact);
        }
    }
    // Both assemblies contain the same ReadPacked instructions. The changed packing moves Count.
    var manifest = Path.Combine(fixture.Root, "layout-gates.json");
    var results = Path.Combine(fixture.Root, "layout-results.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, proofRoot = fixture.Artifact("OriginalFieldsReadPacked"), outputRoot = "layout-gates",
        gates = new[] { new
        {
            name = "packed", method = "Gates.Reader::ReadPacked(Gates.Packed&)", profiles = new[] { "scalar" },
            assembly = assemblies[0], proof = "Proof.lean", theorem = "LayoutGate.correctness",
            variants = new[]
            {
                new { name = "identical", assembly = assemblies[0], expect = "unchanged", program = "same" },
                new { name = "moved", assembly = assemblies[1], expect = "unchanged", program = "different" },
                new { name = "claimed-same", assembly = assemblies[1], expect = "unchanged", program = "same" }
            }
        } }
    }));
    var compared = Execute([.. cli, "gates", manifest, "--only", "packed/scalar/identical",
        "--only", "packed/scalar/moved", "--only", "packed/scalar/claimed-same", "--results", results]);
    if (compared.Code != 1) throw new InvalidOperationException(compared.Output);
    using var receipt = JsonDocument.Parse(File.ReadAllText(results));
    var rows = receipt.RootElement.GetProperty("rows").EnumerateArray().ToDictionary(row =>
        row.GetProperty("variant").GetString()!);
    if (rows["identical"].GetProperty("status").GetString() != "unchanged" ||
        rows["moved"].GetProperty("status").GetString() != "unchanged" ||
        rows["claimed-same"].GetProperty("status").GetString() != "failed" ||
        rows["claimed-same"].GetProperty("stage").GetString() != "program comparison" ||
        !rows["claimed-same"].GetProperty("error").GetString()!.Contains("but it is different.", StringComparison.Ordinal))
        throw new InvalidOperationException(compared.Output);
    Console.WriteLine("PASS unchanged ReadPacked IL with a relocated field compares as a different program");
}

void CheckEnumStorage()
{
    var assembly = fixture.Build("Enums", "DeepCli.Enums", """
        namespace EnumFixture;
        public enum Flags : ulong { One = 1 }
        public static class Operations
        {
            public static Flags Set(Flags input) => input | Flags.One;
        }
        """);
    var extracted = fixture.Artifact("EnumExtraction");
    Run([.. cli, "extract", assembly, "EnumFixture.Operations::Set(EnumFixture.Flags)", extracted]);
    var pins = Path.Combine(fixture.Root, "enum.sha256");
    File.WriteAllText(pins, Sha(assembly) + "  " + assembly + Environment.NewLine);
    var verified = Execute([.. cli, "verify", extracted, "--proof", At("Examples/Proofs/EnumFlags.lean"),
        "--theorem", "ExampleProof.correctness", "--deep-checks", pins, "--format", "json"]);
    if (verified.Code != 0) throw new InvalidOperationException(verified.Output);
    using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(extracted, "verified.json")));
    var fact = report.RootElement.GetProperty("binding").GetProperty("facts").EnumerateArray()
        .Single(item => item.GetProperty("id").GetString() == "enum-underlying-types");
    if (fact.GetProperty("status").GetString() != "reconfirmed" ||
        fact.GetProperty("theorem").GetString() != "BindingAudit.enumStorage")
        throw new InvalidOperationException("Incorrect enum storage report: " + fact);
}

void CheckPublisherKey()
{
    var identity = JsonSerializer.SerializeToElement(new
    {
        assemblySha256 = Sha(app),
        assemblyIdentity = AssemblyName.GetAssemblyName(app).FullName
    });
    var inputs = DeepCheckInputs.Read(digestFile);
    var planned = inputs.MatchPins(identity);
    if (planned.Count != 2 || planned[0].KeyCoverage != false || !planned[1].Reference ||
        planned[1].Platform || planned[1].Identity != AssemblyName.GetAssemblyName(lib).FullName)
        throw new InvalidOperationException("The digest-listed library did not match the unpinned AssemblyRef.");

    var unusedReference = fixture.Build("ReferenceProbe", libName,
        "namespace MultiFixture; public static class Mix { public static ulong Step(ulong x) => x * 3 + 1; " +
        "public static void Print() => System.Console.WriteLine(); }");
    var bytes = File.ReadAllBytes(unusedReference);
    using (var pe = new PEReader(new MemoryStream(bytes, writable: false)))
    {
        var metadata = pe.GetMetadataReader();
        var handle = metadata.AssemblyReferences.Single(h =>
            metadata.StringComparer.Equals(metadata.GetAssemblyReference(h).Name, "System.Console"));
        var signature = metadata.GetMethodDefinition(metadata.MethodDefinitions.First()).Signature;
        var width = metadata.GetBlobReader(signature).Length;
        if (width is 0 or 8 || metadata.GetHeapSize(HeapIndex.Blob) >= 65536)
            throw new InvalidOperationException("Expected a short non-token signature and two-byte blob indices.");
        // AssemblyRef.PublicKeyOrToken follows the four version components and the flags.
        var row = metadata.GetTableMetadataOffset(TableIndex.AssemblyRef) +
            (MetadataTokens.GetRowNumber(handle) - 1) * metadata.GetTableRowSize(TableIndex.AssemblyRef);
        System.Buffers.Binary.BinaryPrimitives.WriteUInt16LittleEndian(
            bytes.AsSpan(pe.PEHeaders.MetadataStartOffset + row + 12),
            checked((ushort)MetadataTokens.GetHeapOffset(signature)));
    }
    var changed = Path.Combine(fixture.Root, "short-token.dll");
    File.WriteAllBytes(changed, bytes);
    var extraction = fixture.Artifact("ShortToken");
    Run([.. cli, "extract", app, "MultiFixture.Application::Direct(System.UInt64)", extraction,
        "--reference", changed]);
    var digestPath = Path.Combine(fixture.Root, "short-token.sha256");
    File.WriteAllText(digestPath, $"{Sha(app)}  {Path.GetRelativePath(fixture.Root, app)}\n" +
        $"{Sha(changed)}  {Path.GetFileName(changed)}\n");
    var result = Execute([.. cli, "verify", extraction, "--proof", proof, "--theorem",
        "MultiAssemblyProof.correctness", "--deep-checks", digestPath, "--format", "json"]);
    if (result.Code == 0 || File.Exists(Path.Combine(extraction, "verified.json")))
        throw new InvalidOperationException("A malformed token in a supplied assembly was certified.");
    var failure = JsonSerializer.Deserialize<JsonElement>(result.Stdout).GetProperty("binding");
    var rejected = failure.GetProperty("facts").EnumerateArray()
        .Single(fact => fact.GetProperty("id").GetString() == "public-key-tokens");
    if (rejected.GetProperty("status").GetString() != "failed" ||
        !rejected.GetProperty("reason").GetString()!.Contains("AssemblyRef System.Console", StringComparison.Ordinal))
        throw new InvalidOperationException("Missing publisher-key rejection: " + result.Output);
    Console.WriteLine("PASS an invalid AssemblyRef token outside the method slice fails with partial reference inputs");
}

if (args is ["--keys"])
{
    CheckPublisherKey();
    return;
}

if (args is ["--pair"])
{
    CheckPlatformPair();
    return;
}

if (args is ["--platform"])
{
    CheckPlatformObject();
    return;
}

void Refused(string name, string[] command, string? expectedStage = null)
{
    var result = Execute(command);
    if (result.Code == 0) throw new InvalidOperationException(name + " was accepted");
    if (expectedStage is not null)
    {
        var report = JsonSerializer.Deserialize<JsonElement>(result.Stdout);
        if (report.GetProperty("stage").GetString() != expectedStage ||
            report.GetProperty("binding").ValueKind != JsonValueKind.Null)
            throw new InvalidOperationException(name + " has the wrong failure boundary: " + result.Output);
    }
    Console.WriteLine("PASS " + name);
}

// The deep checks run only as an option of verify, so a command name that is not one of the listed commands
// is a usage error that runs nothing, whatever it is called.
void RefusedAsUnknownCommand(string[] cli, string output, string digestFile)
{
    foreach (var name in new[] { "audit" + "-binding", "audit", "binding-audit", "strict-binding", "deep-checks",
                 "deep", "verify-deep", "audit-deep" })
    {
        var result = Execute([.. cli, name, output, "--deep-checks", digestFile]);
        if (result.Code == 0 || !result.Output.Contains("Stage: arguments", StringComparison.Ordinal) ||
            !result.Output.Contains("Usage: leancil", StringComparison.Ordinal) ||
            result.Output.Contains("Binding:", StringComparison.Ordinal) ||
            result.Output.Contains("BindingAudit", StringComparison.Ordinal) ||
            result.Output.Contains("StrictBinding", StringComparison.Ordinal))
            throw new InvalidOperationException(name + " was not refused as an unknown command: " + result.Output);
    }
    Console.WriteLine("PASS unknown audit command names");
}

// The help text lists the deep checks only as an option of verify. The one audit command, audit-library, checks
// the theorems of a Lean library and runs no binding check.
void RequireNoSeparateAudit(string[] cli)
{
    var help = Execute([.. cli, "--help"]);
    // A command's usage wraps onto indented lines that do not start with `leancil`; each belongs to the command above.
    var commands = help.Stdout.ReplaceLineEndings("\n").Split('\n')
        .Aggregate(new List<string>(), (joined, raw) =>
        {
            var line = raw.Trim().StartsWith("Usage: ", StringComparison.Ordinal) ? raw.Trim()["Usage: ".Length..]
                : raw.Trim();
            if (line.StartsWith("leancil ", StringComparison.Ordinal)) joined.Add(line);
            else if (line.Length > 0 && raw.StartsWith(' ') && joined.Count > 0) joined[^1] = $"{joined[^1]} {line}";
            return joined;
        }).ToArray();
    var names = commands.Select(line => line.Split(' ')[1])
        .Where(name => !name.StartsWith("--", StringComparison.Ordinal)).ToArray();
    var audits = names.Where(name => name.Contains("audit", StringComparison.OrdinalIgnoreCase)).ToArray();
    var deepLines = commands.Where(line => line.Contains("--deep-checks", StringComparison.Ordinal)).ToArray();
    if (help.Code != 0 || !names.Contains("verify") || !audits.SequenceEqual(["audit-library"]) ||
        deepLines.Length != 1 || !deepLines[0].StartsWith("leancil verify ", StringComparison.Ordinal) ||
        help.Stdout.Contains("binding audit", StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException("The help text names a separate audit entry: " + help.Output);
    Console.WriteLine("PASS help names no separate audit command");
}

if (args is not (["--consumer"] or ["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    Refused("missing digest option value", [.. verify, "--format", "json", "--deep-checks"], "arguments");
    Refused("duplicate digest option", [.. verify, "--format", "json", "--deep-checks", digestFile,
        "--deep-checks", digestFile], "arguments");
    Refused("missing digest file", [.. verify, "--deep-checks", digestFile + ".missing", "--format", "json"],
        "arguments");
    foreach (var content in new[] { "malformed\n", new string('0', 64) + "  " + app + "\n",
        Sha(app) + "  " + app + "\n" })
    {
        File.WriteAllText(digestFile, content);
        Refused("invalid or missing image digest", [.. verify, "--deep-checks", digestFile, "--format", "json"],
            "arguments");
    }
    File.WriteAllBytes(digestFile, [0xff]);
    Refused("invalid UTF-8 digest file", [.. verify, "--deep-checks", digestFile, "--format", "json"], "arguments");
    File.WriteAllText(digestFile, digests);
    foreach (var command in new[] { "verify-batch", "gates", "watch", "workspace", "check", "audit-library" })
        Refused(command + " rejects deep option", [.. cli, command, output, "--deep-checks", digestFile]);
    RefusedAsUnknownCommand(cli, output, digestFile);
    RequireNoSeparateAudit(cli);
    Refused("invalid proof root", [.. verify, "--proof-root", fixture.Root + ".missing", "--deep-checks",
        digestFile, "--format", "json"], "extraction integrity");
    File.Delete(Path.Combine(output, "verification.json"));
    if (args is ["--arguments"]) return;

    var ordinary = Execute(verify);
    if (ordinary.Code != 0 || !ordinary.Stdout.Contains("Binding: default", StringComparison.Ordinal) ||
        ordinary.Stdout.Split(": trusted", StringSplitOptions.None).Length != 13 ||
        ordinary.Output.Contains("BindingAudit", StringComparison.Ordinal))
        throw new InvalidOperationException("Default binding output or work changed: " + ordinary.Output);
    var deep = Execute([.. verify, "--deep-checks", digestFile]);
    string[] reconfirmed = ["body-bytes", "metadata-rows", "static-data"];
    if (deep.Code != 0 || !deep.Stdout.Contains("StrictBinding sources:", StringComparison.Ordinal) ||
        deep.Stdout.Split(": not covered", StringSplitOptions.None).Length != 10)
        throw new InvalidOperationException("Deep binding text is incomplete: " + deep.Output);
    string[] factNames =
    [
        "body-bytes", "metadata-rows", "platform-type-kinds", "enum-underlying-types", "value-tuple-field-order",
        "object-fields", "layout-content", "dispatch-catalogs", "static-data", "generic-constraints",
        "public-key-tokens", "import-identities"
    ];
    foreach (var fact in factNames)
        if (!ordinary.Stdout.Contains(fact + ": trusted", StringComparison.Ordinal) ||
            !deep.Stdout.Contains(fact + (reconfirmed.Contains(fact) ? ": reconfirmed" : ": not covered"),
                StringComparison.Ordinal))
            throw new InvalidOperationException("Binding text omitted wire name " + fact);
    Console.WriteLine("PASS default and deep binding text");
    CheckPlatformObject();
    CheckPlatformPair();
    CheckPublisherKey();
    CheckEnumStorage();
    CheckGenericConstraints();
    CheckLayoutContent();
    CheckDispatchCatalogs();

    var tables = fixture.Build("Table", "DeepCli.Table", """
        public static class Table {
            static System.ReadOnlySpan<uint> Words => [11, 13, 17, 19, 23, 29, 31, 37];
            public static uint Third() => Words[2];
        }
        """);
    var tableOutput = fixture.Artifact("Third");
    Run([.. cli, "extract", tables, "Table::Third()", tableOutput]);
    var tableDigest = Path.Combine(fixture.Root, "table.sha256");
    File.WriteAllText(tableDigest, Sha(tables) + "  " + Path.GetRelativePath(fixture.Root, tables) + "\n");
    var tableProof = Path.Combine(fixture.Root, "Third.lean");
    File.WriteAllText(tableProof, """
        import Extracted
        import CIL.Safety.Execution

        open CIL CIL.Safety
        namespace ExampleProof

        example : Extracted.methodEvidence.any (fun item => item.closed.staticFields.any
            (fun site => site.2.rvaSize == some 32)) = true := by decide +kernel

        theorem correctness : (invoke Extracted.program 64 0 [] Memory.empty).map Prod.snd =
            .ok [.scalar (.i32 17)] := by rfl
        #print axioms correctness
        end ExampleProof

        """);
    Run([.. cli, "verify", tableOutput, "--proof", tableProof, "--deep-checks", tableDigest]);
    var binding = JsonSerializer.Deserialize<JsonElement>(
        File.ReadAllText(Path.Combine(tableOutput, "verified.json"))).GetProperty("binding");
    var data = binding.GetProperty("facts").EnumerateArray().Single(fact =>
        fact.GetProperty("id").GetString() == "static-data");
    if (data.GetProperty("status").GetString() != "reconfirmed" ||
        data.GetProperty("theorem").GetString() != "BindingAudit.staticData")
        throw new InvalidOperationException("The compiled table has no audited physical-data theorem.");
    Console.WriteLine("PASS the third word comes from a 32-byte RVA field in the pinned table assembly");

    ReplayImageCases(tableOutput, tables, "RvaImage", At("Tests/StrictBinding/StaticSiteCases.lean"),
        ["StrictBinding.StaticData"]);
    Console.WriteLine("PASS the pinned FieldRVA rejects a matching prefix, changed bytes and a missing RVA marker");
}

void ReplayImageCases(string directory, string assembly, string imageModule, string casesFile, string[] dependencies,
    params (string Module, string Assembly)[] otherImages)
{
    Run(["lake", "build", .. dependencies], preparation.CheckoutPackage());
    var leanPath = directory + Path.PathSeparator + preparation.CheckoutLeanPath();
    (string Module, string Assembly)[] images = [(imageModule, assembly), .. otherImages];
    foreach (var (module, path) in images)
        File.WriteAllText(Path.Combine(directory, module + ".lean"),
            $"import StrictBinding.Image\nimport CIL.Extraction.FixedDigits\nnamespace {module}\n" +
            BindingImage.Definitions(File.ReadAllBytes(path)) + $"\nend {module}\n");
    var cases = Path.GetFileNameWithoutExtension(casesFile);
    File.Copy(casesFile, Path.Combine(directory, cases + ".lean"), true);
    string[] modules = ["Extracted", .. images.Select(image => image.Module), cases];
    foreach (var module in modules)
    {
        var log = Run([preparation.LeanExecutable, "--root=" + directory, "-o",
            Path.Combine(directory, module + ".olean"), Path.Combine(directory, module + ".lean")],
            leanPath: leanPath);
        if (log.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidDataException(module + " depends on sorryAx");
    }
    preparation.ReplayCheckedModules(modules, leanPath, "Kernel replay of " + cases);
}
if (args is ["--text"]) return;
if (args is ["--mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify);
if (args is ["--controls"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, controlsOnly: true);
if (args is ["--final-mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, finalOnly: true);
if (args is not (["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    var package = Path.Combine(fixture.Root, "Consumer");
    Directory.CreateDirectory(package);
    var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
    File.WriteAllText(Path.Combine(package, "lakefile.toml"), $"""
        name = "deep_cli_consumer"
        [[require]]
        name = "leancil"
        git = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}
        rev = "{revision}"
        """);
    File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
    var consumerProof = Path.Combine(package, "Proof.lean");
    File.Copy(proof, consumerProof);
    Run(["lake", "update"], package);
    string[] consumer = [.. cli, "verify", output, "--proof", consumerProof, "--theorem",
        "MultiAssemblyProof.correctness", "--proof-root", package, "--deep-checks", digestFile, "--format", "json"];
    var checkedConsumer = Execute(consumer);
    if (checkedConsumer.Code != 0) throw new InvalidOperationException(checkedConsumer.Output);
    var consumerReport = JsonSerializer.Deserialize<JsonElement>(checkedConsumer.Stdout);
    var binding = consumerReport.GetProperty("binding");
    if (binding.GetProperty("mode").GetString() != "deep" ||
        binding.GetProperty("facts").GetArrayLength() != 12 ||
        binding.GetProperty("facts")[0].GetProperty("status").GetString() != "reconfirmed")
        throw new InvalidOperationException("Consumer CLI did not retain deep binding");
    Console.WriteLine("PASS proof-root CLI deep verification");
    File.WriteAllText(consumerProof,
        "import Extracted\nnamespace MultiAssemblyProof\ntheorem correctness : False := by exact True.intro\n" +
        "end MultiAssemblyProof\n");
    var rejected = Execute(consumer);
    if (rejected.Code == 0 || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Rejected consumer proof published a certificate");
    var failed = JsonSerializer.Deserialize<JsonElement>(rejected.Stdout);
    var failedFile = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "failed.json")));
    var failureBinding = failed.GetProperty("binding");
    if (!JsonElement.DeepEquals(failureBinding, failedFile.GetProperty("binding")) ||
        failureBinding.GetProperty("facts").GetArrayLength() != 12 ||
        failureBinding.GetProperty("facts").EnumerateArray().Any(fact =>
            fact.GetProperty("status").GetString() != "not covered"))
        throw new InvalidOperationException("Failed consumer binding payload is inconsistent: " + rejected.Output);
    Console.WriteLine("PASS failed.json and JSON retain the same incomplete deep attempt");
}
