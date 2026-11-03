#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;
using Mono.Cecil;

// Generic structs and static methods of generic classes across an SDK-built Lib and App pair.
string root = At("artifacts/MultiAssemblyGenerics-" + Guid.NewGuid().ToString("N"));
string[] cli = ["dotnet", ExtractorPath];
const string libName = "GenericFixture.Lib";
const string appName = "GenericFixture.App";
const string unsigned = ", Version=0.1.0.0, Culture=neutral, PublicKeyToken=null";
const string libraryText = """
using System.Runtime.CompilerServices;
namespace GenericFixture;
public struct Cell { public ulong Value; }
public struct Pair<T> where T : unmanaged { public T A; public T B; }
public struct Holder<T> where T : unmanaged { public T Item; public object? Reference; }
public static class PairOps
{
    public static ulong Sum(ref Pair<ulong> pair) => pair.A + pair.B;
    public static T First<T>(T value) where T : unmanaged => value;
    public static ulong Size<T>(ulong x) where T : unmanaged => x + (ulong)Unsafe.SizeOf<T>();
}
public struct Box<T> where T : unmanaged
{
    public T Item;
    public ulong Tag;
    public static ulong Twice(ulong x) => x * 2;
    public ulong Get() => Tag + 1;
}
public static class Algo<T> where T : unmanaged
{
    public static ulong Run(ulong x) => x * 3 + (ulong)Unsafe.SizeOf<T>();
}
public static class Outer<T> where T : unmanaged
{
    public static class Helper { public static ulong Run(ulong x) => x + (ulong)Unsafe.SizeOf<T>(); }
}
""";
const string applicationText = """
using System.Runtime.CompilerServices;
namespace GenericFixture;
public struct Wrapper<T> where T : unmanaged { public T Inner; public ulong Tag; }
public struct Mine { public uint Value; }
public struct Loop { public Pair<ulong> Pair; }
public static class LocalAlgo<T> where T : unmanaged
{
    public static ulong Counter;
    public static ulong Run(ulong x) => x + (ulong)Unsafe.SizeOf<T>();
    public static ulong Load(ulong x) => x + Counter;
}
public static class Seeded<T> where T : unmanaged
{
    static Seeded() { System.GC.KeepAlive(new object()); }
    public static ulong Get(ulong x) => x;
}
public class Instance<T> where T : unmanaged { public ulong Get(ulong x) => x; }
public static class Free<T> { public static ulong Self(ulong x) => x; }
public static class Application
{
    public static ulong PairLocal(ulong x)
    { Pair<ulong> pair = default; pair.A = x; pair.B = 2; return pair.A + pair.B; }
    public static ulong PairByRef(ulong x)
    { Pair<ulong> pair = default; pair.A = x; pair.B = 2; return Sum(ref pair); }
    static ulong Sum(ref Pair<ulong> pair) => pair.A + pair.B;
    public static ulong PairLib(ulong x)
    { Pair<ulong> pair = default; pair.A = x; pair.B = 1; return PairOps.Sum(ref pair); }
    public static ulong PairArgument(ulong x) => SizeOf<Pair<uint>>(x);
    static ulong SizeOf<T>(ulong x) where T : unmanaged => x + (ulong)Unsafe.SizeOf<T>();
    public static ulong WrapLocal(ulong x)
    { Wrapper<Cell> w = default; w.Inner.Value = x; w.Tag = 1; return w.Inner.Value + w.Tag; }
    public static ulong WrapByRef(ulong x) { Wrapper<Cell> w = default; w.Inner.Value = x; return Read(ref w); }
    static ulong Read(ref Wrapper<Cell> w) => w.Inner.Value + 1;
    public static ulong PairMine(ulong x) { Pair<Mine> pair = default; pair.A.Value = (uint)x; return pair.A.Value; }
    public static ulong LibFirst(ulong x) => PairOps.First(x);
    public static ulong LibSize(ulong x) => PairOps.Size<Mine>(x);
    public static ulong LibBoxStatic(ulong x) => Box<ulong>.Twice(x);
    public static ulong BoxGet(ulong x) { Box<uint> box = default; box.Tag = x; return box.Get(); }
    public static ulong AlgoDirect(ulong x) => Algo<ulong>.Run(x);
    public static ulong AlgoCell(ulong x) => Algo<Cell>.Run(x);
    public static ulong AlgoMine(ulong x) => Algo<Mine>.Run(x);
    public static ulong OuterHelper(ulong x) => Outer<uint>.Helper.Run(x);
    public static unsafe ulong AlgoPointer(ulong x) => ((delegate*<ulong, ulong>)&Algo<ulong>.Run)(x);
    public static unsafe ulong Handler<TGas>(ulong x) where TGas : unmanaged =>
        Invoke(&LocalAlgo<TGas>.Run, x);
    static unsafe ulong Invoke(delegate*<ulong, ulong> handler, ulong x) => handler(x) + 1;
    public static ulong LocalStatic(ulong x) => LocalAlgo<Mine>.Load(x);
    public static ulong LocalSeeded(ulong x) => Seeded<Mine>.Get(x);
    public static ulong LocalInstance(ulong x) => new Instance<Mine>().Get(x);
    public static ulong Holding(ulong x) { Holder<ulong> holder = default; holder.Item = x; return holder.Item; }
    public static ulong ReferenceArgument(ulong x) => Free<string>.Self(x);
    public static ulong Cycle(ulong x) { Loop loop = default; loop.Pair.A = x; return loop.Pair.A; }
    public static unsafe ulong Dispatch<TGas>(delegate*<ulong, ulong>[] handlers, int index, ulong x)
        where TGas : unmanaged => handlers[index](x) + (ulong)Unsafe.SizeOf<TGas>();
    public static unsafe ulong CallDispatch(delegate*<ulong, ulong>[] handlers, ulong x) =>
        Dispatch<Mine>(handlers, 0, x);
    public static unsafe void Targets(delegate*<ulong, ulong>[] handlers) => handlers[0] = &LocalAlgo<Mine>.Run;
    public static unsafe ulong PointerTable<TGas>(delegate*<ulong, ulong>* table, ulong x)
        where TGas : unmanaged => table[0](x);
    public static unsafe ulong Unmanaged<TGas>(delegate* unmanaged<ulong, ulong>[] table, ulong x)
        where TGas : unmanaged => x;
    public static unsafe ulong Narrow<TGas>(delegate*<uint, ulong>[] table, uint x)
        where TGas : unmanaged => table[0](x);
}
""";

string Project(string name, string assembly, string source, string references = "")
{
    string directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.WriteAllText(Path.Combine(directory, name + ".csproj"), $"""
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
        <AssemblyName>{assembly}</AssemblyName><Optimize>true</Optimize><Nullable>enable</Nullable>
        <AllowUnsafeBlocks>true</AllowUnsafeBlocks></PropertyGroup><ItemGroup>{references}</ItemGroup></Project>
        """);
    File.WriteAllText(Path.Combine(directory, name + ".cs"), source);
    Run(["dotnet", "build", Path.Combine(directory, name + ".csproj"), "-c", "Release"]);
    return Path.Combine(directory, "bin", assembly + ".dll");
}

string lib = Project("Lib", libName, libraryText);
string app = Project("App", appName, applicationText, """<ProjectReference Include="../Lib/Lib.csproj" />""");
string libIdentity = libName + unsigned;
string appIdentity = appName + unsigned;
string Artifact(string name) => Path.Combine(root, "x-" + name);
string[] Reference(string path) => ["--reference", path];

string ProofFor(string name, ulong result)
{
    string path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, $$"""
        import Extracted

        /-! The extracted `{{name}}` computes its CLR result from the input 5. -/

        open CIL
        namespace MultiAssemblyGenericsProof

        /-- `{{name}} 5 = {{result}}`, with every layout and body bound to its pinned assembly. -/
        theorem correctness :
            (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 5)] Safety.Memory.empty).map Prod.snd =
              .ok [.scalar (.i64 {{result}})] := by
          rfl

        #print axioms correctness
        end MultiAssemblyGenericsProof
        """);
    return path;
}

void Proved(string name, string selector, ulong result, bool referencedBody, params string[] extra)
{
    string artifact = Artifact(name);
    Run([.. cli, "extract", app, selector, artifact, .. Reference(lib), .. extra]);
    string extracted = File.ReadAllText(Path.Combine(artifact, "Extracted.lean"));
    if (extracted.Contains("assembly := assembly1", StringComparison.Ordinal) != referencedBody)
        throw new InvalidOperationException("Certificate misattributes the referenced assembly's bodies: " + name);
    Run([.. cli, "verify", artifact, "--proof", ProofFor(name, result),
        "--theorem", "MultiAssemblyGenericsProof.correctness"]);
    Console.WriteLine("PASS cross-assembly generic " + name + ": pinned layouts and bodies with proof");
}

string Entry(string method) => "GenericFixture.Application::" + method + "(ulong)";
// Lib generic structs: a local, a reference to an App helper and a Lib callee, a type argument.
Proved("PairLocal", Entry("PairLocal"), 7, referencedBody: false);
Proved("PairByRef", Entry("PairByRef"), 7, referencedBody: false);
Proved("PairLib", Entry("PairLib"), 6, referencedBody: true);
Proved("PairArgument", Entry("PairArgument"), 13, referencedBody: false);
// An App generic struct over a Lib struct, and a Lib generic struct over an App struct.
Proved("WrapLocal", Entry("WrapLocal"), 6, referencedBody: false);
Proved("WrapByRef", Entry("WrapByRef"), 6, referencedBody: false);
Proved("PairMine", Entry("PairMine"), 5, referencedBody: false);
// Lib generic methods and static methods of Lib generic types, closed over App and Lib types.
Proved("LibFirst", Entry("LibFirst"), 5, referencedBody: true);
Proved("LibSize", Entry("LibSize"), 9, referencedBody: true);
Proved("LibBoxStatic", Entry("LibBoxStatic"), 10, referencedBody: true);
// An instance method of a Lib generic struct on an App local.
Proved("BoxGet", Entry("BoxGet"), 6, referencedBody: true);
Proved("AlgoDirect", Entry("AlgoDirect"), 23, referencedBody: true);
Proved("AlgoCell", Entry("AlgoCell"), 23, referencedBody: true);
Proved("AlgoMine", Entry("AlgoMine"), 19, referencedBody: true);
Proved("OuterHelper", Entry("OuterHelper"), 9, referencedBody: true);
Proved("AlgoPointer", Entry("AlgoPointer"), 23, referencedBody: true);
// The handler-table shape: an address of `LocalAlgo<TGas>.Run` taken in a specialized body.
Proved("Handler", Entry("Handler"), 10, referencedBody: false, "--type-argument", "GenericFixture.Mine");
// A static method of a generic class is the entry, closed over an App or a Lib struct.
const string localRun = "GenericFixture.LocalAlgo`1::Run(ulong)";
Proved("EntryMine", localRun, 9, referencedBody: false, "--type-argument", "GenericFixture.Mine");
Proved("EntryCell", localRun, 13, referencedBody: false, "--type-argument", "GenericFixture.Cell, " + libName);
// The open type name assumes every instantiation's initializer ran.
Proved("Seeded", Entry("LocalSeeded"), 5, referencedBody: false, "--assume-initialized", "GenericFixture.Seeded`1");

// Supplied handler tables: a generic entry and a generic callee take `delegate*<ulong, ulong>[]`.
// The catalog comes from the closed `&LocalAlgo<Mine>.Run` in `Targets`; any other identity is
// outside it and stops with `invalidState`, even a real instantiation no extracted body addresses.
const string tableSelector = "(method System.UInt64 *(System.UInt64)[],";
foreach ((string name, string selector, string arguments, ulong result, string[] extra) in new[]
{
    ("Dispatch", "Dispatch" + tableSelector + "System.Int32,System.UInt64)", ".scalar (.i32 0), .scalar (.i64 5)",
        13ul, new[] { "--type-argument", "GenericFixture.Mine" }),
    ("CallDispatch", "CallDispatch" + tableSelector + "System.UInt64)", ".scalar (.i64 5)", 13ul, [])
})
{
    string artifact = Artifact(name);
    Run([.. cli, "extract", app, "GenericFixture.Application::" + selector, artifact, .. Reference(lib), .. extra]);
    string extracted = File.ReadAllText(Path.Combine(artifact, "Extracted.lean"));
    Match catalogued = Regex.Match(extracted,
        @"identity := (\{ owner := ""[^""]*::GenericFixture\.LocalAlgo\\u00601"", [^}]*\})");
    if (!catalogued.Success)
        throw new InvalidOperationException("Precondition: the catalog must hold LocalAlgo<Mine>.Run: " + name);
    string identity = catalogued.Groups[1].Value;
    string uncatalogued = Regex.Replace(identity, @"arguments := \[.*\]",
        "arguments := [.atom CIL.Extraction.runtimeScope \"System.UInt64\"]");
    string proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, $$"""
        import Extracted

        /-! `{{name}}` calls through a supplied table of `LocalAlgo<Mine>.Run` from the input 5. -/

        open CIL
        namespace MultiAssemblyGenericsProof

        /-- The exact managed signature of `delegate*<ulong, ulong>`. -/
        def signature : CIL.ManagedSignature :=
          ⟨.atom CIL.Extraction.runtimeScope "System.UInt64",
            [.atom CIL.Extraction.runtimeScope "System.UInt64"]⟩

        /-- A catalogued handler runs; `LocalAlgo<ulong>.Run`, addressed by no extracted body, does not. -/
        theorem correctness :
            (CIL.Safety.invoke Extracted.program 64 0
              [.methodTable ⟨signature, some #[{{identity}}], none⟩, {{arguments}}]
              Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 {{result}})] ∧
            (match CIL.Safety.invoke Extracted.program 64 0
              [.methodTable ⟨signature, some #[{{uncatalogued}}], none⟩, {{arguments}}]
              Safety.Memory.empty with
              | .error fault => some fault.fault | .ok _ => none) = some .invalidState :=
          ⟨by rfl, by rfl⟩

        #print axioms correctness
        end MultiAssemblyGenericsProof
        """);
    Run([.. cli, "verify", artifact, "--proof", proof, "--theorem", "MultiAssemblyGenericsProof.correctness"]);
    Console.WriteLine("PASS supplied handler table: " + name);
}

void Rejected(string name, string marker, string[] command)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException($"Expected rejection {name} ({marker}): {result.Output}");
    Console.WriteLine("PASS rejected " + name);
}

void RejectedExtract(string name, string marker, string assembly, string selector, params string[] extra)
{
    string output = Path.Combine(root, "r-" + name.Replace(' ', '-'));
    Rejected(name, marker, [.. cli, "extract", assembly, selector, output, .. extra]);
    if (File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Rejected extraction left a certificate: " + name);
}

// Without a pin, Lib types and bodies are never read through Cecil's ambient resolver.
RejectedExtract("unpinned generic struct", "Unsupported type: GenericFixture.Pair`1<System.UInt64>",
    app, Entry("PairLocal"));
RejectedExtract("unpinned type argument", "Unsupported type identity: GenericFixture.Cell", app, Entry("WrapLocal"));
RejectedExtract("unpinned generic class", "Rejected external call", app, Entry("AlgoDirect"));
RejectedExtract("unpinned entry type argument", "no single pinned --reference assembly", app, localRun,
    [.. Reference(lib), "--type-argument", "GenericFixture.Cell, Other"]);
RejectedExtract("reference field", "Unsupported field type: System.Object", app, Entry("Holding"), Reference(lib));
RejectedExtract("reference type argument", "Unsupported type: System.String",
    app, Entry("ReferenceArgument"), Reference(lib));
RejectedExtract("instance method of a generic class", "Unsupported generic method signature or body",
    app, Entry("LocalInstance"), Reference(lib));
RejectedExtract("instance entry of a generic class", "only static methods of a generic type can be an entry",
    app, "GenericFixture.Instance`1::Get(ulong)", "--type-argument", "GenericFixture.Mine");
RejectedExtract("open generic class entry", "followed by 1 for GenericFixture.LocalAlgo`1", app, localRun);
RejectedExtract("static field of a generic class", "Unsupported static field load", app, Entry("LocalStatic"));
string Table(string method, string signature) => $"GenericFixture.Application::{method}(method {signature},";
RejectedExtract("unmanaged function pointer table", "Unsupported entry function pointer calling convention",
    app, Table("Unmanaged", "System.UInt64 *(System.UInt64)[]") + "System.UInt64)",
    [.. Reference(lib), "--type-argument", "GenericFixture.Mine"]);
// No addressed method has the signature `ulong(uint)`, so the indirect call has no target.
RejectedExtract("mismatched function pointer table", "Empty managed pointer target catalog",
    app, Table("Narrow", "System.UInt64 *(System.UInt32)[]") + "System.UInt32)",
    [.. Reference(lib), "--type-argument", "GenericFixture.Mine"]);
RejectedExtract("open function pointer table entry", "Contract method requires an exact closed generic instantiation",
    app, Table("Dispatch", "System.UInt64 *(System.UInt64)[]") + "System.Int32,System.UInt64)", Reference(lib));
// A pointer to function pointers is not an admitted storage type; tables are arrays or `nint*`.
RejectedExtract("function pointer pointer table", "Unsupported stack-storage pointer element type",
    app, Table("PointerTable", "System.UInt64 *(System.UInt64)*") + "System.UInt64)",
    [.. Reference(lib), "--type-argument", "GenericFixture.Mine"]);
RejectedExtract("generic class initializer", "pass --assume-initialized GenericFixture.Seeded`1",
    app, Entry("LocalSeeded"));

// C# rejects struct cycles, so the App field is retyped from `Pair<ulong>` to `Pair<Loop>`.
string cyclic = Path.Combine(root, "Cyclic", appName + ".dll");
Directory.CreateDirectory(Path.GetDirectoryName(cyclic)!);
using (ModuleDefinition module = ModuleDefinition.ReadModule(app))
{
    TypeDefinition loop = module.GetType("GenericFixture.Loop");
    FieldDefinition field = loop.Fields.Single();
    GenericInstanceType pair = new(((GenericInstanceType)field.FieldType).ElementType);
    pair.GenericArguments.Add(loop);
    field.FieldType = pair;
    module.Write(cyclic);
}
RejectedExtract("layout cycle through a pinned reference", "Recursive or excessively nested aggregate layout",
    cyclic, Entry("Cycle"), Reference(lib));

// A layout table that moves Lib's generic owner into App no longer derives its identity.
string forged = Path.Combine(root, "t-owner");
Directory.CreateDirectory(forged);
foreach (string file in Directory.EnumerateFiles(Artifact("PairMine")))
    File.Copy(file, Path.Combine(forged, Path.GetFileName(file)));
string lean = Path.Combine(forged, "Extracted.lean");
string source = File.ReadAllText(lean);
string owner = $"owner := .constructor \"{libIdentity}\"";
if (!source.Contains(owner, StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: the certificate must scope Pair`1 to " + libIdentity);
File.WriteAllText(lean, source.Replace(owner, $"owner := .constructor \"{appIdentity}\"", StringComparison.Ordinal));
Rejected("moved generic owner", "Stale", [.. cli, "verify", forged, "--proof", Path.Combine(root, "PairMine.lean"),
    "--theorem", "MultiAssemblyGenericsProof.correctness"]);
(int Code, string Output, string Stdout, string Stderr) kernel =
    Execute(["lake", "env", "lean", lean], cwd: FixturePackage());
if (kernel.Code == 0 || !kernel.Output.Contains("layouts_validated", StringComparison.Ordinal))
    throw new InvalidOperationException("Lean accepted a generic layout moved to another assembly: " + kernel.Output);
Console.WriteLine("PASS Lean rejected moved generic owner");
Console.WriteLine("PASS cross-assembly generics: structs, generic classes, entries, addresses and rejections");
