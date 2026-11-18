#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil

extern alias IdentityExtractor;

using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;

// Dead instructions in the admitted scalar self-admission corpus, including compiler-generated bodies.
const string Usage = "Usage: HoleCorpus.cs [--update] [--baseline path] [--admission-report path]";
const string Profile = "scalar";
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));
var baselinePath = Path.Combine(root, "Tests/HoleCorpusBaseline.txt");
string? admissionReport = null;
var update = false;
for (var index = 0; index < args.Length; index++)
    switch (args[index])
    {
        case "--update": update = true; break;
        case "--baseline" when index + 1 < args.Length: baselinePath = Path.GetFullPath(args[++index]); break;
        case "--admission-report" when index + 1 < args.Length:
            admissionReport = Path.GetFullPath(args[++index]);
            break;
        default: throw new ArgumentException(Usage);
    }

CheckInspection();
var timer = Stopwatch.StartNew();
var assemblyPath = Path.Combine(root, "Extractor/bin/Nethermind.LeanCIL.dll");
var bytes = File.ReadAllBytes(assemblyPath);
var hash = Convert.ToHexStringLower(SHA256.HashData(bytes));
using var pinned = new PinnedAssemblies(bytes, hash, []);
var methods = pinned.Selected.GetTypes().SelectMany(type => type.Methods)
    .ToDictionary(method => method.FullName, StringComparer.Ordinal);
var directory = Path.Combine(root, "artifacts/HoleCorpus");
Directory.CreateDirectory(directory);
if (admissionReport is null)
{
    var manifest = Path.Combine(directory, "manifest.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        entries = methods.Keys.Order(StringComparer.Ordinal).Select(signature => new { signature, profile = Profile })
    }));
    admissionReport = Path.Combine(directory, "blockers.json");
    if (Blockers.Run([assemblyPath, "--manifest", manifest, "--output", admissionReport]) != 0)
        throw new InvalidOperationException("Corpus admission failed.");
}

using var document = JsonDocument.Parse(File.ReadAllText(admissionReport));
var report = document.RootElement;
var extractorBytes = File.ReadAllBytes(typeof(FeatureProfile).Assembly.Location);
var extractorHash = Convert.ToHexStringLower(SHA256.HashData(extractorBytes));
if (report.GetProperty("assemblySha256").GetString() != hash ||
    report.GetProperty("extractorSha256").GetString() != extractorHash ||
    report.GetProperty("initializedTypes").GetArrayLength() != 0)
    throw new InvalidDataException("Admission report does not match the corpus assembly, extractor or assumptions.");
var results = new List<MethodHoles>();
var seen = new HashSet<string>(StringComparer.Ordinal);
var skipped = 0;
foreach (var entry in report.GetProperty("entries").EnumerateArray())
{
    var signature = entry.GetProperty("signature").GetString()!;
    if (!seen.Add(signature) || !methods.TryGetValue(signature, out var method) ||
        entry.GetProperty("profile").GetString() != Profile ||
        entry.GetProperty("typeArguments").GetArrayLength() != 0)
        throw new InvalidDataException("Unexpected corpus admission entry: " + signature);
    switch (entry.GetProperty("status").GetString())
    {
        case "admitted": results.Add(Inspect(method)); break;
        case "blocked" or "notChecked": skipped++; break;
        default: throw new InvalidDataException("Unexpected admission status for " + signature);
    }
}
if (seen.Count != methods.Count)
    throw new InvalidDataException($"Admission report covers {seen.Count} of {methods.Count} methods.");

File.WriteAllText(Path.Combine(directory, "methods.json"),
    JsonSerializer.Serialize(new { skipped, methods = results }, new JsonSerializerOptions { WriteIndented = true }));
// A corpus with no admitted method would pass with nothing inspected.
if (results.Count == 0)
    throw new InvalidDataException("The admission report admits no corpus method, so no body was inspected.");
string[] rows = [.. results.SelectMany(Rows).Order(StringComparer.Ordinal)];
if (update) File.WriteAllText(baselinePath, string.Concat(rows.Select(row => row + "\n")));
var baseline = File.ReadAllLines(baselinePath).Where(line => line.Length != 0).ToArray();
var removed = baseline.Except(rows, StringComparer.Ordinal).ToArray();
var added = rows.Except(baseline, StringComparer.Ordinal).ToArray();
var homes = results.Count(result => result.Arguments.Length != 0);
var prefixes = results.Sum(result => result.Prefixes.Length);
Console.WriteLine($"{results.Count} admitted methods; {skipped} skipped refused methods; " +
    $"{homes} home differences; {prefixes} dead prefixes; {timer.Elapsed.TotalSeconds:F2} seconds");
foreach (var row in rows) Console.WriteLine(row);
if (!baseline.SequenceEqual(rows, StringComparer.Ordinal))
    throw new InvalidOperationException("Hole corpus differs from " + baselinePath + ":\n" +
        string.Join('\n', removed.Select(row => "- " + row).Concat(added.Select(row => "+ " + row))) +
        "\nReview the differences, then run HoleCorpus.cs --update.");
Console.WriteLine("PASS hole corpus matches the baseline");

static string Source([CallerFilePath] string path = "") => path;

static MethodHoles Inspect(MethodDefinition method)
{
    if (!method.HasBody) return new(method.FullName, [], []);
    var reachable = Reachability.Analyze(method, FeatureProfile.Scalar);
    var allHomes = new HashSet<int>();
    var liveHomes = new HashSet<int>();
    var prefixes = new List<DeadPrefix>();
    var instructions = method.Body.Instructions;
    for (var pc = 0; pc < instructions.Count; pc++)
    {
        var instruction = instructions[pc];
        var live = reachable.Contains(instruction);
        if (instruction.OpCode.Code is Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S)
        {
            var argument = MethodArguments.Index(method, (ParameterDefinition)instruction.Operand);
            allHomes.Add(argument);
            if (live) liveHomes.Add(argument);
        }
        if (!live && instruction.OpCode.OpCodeType == OpCodeType.Prefix)
            prefixes.Add(new(pc, instruction.Offset, instruction.OpCode.Name));
    }
    allHomes.ExceptWith(liveHomes);
    return new(method.FullName, allHomes.Order().ToArray(), prefixes.ToArray());
}

static IEnumerable<string> Rows(MethodHoles result)
{
    if (result.Arguments.Length != 0)
        yield return $"homes\t{result.Method}\t{string.Join(',', result.Arguments)}";
    foreach (var prefix in result.Prefixes)
        yield return $"prefix\t{result.Method}\tpc={prefix.Pc}\tIL_{prefix.Offset:x4}\t{prefix.Opcode}";
}

static void CheckInspection()
{
    using var module = ModuleDefinition.CreateModule("HoleChecks", ModuleKind.Dll);
    var owner = new TypeDefinition("", "Receiver", TypeAttributes.Public, module.TypeSystem.Object);
    module.Types.Add(owner);
    var method = new MethodDefinition("Body", MethodAttributes.Public, module.TypeSystem.Void);
    owner.Methods.Add(method);
    var first = new ParameterDefinition(module.TypeSystem.Int32);
    var second = new ParameterDefinition(module.TypeSystem.Int32);
    method.Parameters.Add(first);
    method.Parameters.Add(second);
    var finish = Instruction.Create(OpCodes.Ret);
    Instruction[] body =
    [
        Instruction.Create(OpCodes.Ldarga_S, first), Instruction.Create(OpCodes.Pop),
        Instruction.Create(OpCodes.Br, finish), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Starg, second), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Starg_S, first), Instruction.Create(OpCodes.Ldnull),
        Instruction.Create(OpCodes.Unaligned, (byte)1), Instruction.Create(OpCodes.Ldind_I4),
        Instruction.Create(OpCodes.Pop), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Readonly), Instruction.Create(OpCodes.Ldelema, module.TypeSystem.Int32),
        Instruction.Create(OpCodes.Pop), finish
    ];
    foreach (var instruction in body) method.Body.Instructions.Add(instruction);
    // Decoded instructions have byte offsets independently of their instruction indices.
    using var image = new MemoryStream();
    module.Write(image);
    image.Position = 0;
    using var decoded = ModuleDefinition.ReadModule(image);
    var result = Inspect(decoded.Types.Single(type => type.Name == owner.Name).Methods.Single());
    string[] expected =
    [
        "homes\tSystem.Void Receiver::Body(System.Int32,System.Int32)\t2",
        "prefix\tSystem.Void Receiver::Body(System.Int32,System.Int32)\tpc=8\tIL_0011\tunaligned.",
        "prefix\tSystem.Void Receiver::Body(System.Int32,System.Int32)\tpc=13\tIL_0018\treadonly."
    ];
    if (!Rows(result).SequenceEqual(expected, StringComparer.Ordinal))
        throw new InvalidOperationException("Incorrect argument or prefix position:\n" +
            string.Join('\n', Rows(result)));
}

sealed record MethodHoles(string Method, int[] Arguments, DeadPrefix[] Prefixes);
sealed record DeadPrefix(int Pc, int Offset, string Opcode);
