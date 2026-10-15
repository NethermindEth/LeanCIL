using System.Globalization;
using System.Numerics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

if (args.Length != 1) throw new ArgumentException("Usage: NativeProbe <output-directory>");
if (IntPtr.Size != 8) throw new PlatformNotSupportedException("Requires a native 64-bit runtime.");
var output = Path.GetFullPath(args[0]);
Directory.CreateDirectory(output);
var operations = new[] {
    OpCodes.Add, OpCodes.Sub, OpCodes.Mul, OpCodes.Div, OpCodes.Div_Un, OpCodes.Rem, OpCodes.Rem_Un,
    OpCodes.Add_Ovf, OpCodes.Add_Ovf_Un, OpCodes.Sub_Ovf, OpCodes.Sub_Ovf_Un, OpCodes.Mul_Ovf, OpCodes.Mul_Ovf_Un,
    OpCodes.And, OpCodes.Or, OpCodes.Xor, OpCodes.Ceq, OpCodes.Clt, OpCodes.Clt_Un, OpCodes.Cgt, OpCodes.Cgt_Un,
    OpCodes.Beq, OpCodes.Bne_Un, OpCodes.Blt, OpCodes.Blt_Un, OpCodes.Bgt, OpCodes.Bgt_Un,
    OpCodes.Ble, OpCodes.Ble_Un, OpCodes.Bge, OpCodes.Bge_Un
};
var fixture = Path.Combine(output, "MixedNative.dll");
using (var module = ModuleDefinition.CreateModule("MixedNative", ModuleKind.Dll))
{
    var owner = new TypeDefinition("Probe", "Mixed", Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Class,
        module.TypeSystem.Object);
    module.Types.Add(owner);
    foreach (var op in operations)
    foreach (var reverse in new[] { false, true })
    foreach (uint? constant in new uint?[] { null, 0, 1, int.MaxValue, 0x80000000, uint.MaxValue })
    foreach (var conversion in UnsignedBranch(op.Code) ? new[] { -1, 0, 1 } : new[] { -1 })
    {
        var method = new MethodDefinition(Name(op, reverse, constant, conversion), Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
            module.TypeSystem.IntPtr);
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.IntPtr));
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
        owner.Methods.Add(method);
        var code = method.Body.Instructions;
        code.Add(reverse && constant.HasValue ? Instruction.Create(OpCodes.Ldc_I4, unchecked((int)constant.Value)) : Instruction.Create(reverse ? OpCodes.Ldarg_1 : OpCodes.Ldarg_0));
        if (reverse && conversion >= 0) code.Add(Instruction.Create(conversion == 0 ? OpCodes.Conv_I : OpCodes.Conv_U));
        code.Add(!reverse && constant.HasValue ? Instruction.Create(OpCodes.Ldc_I4, unchecked((int)constant.Value)) : Instruction.Create(reverse ? OpCodes.Ldarg_0 : OpCodes.Ldarg_1));
        if (!reverse && conversion >= 0) code.Add(Instruction.Create(conversion == 0 ? OpCodes.Conv_I : OpCodes.Conv_U));
        if (op.FlowControl == FlowControl.Cond_Branch)
        {
            var taken = Instruction.Create(OpCodes.Ldc_I4_1);
            var join = Instruction.Create(OpCodes.Conv_I);
            code.Add(Instruction.Create(op, taken));
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            code.Add(Instruction.Create(OpCodes.Br, join));
            code.Add(taken);
            code.Add(join);
        }
        else
        {
            code.Add(Instruction.Create(op));
            code.Add(Instruction.Create(OpCodes.Conv_I));
        }
        code.Add(Instruction.Create(OpCodes.Ret));
    }
    module.Write(fixture, new WriterParameters { DeterministicMvid = true, Timestamp = 0 });
}
var assembly = Assembly.Load(File.ReadAllBytes(fixture));
var type = assembly.GetType("Probe.Mixed")!;
using var rows = new StreamWriter(Path.Combine(output, "results.csv"));
rows.WriteLine("opcode,order,int32_source,conversion,admitted,native_hex,int32_hex,expected,actual,pass");
var count = 0;
var failed = 0;
var rejected = 0;
var historicalDivergences = 0;
foreach (var op in operations)
foreach (var reverse in new[] { false, true })
foreach (var wide in new ulong[] { 0, 1, long.MaxValue, 0x8000000000000000, ulong.MaxValue })
foreach (var narrow in new uint[] { 0, 1, int.MaxValue, 0x80000000, uint.MaxValue })
foreach (var constant in new[] { false, true })
foreach (var conversion in UnsignedBranch(op.Code) ? new[] { -1, 0, 1 } : new[] { -1 })
{
    var method = type.GetMethod(Name(op, reverse, constant ? narrow : null, conversion))!;
    string actual;
    try { actual = unchecked((ulong)(nint)method.Invoke(null, [unchecked((nint)wide), unchecked((int)narrow)])!).ToString("X16", CultureInfo.InvariantCulture); }
    catch (TargetInvocationException error) when (error.InnerException is DivideByZeroException or OverflowException)
    { actual = error.InnerException.GetType().Name; }
    var expected = Expected(op.Code, reverse, wide, narrow, conversion);
    var pass = actual == expected;
    var admitted = !UnsignedBranch(op.Code) || conversion >= 0;
    if (!admitted) rejected++;
    if (!pass && admitted) failed++;
    if (!pass && !admitted) historicalDivergences++;
    count++;
    rows.WriteLine($"{op.Name},{(reverse ? "int32-native" : "native-int32")},{(constant ? "constant" : "argument")},{(conversion < 0 ? "implicit" : conversion == 0 ? "conv.i" : "conv.u")},{admitted},{wide:X16},{narrow:X8},{expected},{actual},{pass}");
}
rows.Dispose();
using var saved = ModuleDefinition.ReadModule(fixture);
var core = typeof(object).Assembly;
var runtimeDirectory = Path.GetDirectoryName(core.Location)!;
string Hash(string path) => Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)));
var binaries = Directory.GetFiles(runtimeDirectory).Where(path => Path.GetFileName(path) is
    "coreclr.dll" or "clrjit.dll" or "libcoreclr.dylib" or "libclrjit.dylib" or "System.Private.CoreLib.dll")
    .ToDictionary(path => Path.GetFileName(path)!, Hash);
var manifest = new {
    framework = RuntimeInformation.FrameworkDescription,
    architecture = RuntimeInformation.ProcessArchitecture.ToString(), os = RuntimeInformation.OSDescription,
    runtimeVersion = Environment.Version.ToString(),
    coreLibraryVersion = core.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion,
    runtimeBuild = File.ReadAllLines(Path.Combine(runtimeDirectory, ".version")),
    runtimeBinarySha256 = binaries, fixtureSha256 = Hash(fixture),
    probeSha256 = Hash(Assembly.GetExecutingAssembly().Location),
    resultsSha256 = Hash(Path.Combine(output, "results.csv")), count, failed, rejected, historicalDivergences,
    methods = saved.GetType("Probe.Mixed").Methods.Select(m => new {
        name = m.Name, signature = m.FullName,
        instructions = m.Body.Instructions.Select(i => i.ToString()).ToArray()
    }).ToArray()
};
File.WriteAllText(Path.Combine(output, "manifest.json"), JsonSerializer.Serialize(manifest, new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine($"{(failed == 0 ? "PASS" : "FAIL")} {count - rejected} admitted probes, {failed} mismatches, {rejected} rejected mixed branches with {historicalDivergences} historical divergences, {RuntimeInformation.FrameworkDescription}, {RuntimeInformation.ProcessArchitecture}");
return failed == 0 ? 0 : 1;

static string Name(OpCode op, bool reverse, uint? constant, int conversion) => op.Name.Replace('.', '_') + (reverse ? "_reverse" : "_forward") + (constant.HasValue ? $"_constant_{constant.Value:X8}" : "_argument") + (conversion < 0 ? "_implicit" : conversion == 0 ? "_conv_i" : "_conv_u");

// Independent mathematical oracle for the admitted mixed-width rules, not an
// invocation of another mixed native/int32 opcode or the extractor.
static bool UnsignedBranch(Code op) => op is Code.Bne_Un or Code.Blt_Un or Code.Bgt_Un or Code.Ble_Un or Code.Bge_Un;

static string Expected(Code op, bool reverse, ulong wide, uint narrow, int conversion)
{
    var zeroExtend = op is Code.Add_Ovf_Un or Code.Sub_Ovf_Un or Code.Mul_Ovf_Un or
        Code.Blt_Un or Code.Bgt_Un or Code.Ble_Un or Code.Bge_Un or Code.Bne_Un;
    if (conversion >= 0) zeroExtend = conversion == 1;
    var extended = zeroExtend ? narrow : unchecked((ulong)(long)(int)narrow);
    var left = reverse ? extended : wide;
    var right = reverse ? wide : extended;
    var unsigned = op is Code.Add_Ovf_Un or Code.Sub_Ovf_Un or Code.Mul_Ovf_Un or Code.Div_Un or Code.Rem_Un or
        Code.Clt_Un or Code.Cgt_Un or Code.Blt_Un or Code.Bgt_Un or Code.Ble_Un or Code.Bge_Un;
    BigInteger x = unsigned ? new BigInteger(left) : new BigInteger(unchecked((long)left));
    BigInteger y = unsigned ? new BigInteger(right) : new BigInteger(unchecked((long)right));
    if (op is Code.Div or Code.Div_Un or Code.Rem or Code.Rem_Un)
    {
        if (y == 0) return nameof(DivideByZeroException);
        if (!unsigned && x == long.MinValue && y == -1) return nameof(OverflowException);
    }
    BigInteger result = op switch {
        Code.Add or Code.Add_Ovf or Code.Add_Ovf_Un => x + y,
        Code.Sub or Code.Sub_Ovf or Code.Sub_Ovf_Un => x - y,
        Code.Mul or Code.Mul_Ovf or Code.Mul_Ovf_Un => x * y,
        Code.Div or Code.Div_Un => x / y,
        Code.Rem or Code.Rem_Un => x % y,
        Code.And => left & right, Code.Or => left | right, Code.Xor => left ^ right,
        Code.Ceq or Code.Beq => left == right ? 1 : 0, Code.Bne_Un => left != right ? 1 : 0,
        Code.Clt or Code.Clt_Un or Code.Blt or Code.Blt_Un => x < y ? 1 : 0,
        Code.Cgt or Code.Cgt_Un or Code.Bgt or Code.Bgt_Un => x > y ? 1 : 0,
        Code.Ble or Code.Ble_Un => x <= y ? 1 : 0, Code.Bge or Code.Bge_Un => x >= y ? 1 : 0,
        _ => throw new InvalidOperationException(op.ToString())
    };
    if (op is Code.Add_Ovf or Code.Sub_Ovf or Code.Mul_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf_Un or Code.Mul_Ovf_Un)
    {
        var min = unsigned ? BigInteger.Zero : long.MinValue;
        var max = unsigned ? new BigInteger(ulong.MaxValue) : long.MaxValue;
        if (result < min || result > max) return nameof(OverflowException);
    }
    return ((ulong)(result & ulong.MaxValue)).ToString("X16", CultureInfo.InvariantCulture);
}


