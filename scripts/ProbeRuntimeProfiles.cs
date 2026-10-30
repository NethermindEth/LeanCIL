#!/usr/bin/env dotnet
#:property PublishAot=false

using System.Diagnostics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;
using System.Text.Json;

if (args is ["--child"])
{
    Console.WriteLine(JsonSerializer.Serialize(new
    {
        runtime = RuntimeInformation.FrameworkDescription,
        runtimeVersion = Environment.Version.ToString(),
        architecture = RuntimeInformation.ProcessArchitecture.ToString(),
        os = RuntimeInformation.OSDescription,
        advSimd = AdvSimd.IsSupported,
        advSimd64 = AdvSimd.Arm64.IsSupported,
        armBase64 = ArmBase.Arm64.IsSupported,
        x86Base64 = X86Base.X64.IsSupported,
        sse2 = Sse2.IsSupported,
        ssse3 = Ssse3.IsSupported,
        sse41 = Sse41.IsSupported,
        sse42 = Sse42.IsSupported,
        avx = Avx.IsSupported,
        avx2 = Avx2.IsSupported,
        bmi1 = Bmi1.IsSupported,
        bmi2 = Bmi2.X64.IsSupported,
        avx512F = Avx512F.IsSupported,
        avx512FVL = Avx512F.VL.IsSupported,
        avx512DQ = Avx512DQ.IsSupported,
        avx512DQVL = Avx512DQ.VL.IsSupported,
        avx512Vbmi = Avx512Vbmi.IsSupported,
        avx512VbmiVL = Avx512Vbmi.VL.IsSupported,
        vector128Accelerated = Vector128.IsHardwareAccelerated,
        vector256Accelerated = Vector256.IsHardwareAccelerated
    }));
    return;
}
if (args is not [var output])
    throw new ArgumentException("Usage: dotnet run --file scripts/ProbeRuntimeProfiles.cs -- <output.json>");

string[] switches = ["EnableHWIntrinsic", "EnableSSE2", "EnableSSSE3", "EnableSSE41", "EnableSSE42",
    "EnableAVX", "EnableAVX2", "EnableBMI1", "EnableBMI2", "EnableAVX512", "EnableAVX512DQ", "EnableAVX512v2",
    "EnableAVX512F_VL", "EnableArm64AdvSimd", "EnableArm64", "PreferredVectorBitWidth"];
var configurations = new List<(string Name, string? Switch, string? Value)> { ("default", null, null) };
configurations.AddRange(switches.Where(name => name != "PreferredVectorBitWidth").Select(name => (name + "=0", (string?)name, (string?)"0")));
configurations.Add(("PreferredVectorBitWidth=128", "PreferredVectorBitWidth", "128"));
configurations.Add(("PreferredVectorBitWidth=64", "PreferredVectorBitWidth", "64"));
var results = new List<object>();
foreach (var configuration in configurations)
{
    var start = new ProcessStartInfo("dotnet") { UseShellExecute = false, RedirectStandardOutput = true, RedirectStandardError = true };
    start.ArgumentList.Add(Assembly.GetExecutingAssembly().Location);
    start.ArgumentList.Add("--child");
    foreach (var name in switches)
    {
        start.Environment.Remove("DOTNET_" + name);
        start.Environment.Remove("COMPlus_" + name);
    }
    if (configuration.Switch is not null) start.Environment["DOTNET_" + configuration.Switch] = configuration.Value;
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start runtime probe.");
    var stdout = process.StandardOutput.ReadToEndAsync();
    var stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    if (process.ExitCode != 0) throw new InvalidOperationException(await stderr);
    using var observed = JsonDocument.Parse(await stdout);
    results.Add(new { configuration = configuration.Name, observed = observed.RootElement.Clone() });
}
File.WriteAllText(output, JsonSerializer.Serialize(results, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
Console.WriteLine($"Recorded {results.Count} fresh-process configurations in {output}");
