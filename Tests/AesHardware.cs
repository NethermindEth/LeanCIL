#!/usr/bin/env dotnet
#:property PublishAot=false

// Compares the host CPU's AES instructions with the Lean model on seeded random blocks. It needs
// only Lean and CIL.SIMD.AES, so an AES-capable runner of either architecture can run it alone.
using System.Diagnostics;
using System.Runtime.Intrinsics;
using ArmAes = System.Runtime.Intrinsics.Arm.Aes;
using X86Aes = System.Runtime.Intrinsics.X86.Aes;

const int Cases = 16;
const int Seed = 20261102;
if (!File.Exists("lakefile.toml")) throw new InvalidOperationException("Run from the LeanCIL repository root");
if (!X86Aes.IsSupported && !ArmAes.IsSupported)
    throw new InvalidOperationException("The AES hardware comparison needs an x86 or ARM64 AES host");

var random = new Random(Seed);
Vector128<byte> Block()
{
    var bytes = new byte[16];
    random.NextBytes(bytes);
    return Vector128.Create(bytes);
}
// Byte i of the vector is bit range 8i of the model's bit vector, so the literal lists bytes high first.
string Literal(Vector128<byte> value)
{
    var bytes = new byte[16];
    value.CopyTo(bytes);
    Array.Reverse(bytes);
    return $"(0x{Convert.ToHexString(bytes)} : V128)";
}

var claims = new List<string>();
for (var index = 0; index < Cases; index++)
{
    Vector128<byte> state = Block(), roundKey = Block();
    if (X86Aes.IsSupported)
        claims.Add($"aesEncryptRound {Literal(state)} {Literal(roundKey)} =\n      " +
            Literal(X86Aes.Encrypt(state, roundKey)));
    else
    {
        claims.Add($"armAesEncrypt {Literal(state)} {Literal(roundKey)} =\n      " +
            Literal(ArmAes.Encrypt(state, roundKey)));
        claims.Add($"aesMixColumns {Literal(state)} = {Literal(ArmAes.MixColumns(state))}");
    }
}
var instructions = X86Aes.IsSupported ? "x86 AESENC" : "ARM64 AESE and AESMC";
var output = Path.Combine("artifacts", "AesHardware");
Directory.CreateDirectory(output);
var proof = Path.Combine(output, "AesHardware.lean");
File.WriteAllText(proof, $$"""
    import CIL.SIMD.AES
    open CIL CIL.Vector
    /-- The host CPU's {{instructions}} on {{Cases}} seeded random blocks. -/
    theorem hostAes :
        {{string.Join(" ∧\n    ", claims)}} := by
      decide +kernel
    #print axioms hostAes

    """);

void Run(params string[] command)
{
    var start = new ProcessStartInfo(command[0]) { UseShellExecute = false };
    foreach (var argument in command[1..]) start.ArgumentList.Add(argument);
    using var process = Process.Start(start)!;
    process.WaitForExit();
    if (process.ExitCode != 0)
        throw new InvalidOperationException($"Command failed ({process.ExitCode}): {string.Join(' ', command)}");
}
Run("lake", "build", "CIL.SIMD.AES");
Run("lake", "env", "lean", proof);
Console.WriteLine($"PASS {instructions} match the Lean AES model on {Cases} seeded random blocks");
