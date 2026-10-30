using System.Reflection;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

internal static class RuntimeProfileValidation
{
    internal static IEnumerable<(string Json, bool Valid)> Observations(IEnumerable<string> files)
    {
        foreach (var file in files)
        {
            var observations = JsonNode.Parse(File.ReadAllText(file))!.AsArray();
            if (observations.Count == 0) throw new InvalidDataException("Empty runtime evidence: " + file);
            foreach (var observation in observations)
            {
                var profile = observation!["observed"]!.DeepClone().AsObject();
                // Feature getters read AdvSimd.Arm64 as AdvSimd; a split observation refutes that model.
                if (profile["advSimd64"]?.GetValue<bool>() is not bool advSimd64 ||
                    advSimd64 != profile["advSimd"]!.GetValue<bool>())
                    throw new InvalidDataException("AdvSimd.Arm64 is missing or differs from AdvSimd: " + file);
                profile.Remove("advSimd64");
                // Feature getters read Avx512Vbmi.VL as Avx512Vbmi; a split observation refutes that model.
                if (profile["avx512VbmiVL"]?.GetValue<bool>() is not bool avx512VbmiVL ||
                    avx512VbmiVL != profile["avx512Vbmi"]?.GetValue<bool>())
                    throw new InvalidDataException($"Avx512Vbmi.VL is missing or differs from Avx512Vbmi: {file}");
                profile.Remove("avx512VbmiVL");
                profile.Remove("runtime");
                profile.Remove("runtimeVersion");
                profile.Remove("os");
                profile["name"] = Path.GetFileName(file) + ":" + observation["configuration"]!.GetValue<string>();
                profile["architecture"] = profile["architecture"]!.GetValue<string>().ToLowerInvariant();
                profile["nativeWidth"] = 64;
                profile["littleEndian"] = true;
                yield return (profile.ToJsonString(), true);
            }
        }
    }

    // The same cases exercise the production C# validator and kernel-checked Lean policy.
    internal static void Check(IEnumerable<(string Json, bool Valid)> cases, string extractor, string leanFile)
    {
        var type = Assembly.LoadFrom(Path.GetFullPath(extractor)).GetType("Nethermind.LeanCIL.FeatureProfile", true)!;
        var validate = type.GetMethod("Validate", BindingFlags.Instance | BindingFlags.NonPublic)!;
        var lean = type.GetProperty("Lean", BindingFlags.Instance | BindingFlags.NonPublic)!;
        var options = new JsonSerializerOptions { PropertyNameCaseInsensitive = true };
        var source = new StringBuilder("import CIL.Features\nnamespace RuntimeProfileEvidence\n");
        var index = 0;
        foreach (var (json, valid) in cases)
        {
            var profile = JsonSerializer.Deserialize(json, type, options)!;
            var accepted = true;
            try { validate.Invoke(profile, null); }
            catch (TargetInvocationException exception) when (exception.InnerException is InvalidDataException)
            { accepted = false; }
            if (accepted != valid) throw new InvalidDataException("Unexpected runtime profile validation result: " + json);
            source.AppendLine($"def profile{index} : CIL.FeatureProfile := {lean.GetValue(profile)}");
            source.AppendLine($"theorem case{index} : {(valid ? "" : "¬ ")}profile{index}.Valid := by decide +kernel");
            source.AppendLine($"#print axioms case{index}");
            index++;
        }
        if (index == 0) throw new InvalidDataException("No runtime profile cases supplied.");
        source.AppendLine("end RuntimeProfileEvidence");
        File.WriteAllText(leanFile, source.ToString());
        Console.WriteLine($"C# accepted the expected results for {index} runtime profile cases; Lean evidence: {leanFile}");
    }
}
