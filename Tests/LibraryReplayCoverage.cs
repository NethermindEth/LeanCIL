#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var root = At("artifacts/LibraryReplayCoverage-" + Guid.NewGuid().ToString("N"));
var library = Path.Combine(root, "library");
using var verifier = new Program();
var (key, sources) = verifier.LibraryIdentity(CommonInputs());
foreach (var name in sources.Keys)
{
    var destination = Path.Combine(library, name);
    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
    File.Copy(At(name), destination);
}
var source = Path.Combine(root, "AUnaggregatedForgery.lean");
Directory.CreateDirectory(Path.GetDirectoryName(source)!);
File.WriteAllText(source, """
    import Lean
    def main (args : List String) : IO Unit := do
      Lean.initSearchPath (← Lean.findSysroot)
      let env ← Lean.importModules #[{ module := `Init }] {}
      Lean.writeModule (env.setMainModule `CIL) args[0]!
      let env := env.setMainModule `AUnaggregatedForgery
      let env ← IO.ofExcept <| (env.addDeclCore 0 0 (.thmDecl {
        name := `UnaggregatedForgery.bad
        levelParams := []
        type := Lean.mkConst ``False
        value := Lean.mkConst ``True.intro
      }) none false).mapError (fun _ => "Could not construct rejection fixture")
      Lean.writeModule env args[1]!
    """);
Directory.CreateDirectory(Path.Combine(library, ".lake/build/lib/lean"));
Run([verifier.LeanExecutable, "--run", source, Path.Combine(library, ".lake/build/lib/lean/CIL.olean"),
    Path.Combine(library, ".lake/build/lib/lean/AUnaggregatedForgery.olean")],
    environment: verifier.LeanEnvironment);
// Simulate a faulty producer with a tiny target set, so the regression tests kernel coverage
// rather than source correspondence or artifact authentication (which have separate fixtures).
File.WriteAllText(Path.Combine(library, "library-key.txt"), key);
File.WriteAllText(Path.Combine(library, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(library)));
var digest = Sha(Path.Combine(library, "cache-manifest.json"));
try { verifier.ReusePreparedLibrary(library, digest); }
catch (InvalidOperationException error) when (
    error.Message.Contains("UnaggregatedForgery.bad", StringComparison.Ordinal))
{
    Console.WriteLine("PASS fallback kernel replay rejects a forged module outside the CIL aggregate");
    return;
}
throw new Exception("Fallback kernel replay ignored an invalid nonaggregate library module");
