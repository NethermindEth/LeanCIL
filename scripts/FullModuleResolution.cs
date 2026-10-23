using System.Text.Json;

partial class Program
{
    // Lean must load each module from the exact file whose hash was accepted.
    void CheckFullResolution(string directory, string leanPath, SortedDictionary<string, string> modules)
    {
        string manifest = Path.Combine(directory, "full-module-resolution.json");
        File.WriteAllText(manifest, JsonSerializer.Serialize(modules.Select(pair => new { name = pair.Key, path = pair.Value })));
        string probe = Path.Combine(directory, "FullModuleResolution.lean");
        File.WriteAllText(probe, $$"""
import Lean
private structure ExpectedResolution where
  name : String
  path : String
  deriving Lean.FromJson
run_cmd do
  let expected : Array ExpectedResolution <- IO.ofExcept <|
    (Lean.Json.parse (<- IO.FS.readFile {{JsonSerializer.Serialize(manifest)}})).bind Lean.fromJson?
  for item in expected do
    let path <- Lean.findOLean item.name.toName
    -- Lean joins roots verbatim; compare canonical files, not spellings.
    unless (<- IO.FS.realPath path) == (<- IO.FS.realPath item.path) do throwError "Full-verification resolved module path changed: {item.name}"
""");
        Run([LeanExecutable, probe], directory, leanPath, environment: LeanEnvironment,
            progress: "Checking actual full-verification module resolution");
    }
}
