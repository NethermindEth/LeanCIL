using System.Text.Json;

partial class Program
{
    static readonly string[] CorpusCompilerVersions = ["4.14.0", "5.0.0", "5.9.0"];
    const string CorpusReferenceVersion = "10.0.0";

    sealed record CompilerToolchain(string Packages, string References);

    static CompilerToolchain RestoreCompilerToolchain()
    {
        var directory = At("artifacts/CompilerToolchain");
        Directory.CreateDirectory(directory);
        var project = Path.Combine(directory, "Inputs.csproj");
        File.WriteAllText(project, $$"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
              <ItemGroup>
                <PackageDownload Include="Microsoft.Net.Compilers.Toolset"
                  Version="{{string.Join(';', CorpusCompilerVersions.Select(version => "[" + version + "]"))}}" />
                <PackageDownload Include="Microsoft.NETCore.App.Ref" Version="[{{CorpusReferenceVersion}}]" />
              </ItemGroup>
            </Project>
            """);
        Run(["dotnet", "restore", project]);
        using var assets = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, "obj/project.assets.json")));
        var packages = assets.RootElement.GetProperty("packageFolders").EnumerateObject().First().Name;
        return new(packages, Path.Combine(packages, "microsoft.netcore.app.ref", CorpusReferenceVersion, "ref/net10.0"));
    }
}
