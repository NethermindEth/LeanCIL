#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationGroupRunner.cs

using System.Reflection;

if (args is ["--suite", var suite])
{
    Console.WriteLine(suite + ":" + Environment.GetEnvironmentVariable("LEANCIL_SUITE"));
    var cache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR")!;
    Directory.CreateDirectory(cache);
    if (File.Exists(Path.Combine(cache, "visited"))) return 4;
    File.WriteAllText(Path.Combine(cache, "visited"), suite);
    Console.Error.WriteLine("stderr " + suite);
    return suite == "fails" ? 3 : 0;
}
var directory = Path.GetFullPath(Path.Combine("artifacts", "group-test-" + Guid.NewGuid().ToString("N")));
string[] command = ["dotnet", Assembly.GetExecutingAssembly().Location];
var result = await VerificationGroupRunner.Run(command, ["fails", "passes"], directory);
if (result != 1) throw new InvalidOperationException("A failed member must fail the group");
foreach (var name in new[] { "fails", "passes" })
{
    var log = File.ReadAllText(Path.Combine(directory, "verification-" + name + ".log"));
    if (!log.Contains(name + ":" + name, StringComparison.Ordinal) ||
        !log.Contains("stderr " + name, StringComparison.Ordinal) ||
        File.ReadAllText(Path.Combine(directory, "suite-caches", name, "visited")) != name)
        throw new InvalidOperationException("Every member must run with its own log and cache");
}
if (await VerificationGroupRunner.Run(command, ["other"], directory) != 0)
    throw new InvalidOperationException("A passing group must pass");
foreach (string[] invalid in new[] { Array.Empty<string>(), new[] { "passes", "passes" }, new[] { "../escape" } })
{
    try
    {
        await VerificationGroupRunner.Run(command, invalid, directory);
        throw new InvalidOperationException("Invalid suite list accepted");
    }
    catch (ArgumentException) { }
}
Console.WriteLine("Group failure aggregation, logs, cache isolation and argument validation passed.");
return 0;
