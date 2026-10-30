#!/usr/bin/env dotnet
#:property PublishAot=false

using System.Runtime.CompilerServices;
using System.Text.RegularExpressions;

// Each [`name`](path.lean|path.cs) link in the documentation must name something the file still
// declares, so a rename or deletion fails here instead of leaving a stale citation. Line-number
// citations drift silently, so any link whose text or anchor names a source line fails.
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(SourcePath())!, ".."));
var documents = Directory.EnumerateFiles(Path.Combine(root, "docs"), "*.md", SearchOption.AllDirectories)
    .Append(Path.Combine(root, "README.md"))
    .Order(StringComparer.Ordinal)
    .ToArray();
var sources = new Dictionary<string, Source>(StringComparer.Ordinal);
List<string> failures = [];
var checkedReferences = 0;
foreach (var document in documents)
{
    var lines = File.ReadAllLines(document);
    for (var index = 0; index < lines.Length; index++)
    {
        foreach (Match match in Patterns.LineCitation().Matches(lines[index]))
            failures.Add($"{Relative(document)}:{index + 1}: `{match.Value}` cites a source line; cite a declaration name");
        foreach (Match match in Patterns.Link().Matches(lines[index]))
        {
            checkedReferences++;
            var label = match.Groups["label"].Value;
            var target = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(document)!, match.Groups["target"].Value));
            var at = $"{Relative(document)}:{index + 1}: `{label}` -> {Relative(target)}";
            if (!target.StartsWith(root, StringComparison.Ordinal) || !File.Exists(target))
            {
                failures.Add(at + ": the linked file does not exist");
                continue;
            }
            if (!sources.TryGetValue(target, out var source))
                sources[target] = source = Source.Read(target);
            if (Problem(label, target, source) is { } problem) failures.Add(at + ": " + problem);
        }
    }
}
if (failures.Count != 0)
{
    Console.Error.WriteLine($"Stale code references ({failures.Count}):");
    foreach (var failure in failures) Console.Error.WriteLine("  " + failure);
    Console.Error.WriteLine("Rename the link to the new declaration name, or link the file without a name.");
    return 1;
}
Console.WriteLine($"PASS {checkedReferences} named code references in {documents.Length} documents");
return 0;

string Relative(string path) => Path.GetRelativePath(root, path).Replace('\\', '/');

static string SourcePath([CallerFilePath] string path = "") => path;

// Null when `label` is still present in `source`, otherwise why it is not.
static string? Problem(string label, string target, Source source)
{
    if (label.Length > 1 && label[0] == '"' && label[^1] == '"')
        return source.Text.Contains(label, StringComparison.Ordinal) ? null : "the string literal is not in the file";
    if (label.Contains('/'))
        return target.Replace('\\', '/').EndsWith("/" + label, StringComparison.Ordinal)
            ? null : "a path label must name the linked file";
    if (!Patterns.DottedName().IsMatch(label))
        return "the label is neither a declaration name, a quoted string nor a path";
    return target.EndsWith(".lean", StringComparison.Ordinal) ? LeanProblem(label, source) : CSharpProblem(label, source);
}

// A Lean declaration of the full dotted name, or of its last component inside the namespace prefix.
static string? LeanProblem(string label, Source source)
{
    if (EndsWithName(source.Declarations, label)) return null;
    var split = label.LastIndexOf('.');
    return split > 0 && EndsWithName(source.Declarations, label[(split + 1)..]) &&
        EndsWithName(source.Namespaces, label[..split]) ? null : "no Lean declaration has this name";
}

// `Type`, `Member` or `Type.Member`: the type must be declared, and the member declared with a return type.
static string? CSharpProblem(string label, Source source)
{
    var parts = label.Split('.');
    if (parts.Length > 2) return "a C# reference must be `Type`, `Member` or `Type.Member`";
    if (parts.Length == 2 && !source.Types.Contains(parts[0])) return $"no C# type `{parts[0]}` is declared";
    var member = parts[^1];
    if (parts.Length == 1 && source.Types.Contains(member)) return null;
    return source.Members.Contains(member) ? null : $"no C# member `{member}` is declared";
}

// Whether some declared name is `name` or ends with `.name`.
static bool EndsWithName(HashSet<string> names, string name) =>
    names.Any(declared => declared == name || declared.EndsWith("." + name, StringComparison.Ordinal));

// One documented source file and every name it declares, scanned once however many links cite it.
sealed record Source(string Text, HashSet<string> Declarations, HashSet<string> Namespaces,
    HashSet<string> Types, HashSet<string> Members)
{
    static readonly string[] Statements =
        ["return", "new", "throw", "await", "else", "case", "yield", "in", "is", "not", "and", "or"];

    internal static Source Read(string path)
    {
        var text = File.ReadAllText(path);
        return new(text,
            Names(Patterns.LeanDeclaration().Matches(text)),
            Names(Patterns.LeanNamespace().Matches(text)),
            Names(Patterns.CSharpType().Matches(text)),
            Names(Patterns.CSharpMember().Matches(text).Where(declaration =>
                !Statements.Contains(declaration.Groups["prefix"].Value.TrimEnd().Split(' ', '\t')[^1],
                    StringComparer.Ordinal))));
    }

    static HashSet<string> Names(IEnumerable<Match> matches) =>
        matches.Select(match => match.Groups["name"].Value).ToHashSet(StringComparer.Ordinal);
}

static partial class Patterns
{
    [GeneratedRegex(@"\[`(?<label>[^`\]]+)`\]\((?<target>[^)#\s]+\.(?:lean|cs))\)")]
    internal static partial Regex Link();

    [GeneratedRegex(@"\[[^\]]*\.(?:lean|cs):\d[^\]]*\]\(|\]\([^)\s]*\.(?:lean|cs)#L\d")]
    internal static partial Regex LineCitation();

    [GeneratedRegex(@"\A[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)*\z")]
    internal static partial Regex DottedName();

    [GeneratedRegex(@"(?m)^[ \t]*(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*" +
        @"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|macro|syntax|elab)\s+" +
        @"(?<name>[\w'.]*[\w'])")]
    internal static partial Regex LeanDeclaration();

    [GeneratedRegex(@"(?m)^namespace\s+(?<name>[\w'.]*[\w'])\s*$")]
    internal static partial Regex LeanNamespace();

    [GeneratedRegex(@"\b(?:class|struct|record|interface|enum)\s+(?<name>\w+)\b")]
    internal static partial Regex CSharpType();

    [GeneratedRegex(@"(?m)^[ \t]*(?<prefix>(?:[\w<>\[\],.?]+[ \t]+)+)(?<name>\w+)[ \t]*(?:<[^>\n]*>)?[ \t]*\(")]
    internal static partial Regex CSharpMember();
}
