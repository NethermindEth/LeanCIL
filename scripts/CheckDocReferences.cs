#!/usr/bin/env dotnet
#:property PublishAot=false

using System.Runtime.CompilerServices;
using System.Text.RegularExpressions;

// Each [`name`](path.lean|path.cs) link in the documentation must name something the file still
// declares, so a rename or deletion fails here instead of leaving a stale citation.
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));
var documents = Directory.EnumerateFiles(Path.Combine(root, "docs"), "*.md", SearchOption.AllDirectories)
    .Append(Path.Combine(root, "README.md"))
    .Order(StringComparer.Ordinal)
    .ToArray();
var link = new Regex(@"\[`(?<label>[^`\]]+)`\]\((?<target>[^)#\s]+\.(?:lean|cs))\)");
var sources = new Dictionary<string, string>(StringComparer.Ordinal);
List<string> failures = [];
var checkedReferences = 0;
foreach (var document in documents)
{
    var lines = File.ReadAllLines(document);
    for (var index = 0; index < lines.Length; index++)
        foreach (Match match in link.Matches(lines[index]))
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
            if (!sources.TryGetValue(target, out var text))
                sources[target] = text = File.ReadAllText(target);
            if (Problem(label, target, text) is { } problem) failures.Add(at + ": " + problem);
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

static string Source([CallerFilePath] string path = "") => path;

// Null when `label` is still present in `text`, otherwise why it is not.
static string? Problem(string label, string target, string text)
{
    if (label.Length > 1 && label[0] == '"' && label[^1] == '"')
        return text.Contains(label, StringComparison.Ordinal) ? null : "the string literal is not in the file";
    if (label.Contains('/'))
        return target.Replace('\\', '/').EndsWith("/" + label, StringComparison.Ordinal)
            ? null : "a path label must name the linked file";
    if (!Regex.IsMatch(label, @"\A[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)*\z"))
        return "the label is neither a declaration name, a quoted string nor a path";
    return target.EndsWith(".lean", StringComparison.Ordinal) ? LeanProblem(label, text) : CSharpProblem(label, text);
}

// A Lean declaration of the full dotted name, or of its last component inside the namespace prefix.
static string? LeanProblem(string label, string text)
{
    const string keywords =
        "theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|macro|syntax|elab";
    const string modifiers = @"(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*";
    bool Declares(string name) => Regex.IsMatch(text,
        $@"(?m)^[ \t]*{modifiers}(?:{keywords})\s+(?:[\w'.]+\.)?{Regex.Escape(name)}(?![\w'.])");
    if (Declares(label)) return null;
    var split = label.LastIndexOf('.');
    if (split > 0 && Declares(label[(split + 1)..]) &&
        Regex.IsMatch(text, $@"(?m)^namespace\s+(?:[\w'.]+\.)?{Regex.Escape(label[..split])}\s*$"))
        return null;
    return "no Lean declaration has this name";
}

// `Type`, `Member` or `Type.Member`: the type must be declared, and the member declared with a return type.
static string? CSharpProblem(string label, string text)
{
    bool DeclaresType(string name) =>
        Regex.IsMatch(text, $@"\b(?:class|struct|record|interface|enum)\s+{Regex.Escape(name)}\b");
    var parts = label.Split('.');
    if (parts.Length > 2) return "a C# reference must be `Type`, `Member` or `Type.Member`";
    if (parts.Length == 2 && !DeclaresType(parts[0])) return $"no C# type `{parts[0]}` is declared";
    var member = parts[^1];
    if (parts.Length == 1 && DeclaresType(member)) return null;
    string[] statements = ["return", "new", "throw", "await", "else", "case", "yield", "in", "is", "not", "and", "or"];
    var declarations = Regex.Matches(text,
        $@"(?m)^[ \t]*(?<prefix>(?:[\w<>\[\],.?]+[ \t]+)+){Regex.Escape(member)}[ \t]*(?:<[^>\n]*>)?[ \t]*\(");
    return declarations.Any(declaration =>
        !statements.Contains(declaration.Groups["prefix"].Value.TrimEnd().Split(' ', '\t')[^1], StringComparer.Ordinal))
        ? null : $"no C# member `{member}` is declared";
}
