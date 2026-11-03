using System.Text;
using System.Text.RegularExpressions;

/// <summary>How a Lean code block in the documentation is checked; the info string after `lean` selects it.</summary>
enum SnippetKind
{
    /// <summary>No marker: elaborated after `import CIL` and its own imports, in a namespace of its own.</summary>
    Checked,
    /// <summary>`excerpt PATH`: every line, in order, begins a line of that verified repository file.</summary>
    Excerpt,
    /// <summary>`extracted`: needs a generated `Extracted` module; imports, commands and names are checked.</summary>
    Extracted,
    /// <summary>`illustrative`: a shape, not code; only its imports, commands and names are checked.</summary>
    Illustrative
}

/// <summary>A fenced Lean block: <c>Line</c> is the document line of its first code line.</summary>
sealed record LeanBlock(string Document, int Line, SnippetKind Kind, string? Source, string[] Lines);

/// <summary>A line of Markdown outside every fence.</summary>
sealed record ProseLine(string Document, int Line, string Text);

/// <summary>One parsed document: who reads it, its prose, its Lean blocks and any malformed markers.</summary>
sealed record DocumentPage(string Path, string Audience, ProseLine[] Prose, LeanBlock[] Blocks, string[] Problems);

/// <summary>Where a line of the generated snippet batch came from.</summary>
sealed record SnippetOrigin(string Document, int Line);

/// <summary>A generated Lean file, the origin of each line and how many snippets or names it holds.</summary>
sealed record SnippetBatch(string Text, SnippetOrigin?[] Origins, int Count);

/// <summary>
/// The documentation users and agents read (README, docs/, skills/) and the checks that keep its
/// citations, markers and Lean snippets in step with the repository.
/// </summary>
static partial class Documentation
{
    /// <summary>Documents for consumers of the tool and library; the default audience.</summary>
    internal const string Users = "users";

    /// <summary>Documents about LeanCIL's own implementation, validation and evidence.</summary>
    internal const string Maintainers = "maintainers";

    const string Repository = "https://github.com/NethermindEth/LeanCIL/";

    /// <summary>The documents under <paramref name="root"/>, in a stable order.</summary>
    internal static string[] Documents(string root) =>
        new[] { "docs", "skills" }.Select(folder => Path.Combine(root, folder)).Where(Directory.Exists)
            .SelectMany(folder => Directory.EnumerateFiles(folder, "*.md", SearchOption.AllDirectories))
            .Append(Path.Combine(root, "README.md")).Where(File.Exists)
            .Order(StringComparer.Ordinal).ToArray();

    internal static string Relative(string root, string path) => Path.GetRelativePath(root, path).Replace('\\', '/');

    /// <summary>Splits a document into prose and Lean blocks; fenced non-Lean code is neither.</summary>
    internal static DocumentPage Read(string root, string path)
    {
        var name = Relative(root, path);
        var lines = File.ReadAllLines(path);
        List<ProseLine> prose = [];
        List<LeanBlock> blocks = [];
        List<string> problems = [];
        string? audience = null;
        for (var index = 0; index < lines.Length; index++)
        {
            if (Patterns.Audience().Match(lines[index]) is { Success: true } declared)
            {
                if (audience is not null) problems.Add($"{name}:{index + 1}: a document declares one audience");
                audience = declared.Groups["value"].Value;
                if (audience is not (Users or Maintainers))
                    problems.Add($"{name}:{index + 1}: audience must be `{Users}` or `{Maintainers}`");
            }
            var open = Patterns.Fence().Match(lines[index]);
            if (!open.Success)
            {
                prose.Add(new(name, index + 1, lines[index]));
                continue;
            }
            var indent = open.Groups["indent"].Length;
            var fence = open.Groups["fence"].Value;
            var info = open.Groups["info"].Value.Trim().Split((char[])[' ', '\t'],
                StringSplitOptions.RemoveEmptyEntries);
            var first = index + 1;
            var end = first;
            while (end < lines.Length && !Closes(lines[end], fence)) end++;
            if (end == lines.Length) problems.Add($"{name}:{index + 1}: the code fence is never closed");
            // A variant spelling would otherwise hide a Lean block from every check.
            if (info.Length > 0 && info[0] != "lean" && info[0].StartsWith("lean", StringComparison.OrdinalIgnoreCase))
                problems.Add($"{name}:{index + 1}: write the Lean info string as `lean`, not `{info[0]}`");
            else if (info.Length > 0 && info[0] == "lean")
            {
                var code = lines[first..end].Select(line => Unindent(line, indent)).ToArray();
                var words = string.Join(' ', info[1..]);
                if (Marker(info[1..]) is { } marker)
                    blocks.Add(new(name, first + 1, marker.Kind, marker.Source, code));
                else
                    problems.Add($"{name}:{index + 1}: unknown Lean block marker `{words}`; {MarkerForms}");
            }
            index = end;
        }
        return new(path, audience ?? Users, prose.ToArray(), blocks.ToArray(), problems.ToArray());
    }

    static bool Closes(string line, string fence)
    {
        var trimmed = line.Trim();
        return trimmed.Length >= fence.Length && trimmed.All(character => character == fence[0]);
    }

    static string Unindent(string line, int indent)
    {
        var strip = 0;
        while (strip < indent && strip < line.Length && line[strip] is ' ' or '\t') strip++;
        return line[strip..];
    }

    // Markers are deliberately few, so every unelaborated block states why it is not elaborated.
    static (SnippetKind Kind, string? Source)? Marker(string[] words) => words switch
    {
        [] => (SnippetKind.Checked, null),
        ["excerpt", var source] => (SnippetKind.Excerpt, source),
        ["extracted"] => (SnippetKind.Extracted, null),
        ["illustrative"] => (SnippetKind.Illustrative, null),
        _ => null
    };

    /// <summary>A failure for each malformed marker, missing path, unshipped citation or stale excerpt.</summary>
    internal static (List<string> Failures, int References, int Blocks) CheckReferences(string root,
        IEnumerable<DocumentPage> pages)
    {
        var sources = new Dictionary<string, DeclarationSource>(StringComparer.Ordinal);
        var anchors = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        HashSet<string> AnchorsOf(string path) =>
            anchors.TryGetValue(path, out var known) ? known : anchors[path] = Anchors(path);
        var commands = Commands(root);
        List<string> failures = [];
        int references = 0, blocks = 0;
        foreach (var page in pages)
        {
            failures.AddRange(page.Problems);
            var userFacing = page.Audience == Users;
            foreach (var line in page.Prose)
            {
                var at = $"{line.Document}:{line.Line}";
                foreach (Match match in Patterns.LineCitation().Matches(line.Text))
                    failures.Add($"{at}: `{match.Value}` cites a source line; cite a declaration name");
                foreach (Match match in Patterns.AnyLink().Matches(line.Text))
                {
                    references++;
                    var target = match.Groups["target"].Value;
                    var hash = target.IndexOf('#');
                    var linked = hash == 0 ? page.Path : LinkedPath(root, page.Path, target);
                    if (linked is null) continue;
                    var relative = Relative(root, linked);
                    if (!linked.StartsWith(root, StringComparison.Ordinal) ||
                        !File.Exists(linked) && !Directory.Exists(linked))
                    {
                        failures.Add($"{at}: link target `{target}` does not exist");
                        continue;
                    }
                    if (userFacing && Unshipped(relative))
                        failures.Add($"{at}: `{target}`: {UnshippedReason}");
                    if (hash >= 0 && linked.EndsWith(".md", StringComparison.Ordinal) && File.Exists(linked) &&
                        !AnchorsOf(linked).Contains(target[(hash + 1)..]))
                        failures.Add($"{at}: `{target}` names no heading of {relative}");
                    if (Patterns.NamedLink().Match(match.Value) is { Success: true } named &&
                        Path.GetExtension(linked) is ".lean" or ".cs" && File.Exists(linked))
                    {
                        var label = named.Groups["label"].Value;
                        if (!sources.TryGetValue(linked, out var source))
                            sources[linked] = source = DeclarationSource.Read(linked);
                        if (Problem(label, linked, source) is { } problem)
                            failures.Add($"{at}: `{label}` -> {relative}: {problem}");
                    }
                }
                foreach (Match match in Patterns.CodeSpan().Matches(line.Text))
                {
                    var span = match.Groups["span"].Value;
                    if (Patterns.RepositoryPath().IsMatch(span))
                    {
                        references++;
                        var path = span.TrimEnd('/');
                        if (!File.Exists(Path.Combine(root, path)) && !Directory.Exists(Path.Combine(root, path)))
                            failures.Add($"{at}: `{span}` does not exist");
                    }
                    if (userFacing && (Unshipped(span) || Patterns.TestModule().IsMatch(span)))
                        failures.Add($"{at}: `{span}`: {UnshippedReason}");
                    if (Patterns.CommandSpan().Match(span) is { Success: true } command)
                    {
                        references++;
                        if (!commands.Contains(command.Value))
                            failures.Add($"{at}: `{command.Value}` {NotCommand}");
                    }
                }
            }
            foreach (var block in page.Blocks)
            {
                blocks++;
                failures.AddRange(CheckBlock(root, block, userFacing, commands));
            }
        }
        return (failures, references, blocks);
    }

    const string MarkerForms = "use none, `excerpt <path>`, `extracted` or `illustrative`";

    const string UnshippedReason =
        "Tests/ is not shipped; cite Examples/Proofs or a checked snippet, or address the document to maintainers";

    const string NotCommand = "is not a LeanCIL command, tactic or attribute";

    static string ModulePath(string module) => $"{module.Replace('.', '/')}.lean";

    // GitHub's heading anchors: lowercased, punctuation dropped, spaces to hyphens, repeats numbered.
    static HashSet<string> Anchors(string path)
    {
        var anchors = new HashSet<string>(StringComparer.Ordinal);
        foreach (var line in File.ReadLines(path))
        {
            if (Patterns.ExplicitAnchor().Match(line) is { Success: true } named)
                anchors.Add(named.Groups["name"].Value);
            if (Patterns.Heading().Match(line) is not { Success: true } heading) continue;
            var slug = Patterns.AnchorPunctuation().Replace(heading.Groups["text"].Value.Trim().ToLowerInvariant(), "")
                .Replace(' ', '-');
            var unique = slug;
            for (var repeat = 1; !anchors.Add(unique); repeat++) unique = $"{slug}-{repeat}";
        }
        return anchors;
    }

    // Tests/ holds the repository's regression fixtures; the tool ships CIL/ and Examples/ stays readable.
    static bool Unshipped(string relative) => relative.StartsWith("Tests/", StringComparison.Ordinal);

    // The local file a Markdown link names, or null for an anchor or an external site.
    static string? LinkedPath(string root, string document, string target)
    {
        var path = target.Split('#')[0];
        if (path.Length == 0 || path.StartsWith("mailto:", StringComparison.Ordinal)) return null;
        foreach (var form in new[] { "blob/main/", "tree/main/" })
            if (path.StartsWith(Repository + form, StringComparison.Ordinal))
                return Path.GetFullPath(Path.Combine(root, path[(Repository.Length + form.Length)..]));
        if (path.Contains("://", StringComparison.Ordinal)) return null;
        return Path.GetFullPath(Path.Combine(Path.GetDirectoryName(document)!, path));
    }

    static IEnumerable<string> CheckBlock(string root, LeanBlock block, bool userFacing, HashSet<string> commands)
    {
        var at = $"{block.Document}:{block.Line}";
        for (var offset = 0; offset < block.Lines.Length; offset++)
            if (Patterns.Import().Match(block.Lines[offset]) is { Success: true } import &&
                ImportProblem(root, import.Groups["module"].Value, block.Kind) is { } problem)
                yield return $"{block.Document}:{block.Line + offset}: {problem}";
        switch (block.Kind)
        {
            case SnippetKind.Checked when block.Lines.Any(line => Patterns.Extraction().IsMatch(StripComment(line))):
                yield return $"{at}: the block needs an extraction; mark it `excerpt <path>` or `extracted`";
                break;
            case SnippetKind.Excerpt:
                if (ExcerptProblem(root, block, userFacing) is { } problem) yield return $"{at}: {problem}";
                yield break;
        }
        for (var offset = 0; offset < block.Lines.Length; offset++)
            foreach (Match command in Patterns.Command().Matches(StripComment(block.Lines[offset])))
                if (!commands.Contains(command.Value))
                    yield return $"{block.Document}:{block.Line + offset}: `{command.Value}` {NotCommand}";
    }

    static string StripComment(string line) => line.Split("--")[0];

    // Snippets import the library, Lean's own modules and, with an extraction, its generated modules.
    static string? ImportProblem(string root, string module, SnippetKind kind)
    {
        if (module is "Lean" or "Std" || module.StartsWith("Lean.", StringComparison.Ordinal) ||
            module.StartsWith("Std.", StringComparison.Ordinal))
            return null;
        if (module is "Extracted" or "ExtractedSymbols")
            return kind == SnippetKind.Checked ? $"`import {module}` needs an extraction; mark the block" : null;
        if (module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal))
            return File.Exists(Path.Combine(root, ModulePath(module))) ? null
                : $"`import {module}` names no library module";
        return kind == SnippetKind.Excerpt ? null : $"`import {module}` is not a library module";
    }

    // Each excerpt line, in order, must begin a line of the source; elided lines are allowed.
    static string? ExcerptProblem(string root, LeanBlock block, bool userFacing)
    {
        var source = block.Source!;
        var path = Path.GetFullPath(Path.Combine(root, source));
        if (!path.StartsWith(root, StringComparison.Ordinal) || !File.Exists(path))
            return $"excerpt source `{source}` does not exist";
        if (userFacing && Unshipped(source)) return $"excerpt source `{source}`: {UnshippedReason}";
        var lines = File.ReadAllLines(path).Select(line => line.Trim()).ToArray();
        var next = 0;
        foreach (var excerpt in block.Lines.Select(line => line.Trim()).Where(line => line.Length != 0))
        {
            while (next < lines.Length && !lines[next].StartsWith(excerpt, StringComparison.Ordinal)) next++;
            if (next == lines.Length) return $"excerpt line `{excerpt}` is not in `{source}` after the previous ones";
            next++;
        }
        return null;
    }

    /// <summary>Every `bind_` and `cil_` command, tactic and attribute the library declares.</summary>
    internal static HashSet<string> Commands(string root)
    {
        var library = Path.Combine(root, "CIL");
        var names = new HashSet<string>(StringComparer.Ordinal);
        if (!Directory.Exists(library)) return names;
        foreach (var file in Directory.EnumerateFiles(library, "*.lean", SearchOption.AllDirectories))
            foreach (Match match in Patterns.DeclaredCommand().Matches(File.ReadAllText(file)))
                names.Add(match.Groups["name"].Value);
        return names;
    }

    /// <summary>One Lean file holding every checked snippet, each in a namespace of its own.</summary>
    internal static SnippetBatch Snippets(IEnumerable<DocumentPage> pages)
    {
        var batch = new BatchWriter();
        var checkedBlocks = pages.SelectMany(page => page.Blocks).Where(block => block.Kind == SnippetKind.Checked)
            .ToArray();
        var imports = checkedBlocks.SelectMany(block => block.Lines.Select((line, offset) =>
                (Module: Patterns.Import().Match(line).Groups["module"].Value,
                    Origin: new SnippetOrigin(block.Document, block.Line + offset))))
            .Where(import => import.Module is not ("" or "CIL")).DistinctBy(import => import.Module);
        batch.Emit("import CIL");
        foreach (var (module, origin) in imports) batch.Emit($"import {module}", origin);
        foreach (var block in checkedBlocks)
        {
            batch.Emit($"namespace DocSnippet{++batch.Count}");
            for (var offset = 0; offset < block.Lines.Length; offset++)
                batch.Emit(Patterns.Import().IsMatch(block.Lines[offset]) ? "" : block.Lines[offset],
                    new(block.Document, block.Line + offset));
            batch.Emit($"end DocSnippet{batch.Count}");
        }
        return batch.Finish();
    }

    /// <summary>
    /// One Lean file importing every library module and probing each `CIL.`-rooted name that prose and
    /// unelaborated blocks cite; a name that is a module or module folder of <paramref name="library"/>
    /// is not probed.
    /// </summary>
    internal static SnippetBatch Names(string library, IEnumerable<DocumentPage> pages)
    {
        var batch = new BatchWriter();
        var modules = Directory.EnumerateFiles(Path.Combine(library, "CIL"), "*.lean", SearchOption.AllDirectories)
            .Select(path => Path.ChangeExtension(Relative(library, path), null).Replace('/', '.'))
            .Prepend("CIL").Order(StringComparer.Ordinal);
        foreach (var module in modules) batch.Emit($"import {module}");
        foreach (var line in NameProbe.Split('\n')) batch.Emit(line);
        batch.Emit("namespace DocNames");
        foreach (var (name, origin) in CitedNames(library, pages.ToArray()))
        {
            batch.Emit($"#doc_name {name}", origin);
            batch.Count++;
        }
        batch.Emit("end DocNames");
        return batch.Finish();
    }

    sealed class BatchWriter
    {
        readonly StringBuilder text = new();
        readonly List<SnippetOrigin?> origins = [];
        internal int Count;

        internal void Emit(string line, SnippetOrigin? origin = null)
        {
            text.Append(line).Append('\n');
            origins.Add(origin);
        }

        internal SnippetBatch Finish() => new(text.ToString(), origins.ToArray(), Count);
    }

    // `CIL.`-rooted names outside checked blocks, minus module names; each with where it is cited.
    static IEnumerable<(string Name, SnippetOrigin Origin)> CitedNames(string root, DocumentPage[] pages)
    {
        var seen = new HashSet<(string, string, int)>();
        IEnumerable<(string Text, SnippetOrigin Origin)> Texts(DocumentPage page)
        {
            foreach (var line in page.Prose)
                foreach (Match span in Patterns.CodeSpan().Matches(line.Text))
                    yield return (span.Groups["span"].Value, new(line.Document, line.Line));
            foreach (var block in page.Blocks.Where(block => block.Kind is SnippetKind.Extracted
                         or SnippetKind.Illustrative))
                for (var offset = 0; offset < block.Lines.Length; offset++)
                    yield return (StripComment(block.Lines[offset]), new(block.Document, block.Line + offset));
        }
        foreach (var page in pages)
            foreach (var (text, origin) in Texts(page))
                foreach (Match match in Patterns.LibraryName().Matches(text))
                {
                    var name = match.Value;
                    if (File.Exists(Path.Combine(root, name)) ||
                        File.Exists(Path.Combine(root, ModulePath(name))) ||
                        Directory.Exists(Path.Combine(root, name.Replace('.', '/'))) ||
                        !seen.Add((name, origin.Document, origin.Line)))
                        continue;
                    yield return (name, origin);
                }
    }

    const string NameProbe = """
        open Lean Elab Command in
        /-- Fails unless the name is a constant or a namespace of the imported library. -/
        elab "#doc_name " name:ident : command => do
          let environment <- getEnv
          unless environment.contains name.getId || environment.isNamespace name.getId do
            throwErrorAt name m!"unknown library name {name.getId}"
        """;

    /// <summary>
    /// The diagnostics of an elaborated batch, each attributed to its document line; any error, warning or
    /// `sorryAx` fails. Diagnostics outside every snippet are reported against the batch itself.
    /// </summary>
    internal static List<string> Diagnostics(SnippetBatch batch, string batchPath, string output)
    {
        List<string> failures = [];
        var lines = output.ReplaceLineEndings("\n").Split('\n');
        for (var index = 0; index < lines.Length; index++)
        {
            var match = Patterns.Diagnostic().Match(lines[index]);
            if (!match.Success)
            {
                if (lines[index].Contains("sorryAx", StringComparison.Ordinal))
                    failures.Add($"a checked snippet depends on sorryAx: {lines[index].Trim()}");
                continue;
            }
            if (match.Groups["severity"].Value == "info") continue;
            var message = new StringBuilder(match.Groups["message"].Value);
            while (index + 1 < lines.Length && !Patterns.Diagnostic().IsMatch(lines[index + 1]) &&
                   lines[index + 1].Length != 0)
                message.Append("\n    ").Append(lines[++index]);
            var line = int.Parse(match.Groups["line"].Value) - 1;
            var origin = line >= 0 && line < batch.Origins.Length ? batch.Origins[line] : null;
            var at = origin is null ? $"{batchPath}:{line + 1}" : $"{origin.Document}:{origin.Line}";
            failures.Add($"{at}: {match.Groups["severity"].Value}: {message}");
        }
        return failures;
    }

    // Null when `label` is still present in `source`, otherwise why it is not.
    static string? Problem(string label, string target, DeclarationSource source)
    {
        if (label.Length > 1 && label[0] == '"' && label[^1] == '"')
            return source.Text.Contains(label, StringComparison.Ordinal) ? null
                : "the string literal is not in the file";
        if (label.Contains('/'))
            return target.Replace('\\', '/').EndsWith("/" + label, StringComparison.Ordinal)
                ? null : "a path label must name the linked file";
        if (!Patterns.DottedName().IsMatch(label))
            return "the label is neither a declaration name, a quoted string nor a path";
        return target.EndsWith(".lean", StringComparison.Ordinal) ? LeanProblem(label, source)
            : CSharpProblem(label, source);
    }

    // A Lean declaration of the full dotted name, or of its last component inside the namespace prefix.
    static string? LeanProblem(string label, DeclarationSource source)
    {
        if (EndsWithName(source.Declarations, label)) return null;
        var split = label.LastIndexOf('.');
        return split > 0 && EndsWithName(source.Declarations, label[(split + 1)..]) &&
            EndsWithName(source.Namespaces, label[..split]) ? null : "no Lean declaration has this name";
    }

    // `Type`, `Member` or `Type.Member`: the type must be declared, and the member declared with a return type.
    static string? CSharpProblem(string label, DeclarationSource source)
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
}

/// <summary>One documented source file and every name it declares, scanned once however many links cite it.</summary>
sealed record DeclarationSource(string Text, HashSet<string> Declarations, HashSet<string> Namespaces,
    HashSet<string> Types, HashSet<string> Members)
{
    static readonly string[] Statements =
        ["return", "new", "throw", "await", "else", "case", "yield", "in", "is", "not", "and", "or"];

    internal static DeclarationSource Read(string path)
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
    [GeneratedRegex(@"^<!--\s*audience:\s*(?<value>[\w-]+)\s*-->\s*$")]
    internal static partial Regex Audience();

    [GeneratedRegex(@"^(?<indent>[ \t]*)(?<fence>`{3,}|~{3,})(?<info>[^`]*)$")]
    internal static partial Regex Fence();

    [GeneratedRegex(@"\[(?:[^\[\]]|\[[^\]]*\])*\]\((?<target>[^)\s]+)\)")]
    internal static partial Regex AnyLink();

    [GeneratedRegex(@"^#{1,6}[ \t]+(?<text>.*?)[ \t#]*$")]
    internal static partial Regex Heading();

    [GeneratedRegex(@"[^\w\- ]")]
    internal static partial Regex AnchorPunctuation();

    [GeneratedRegex(@"<a\s+(?:id|name)=""(?<name>[^""]+)""")]
    internal static partial Regex ExplicitAnchor();

    [GeneratedRegex(@"\A\[`(?<label>[^`\]]+)`\]\(")]
    internal static partial Regex NamedLink();

    [GeneratedRegex(@"\[[^\]]*\.(?:lean|cs):\d[^\]]*\]\(|\]\([^)\s]*\.(?:lean|cs)#L\d")]
    internal static partial Regex LineCitation();

    [GeneratedRegex(@"`(?<span>[^`\n]+)`")]
    internal static partial Regex CodeSpan();

    // A repository path whose existence a reader relies on; build outputs and patterns are not paths.
    [GeneratedRegex(@"\A(?:CIL|Examples|Tests|scripts|docs|skills|Extractor)/" +
        @"(?!(?:.*/)?(?:bin|obj)/)[\w.-]+(?:/[\w.-]+)*/?\z")]
    internal static partial Regex RepositoryPath();

    [GeneratedRegex(@"\ATests\.[A-Z]\w*")]
    internal static partial Regex TestModule();

    [GeneratedRegex(@"\A(?:bind|cil)_\w+")]
    internal static partial Regex CommandSpan();

    [GeneratedRegex(@"(?<![\w.'])(?:bind|cil)_\w+")]
    internal static partial Regex Command();

    [GeneratedRegex(@"(?:""|register_simp_attr\s+|register_label_attr\s+)(?<name>(?:bind|cil)_\w+)")]
    internal static partial Regex DeclaredCommand();

    [GeneratedRegex(@"^\s*import\s+(?<module>[\w.]+)\s*$")]
    internal static partial Regex Import();

    [GeneratedRegex(@"\bExtracted(?:Symbols)?\.\w")]
    internal static partial Regex Extraction();

    [GeneratedRegex(@"(?<![\w.'])CIL(?:\.[A-Za-z_][\w'!?]*)+")]
    internal static partial Regex LibraryName();

    [GeneratedRegex(
        @"^(?<path>.+?):(?<line>\d+):(?<column>\d+): (?<severity>error|warning|info)(?:\([^)]*\))?: ?(?<message>.*)$")]
    internal static partial Regex Diagnostic();

    [GeneratedRegex(@"\A[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)*\z")]
    internal static partial Regex DottedName();

    [GeneratedRegex(@"(?m)^[ \t]*(?:@\[[^\]\n]*\]\s*)?" +
        @"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*" +
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
