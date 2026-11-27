using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;

// Binding schemas, verification reports, proof checking and observer source relocation.
partial class Program
{
    // Keeps the `#check` and `#print axioms` text shape that statement display reads; no decision reads it.
    static string AuditText(AuditedTheorem audited) => (audited.statement is null ? "" : audited.statement + "\n") +
        (audited.axioms is not { Length: > 0 } axioms ? $"'{audited.name}' does not depend on any axioms"
            : $"'{audited.name}' depends on axioms: [{string.Join(", ", axioms)}]") + "\n";

    /// <summary>An informational or warning message Lean reported while checking the selected proof.</summary>
    internal sealed record ProofMessage(string severity, int line, int column, string text);

    /// <summary>A method that a verified statement names through a framework predicate.</summary>
    internal sealed record StatementSubject(string role, string head, bool extracted, int? method, string? signature);

    /// <summary>A definition of the proof module as Lean prints it: `def name binders : type := body`.</summary>
    internal sealed record StatementDefinition(string name, string text);

    /// <summary>
    /// A verified statement as framework notation prints it, the methods it names and the proof module's
    /// definitions it is stated with, each before the ones its body uses; null when they were not read.
    /// </summary>
    internal sealed record StatementView(string statement, StatementSubject[] subjects,
        StatementDefinition[]? definitions = null);

    /// <summary>
    /// Set by callers that print <see cref="VerifiedStatement"/>; printing costs one Lean run beside the audit.
    /// </summary>
    bool viewsStatement { get; init; }

    /// <summary>
    /// Set by callers that read failure records: the proof is checked as <see cref="ObservedProof"/> with
    /// <see cref="DiagnosticsOption"/>, so each failure of a LeanCIL tactic is logged as a record after
    /// <see cref="FailureMarker"/>. The observer reads the elaborated proof and changes no proof term.
    /// </summary>
    bool structuredFailures { get; init; }

    /// <summary>The Lean option `cil.diagnostics`, which `CIL.Observe` reads.</summary>
    internal const string DiagnosticsOption = "-Dweak.cil.diagnostics=true";

    /// <summary>`CIL.Safety.failureMarker`, which starts each failure record the observer logs.</summary>
    internal const string FailureMarker = "[LeanCIL failure v1] ";

    /// <summary>
    /// Set by callers that print each step the proof takes: the proof is checked as <see cref="ObservedProof"/>
    /// with <see cref="TraceOption"/>.
    /// </summary>
    bool tracesSteps { get; init; }

    /// <summary>The Lean option tracing each step of the proof, as `[CIL.step]` messages of `CIL.Observe`.</summary>
    internal const string TraceOption = "-Dweak.trace.CIL.step=true";

    /// <summary>The start of a message of the `CIL.step` trace class.</summary>
    internal const string TraceHeader = "[CIL.step]";

    /// <summary>
    /// Set by callers that print open goals: the proof is checked as <see cref="ObservedProof"/> with
    /// <see cref="GoalsOption"/>, so the goal at each `sorry` and failing tactic is logged after
    /// <see cref="GoalMarker"/>.
    /// </summary>
    bool showsGoals { get; init; }

    /// <summary>The Lean option `cil.goals`, which `CIL.Observe` reads.</summary>
    internal const string GoalsOption = "-Dweak.cil.goals=true";

    /// <summary>`CIL.Safety.goalMarker`, which starts each open goal the observer logs.</summary>
    internal const string GoalMarker = "[LeanCIL goal v1] ";

    /// <summary>Whether the proof is checked as <see cref="ObservedProof"/>: records, a trace and goals need it.
    /// </summary>
    bool ObservesProof => structuredFailures || tracesSteps || showsGoals;

    /// <summary>The options the proof module is checked with: none unless asked for records, a trace or goals.
    /// </summary>
    string[] ProofOptions => [.. structuredFailures ? [DiagnosticsOption] : Array.Empty<string>(),
        .. tracesSteps ? [TraceOption] : Array.Empty<string>(), .. showsGoals ? [GoalsOption] : Array.Empty<string>()];

    /// <summary>The bytes the proof module is checked from: the developer's, or <see cref="ObservedProof"/>.</summary>
    byte[] CheckedProofBytes(byte[] source) => ObservesProof ? ObservedProof.Insert(source).Bytes : source;

    /// <summary>Binds a cached proof result to its options; empty for a default run, keeping its keys.</summary>
    string ProofOptionsKey => ProofOptions.Length == 0 ? "" : "\noptions " + string.Join(' ', ProofOptions);

    /// <summary>Messages from the last proof check, kept for display; no check reads them.</summary>
    internal ProofMessage[]? ProofMessages { get; private set; }

    /// <summary>The display form of the last verified statement; null when not printed.</summary>
    internal StatementView? VerifiedStatement { get; private set; }

    const string ProofMessagesFile = "Proof.messages.json";
    const string StatementViewFile = "Proof.statement.json";
    const string NamedErrorSuffix = "._namedError";

    /// <summary>
    /// Lean `--json` output rendered as Lean's plain text, with informational messages labelled
    /// `info:` at their position, and the non-error messages of `source`.
    /// </summary>
    static (string Text, ProofMessage[] Messages) LeanJsonMessages(string output, string source)
    {
        var text = new StringBuilder();
        var messages = new List<ProofMessage>();
        foreach (var line in output.ReplaceLineEndings("\n").Split('\n'))
        {
            JsonElement message;
            try { message = line.StartsWith('{') ? JsonSerializer.Deserialize<JsonElement>(line) : default; }
            catch (JsonException) { message = default; }
            if (message.ValueKind != JsonValueKind.Object || !message.TryGetProperty("severity", out var severity))
            {
                if (line.Length > 0) text.Append(line).Append('\n');
                continue;
            }
            var file = message.GetProperty("fileName").GetString() ?? "";
            var located = message.TryGetProperty("pos", out var position) && position.ValueKind == JsonValueKind.Object;
            var row = located ? position.GetProperty("line").GetInt32() : 1;
            var column = located ? position.GetProperty("column").GetInt32() : 0;
            var caption = message.TryGetProperty("caption", out var title) ? title.GetString() ?? "" : "";
            var data = message.GetProperty("data").GetString() ?? "";
            if (caption.Length > 0) data = caption + ":\n" + data;
            var kind = message.TryGetProperty("kind", out var tag) ? tag.GetString() ?? "" : "";
            var name = kind.EndsWith(NamedErrorSuffix, StringComparison.Ordinal)
                ? $"({kind[..^NamedErrorSuffix.Length]})" : "";
            var label = severity.GetString() switch { "error" => "error", "warning" => "warning", _ => "info" };
            text.Append($"{file}:{row}:{column}: {label}{name}: {data}");
            if (!data.EndsWith('\n')) text.Append('\n');
            if (label != "error" && file.Length > 0 &&
                LocationComparer.Equals(Path.GetFullPath(file, Path.GetDirectoryName(source)!), source))
                messages.Add(new(label, row, column, data.TrimEnd('\n')));
        }
        return (text.ToString(), [.. messages]);
    }

    /// <summary>
    /// The non-error messages of `source` in a Lake module trace: Lake checks the module with `lean --json`
    /// and logs each message as `file:line:column: text`, with `file` relative to `package`.
    /// </summary>
    static ProofMessage[] LakeTraceMessages(string trace, string package, string source)
    {
        JsonElement record;
        // Display only: an unreadable trace shows no messages rather than failing verification.
        try { record = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(trace)); }
        catch (Exception error) when (error is IOException or JsonException) { return []; }
        if (record.ValueKind != JsonValueKind.Object || !record.TryGetProperty("log", out var log) ||
            log.ValueKind != JsonValueKind.Array)
            return [];
        var entries = log.EnumerateArray()
            .Where(entry => entry.ValueKind == JsonValueKind.Object &&
                entry.TryGetProperty("level", out var level) && level.ValueKind == JsonValueKind.String &&
                entry.TryGetProperty("message", out var text) && text.ValueKind == JsonValueKind.String)
            .Select(entry => (entry.GetProperty("level").GetString()!, entry.GetProperty("message").GetString()!));
        return SourceMessages(entries, package, source);
    }

    /// <summary>The informational and warning entries located in `source`, in their logged order.</summary>
    static ProofMessage[] SourceMessages(IEnumerable<(string Level, string Message)> entries, string package,
        string source)
    {
        var messages = new List<ProofMessage>();
        foreach (var (level, text) in entries)
        {
            var label = level switch { "info" => "info", "warning" => "warning", _ => null };
            var located = LocatedMessage.Match(text);
            if (label is null || !located.Success ||
                !LocationComparer.Equals(Path.GetFullPath(located.Groups["file"].Value, package), source))
                continue;
            messages.Add(new(label, int.Parse(located.Groups["line"].Value),
                int.Parse(located.Groups["column"].Value), located.Groups["text"].Value.TrimEnd('\n')));
        }
        return [.. messages];
    }

    [GeneratedRegex(@"\A(?<file>[^\n]+?):(?<line>[0-9]+):(?<column>[0-9]+): (?<text>.*)\z", RegexOptions.Singleline)]
    private static partial Regex LocatedMessage { get; }

    static string LeanString(string value) => Nethermind.LeanCIL.IdentityText.Quote(value);

    /// <summary>
    /// Prints `theorem` from the checked proof module `olean` with only its imports' notation, writing the
    /// view to `directory`: the proof's own declarations are added without its extensions, so proof code
    /// cannot change the text. Display only; returns null when Lean cannot print it.
    /// </summary>
    StatementView? ViewStatement(string directory, string olean, string leanPath, string proofSource, string theorem)
    {
        var imports = SourceImport.Matches(proofSource).Select(import => import.Groups[1].Value)
            .Concat(["Lean", "Extracted", StatementModule]).Distinct(StringComparer.Ordinal);
        var source = Path.Combine(directory, "LeanCILStatement.lean");
        var result = Path.Combine(directory, StatementViewFile);
        File.WriteAllText(source, string.Concat(imports.Select(module => "import " + module + "\n")) + $$"""

            open Lean Meta Elab Command

            /-- A proof declaration for display, without the proof's extensions or kernel checking. -/
            def LeanCILStatement.declaration : ConstantInfo -> Declaration
              | .defnInfo value => .defnDecl value
              | info => .axiomDecl
                  { name := info.name, levelParams := info.levelParams, type := info.type, isUnsafe := false }

            /-- Positions of the `program : CIL.Program` and `method : Nat` binders of a head's type. -/
            def LeanCILStatement.positions : Expr -> Nat -> Option Nat -> Option Nat -> Option (Prod Nat Nat)
              | .forallE name type body _, index, program, method =>
                LeanCILStatement.positions body (index + 1)
                  (if name == `program && type == mkConst ``CIL.Program then some index else program)
                  (if name == `method && type == mkConst ``Nat then some index else method)
              | _, _, some program, some method => some (program, method)
              | _, _, _, _ => none

            /-- Methods that `expression` names through a framework head taking a program and method. -/
            def LeanCILStatement.methods (role : String) (expression : Expr) (table : Array String)
                (proof : NameSet) : MetaM (Array Json) := do
              let found <- IO.mkRef (#[] : Array Json)
              Meta.forEachExpr expression fun sub => do
                let .const head _ := sub.getAppFn | return
                if proof.contains head then return
                let some info := (<- getEnv).find? head | return
                let some (programAt, methodAt) := LeanCILStatement.positions info.type 0 none none | return
                let args := sub.getAppArgs
                unless programAt < args.size && methodAt < args.size do return
                let method := args[methodAt]!
                let index <- if method.hasLooseBVars then pure none else do
                  match <- whnf method with
                  | .lit (.natVal n) => pure (some n)
                  | reduced => evalNat reduced
                let extracted := args[programAt]!.consumeMData == mkConst `Extracted.program
                let signature := if extracted then index.bind (fun position => table[position]?) else none
                found.modify (fun entries => entries.push (Json.mkObj [("role", toJson role),
                  ("head", toJson head.toString), ("extracted", toJson extracted),
                  ("method", toJson index), ("signature", toJson signature)]))
              found.get

            /-- How many leading binders of `type` a printed signature names before its colon. -/
            def LeanCILStatement.namedBinders : Expr -> Nat
              | .forallE name _ body info =>
                if name.hasMacroScopes && !info.isInstImplicit then 0
                else LeanCILStatement.namedBinders body + 1
              | _ => 0

            /-- Whether `value` only projects a field of its argument, as a structure's accessor does. -/
            def LeanCILStatement.projects : Expr -> Bool
              | .lam _ _ body _ => LeanCILStatement.projects body
              | .proj .. => true
              | _ => false

            /-- The proof's definitions that `root` is stated with, each before those its body uses,
                printed as `def name binders : type := body` from its elaborated value. A structure's
                accessors are not listed: the statement names the structure and its fields. -/
            partial def LeanCILStatement.definitions (root : Expr) (proof : NameSet) :
                MetaM (Array Json) := do
              let seen <- IO.mkRef ({} : NameSet)
              let found <- IO.mkRef (#[] : Array Json)
              let rec visit (expression : Expr) : MetaM Unit := do
                for name in expression.getUsedConstants do
                  unless proof.contains name && !(<- seen.get).contains name do continue
                  seen.modify (fun names => names.insert name)
                  let some (.defnInfo definition) := (<- getEnv).find? name | continue
                  if name.isInternalDetail || LeanCILStatement.projects definition.value then continue
                  let named := LeanCILStatement.namedBinders definition.type
                  let signature <- PrettyPrinter.ppSignature name
                  let printed <- lambdaBoundedTelescope definition.value named fun binders body => do
                    if binders.size == named then
                      return f!"def {signature.fmt} :=" ++ Format.nest 2 (Format.line ++ (<- ppExpr body))
                    return f!"def {name} : {<- ppExpr definition.type} :=" ++
                      Format.nest 2 (Format.line ++ (<- ppExpr definition.value))
                  found.modify (fun entries => entries.push (Json.mkObj
                    [("name", toJson name.toString), ("text", toJson (toString printed.group))]))
                  visit definition.value
              visit root
              found.get

            #eval show CommandElabM Unit from do
              let (data, _) <- readModuleData {{LeanString(olean.Replace('\\', '/'))}}
              let mut env <- getEnv
              let mut proof : NameSet := {}
              for info in data.constants do
                unless env.contains info.name do
                  proof := proof.insert info.name
                  if let .ok next := env.addDeclCore 0 0 (LeanCILStatement.declaration info) none
                      (doCheck := false) then
                    env := next
              setEnv env
              let target := {{LeanString(theorem)}}.toName
              let result <- liftTermElabM do
                let statement <- PrettyPrinter.ppSignature target
                let some info := (<- getEnv).find? target | throwError "missing {target}"
                let table <- CIL.MethodIdentity.strings (mkConst `Extracted.signatures)
                forallTelescope info.type fun binders body => do
                  let mut subjects := #[]
                  for binder in binders do
                    subjects := subjects ++
                      (<- LeanCILStatement.methods "premise" (<- inferType binder) table proof)
                  subjects := subjects ++ (<- LeanCILStatement.methods "conclusion" body table proof)
                  return Json.mkObj [("statement", toJson (toString statement.fmt)),
                    ("subjects", toJson subjects),
                    ("definitions", toJson (<- LeanCILStatement.definitions info.type proof))]
              IO.FS.writeFile {{LeanString(result.Replace('\\', '/'))}} result.compress

            """);
        try
        {
            var printed = Execute([LeanExecutable, source], directory, leanPath);
            return printed.Code == 0 && File.Exists(result) ? ReadStatementView(result) : null;
        }
        finally { File.Delete(source); }
    }

    static StatementView? ReadStatementView(string path)
    {
        try { return JsonSerializer.Deserialize<StatementView>(File.ReadAllText(path)); }
        catch (Exception error) when (error is IOException or JsonException) { return null; }
    }

    // Every olean an audit may load from the session library and the proof directory.
    static SortedDictionary<string, string> OleanHashes(string fresh, string session)
    {
        var result = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var (name, hash) in ModuleArtifacts(session)) result["library:" + name] = hash;
        foreach (var path in Directory.EnumerateFiles(fresh, "*", SearchOption.AllDirectories)
            .Where(path => Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal)))
            result[Path.GetRelativePath(fresh, path).Replace('\\', '/')] = Sha(path);
        return result;
    }

    // An untrusted build may add only its own modules' oleans; any other change voids the replayed set.
    static void RequireOnlyAdded(SortedDictionary<string, string> bound, SortedDictionary<string, string> built,
        params string[] modules)
    {
        var permitted = modules.ToHashSet(StringComparer.Ordinal);
        bool Permitted(string artifact)
        {
            var marker = artifact.IndexOf(".olean", StringComparison.Ordinal);
            if (marker < 0) return false;
            var end = marker + ".olean".Length;
            return (end == artifact.Length || artifact[end] == '.') && permitted.Contains(artifact[..marker]);
        }
        if (bound.Any(pair => !built.TryGetValue(pair.Key, out var hash) || hash != pair.Value) ||
            built.Keys.Any(name => !bound.ContainsKey(name) && !Permitted(name)))
            throw new InvalidOperationException("Compiled artifacts changed during verification");
    }

    /// <summary>The version of the certificate `verified.json` holds; every reader rejects any other.</summary>
    internal const int CertificateSchema = 9;

    /// <summary>
    /// A fact the default verification trusts about the assembly images, which a deep check reconfirms from them.
    /// </summary>
    [JsonConverter(typeof(BindingFactNames))]
    internal enum BindingFact
    {
        /// <summary>Each body is the image's bytes at the offset the section table maps its MethodDef RVA to.
        /// </summary>
        BodyBytes,
        /// <summary>
        /// Each carried metadata block's table header, Assembly row, table rows and heap entries are the image's,
        /// with MethodDef RVAs zeroed, under one numbering of the #Strings and #Blob offsets per heap for the table
        /// rows and another for the Assembly row. The block's identity is its image's, its key token is computed
        /// from the image's public key, and its core library is a core-named AssemblyRef row of the image. Links,
        /// #GUID, the Module table and the RVAs of MethodDefs outside the evidence are not part of it.
        /// </summary>
        MetadataRows,
        /// <summary>
        /// Each carried MemberRef link names the definition its row resolves to: same kind, name and signature,
        /// declared by the parent type's definition in the pinned images.
        /// </summary>
        MemberLinks,
        /// <summary>Each platform type relied on is the value type, class or enum the extraction took it for.
        /// </summary>
        PlatformTypeKinds,
        /// <summary>Each platform enum relied on has the underlying type the extraction took.</summary>
        EnumUnderlyingTypes,
        /// <summary>Each value tuple relied on has the field order the extraction took.</summary>
        ValueTupleFieldOrder,
        /// <summary>`System.Object` has no instance fields.</summary>
        ObjectFields,
        /// <summary>The raw layouts are the contents of their TypeDefs.</summary>
        LayoutContent,
        /// <summary>Each dispatch catalog lists every class of the pinned images that reaches the slot.</summary>
        DispatchCatalogs,
        /// <summary>The RVA static field bytes are the image's.</summary>
        StaticData,
        /// <summary>The generic parameters and their constraints are the rows'.</summary>
        GenericConstraints,
        /// <summary>The AssemblyRef public key tokens are the tokens of the referenced images' keys.</summary>
        PublicKeyTokens,
        /// <summary>Each generic import identity names its pinned implementation definition.</summary>
        ImportIdentities,
        /// <summary>Each layout an import slot selected is the layout its implementation image defines.</summary>
        ImportedLayouts
    }

    /// <summary>What a run established about one binding fact.</summary>
    [JsonConverter(typeof(BindingStatusNames))]
    internal enum BindingStatus
    {
        /// <summary>The run relied on the fact without checking it; only a default run reports it.</summary>
        Trusted,
        /// <summary>A kernel-replayed, axiom-audited theorem states the fact for the pinned images.</summary>
        Reconfirmed,
        /// <summary>The run did not check the fact, for the reason it records.</summary>
        NotCovered,
        /// <summary>A check of the fact did not pass.</summary>
        Failed
    }

    /// <summary>Whether a run trusted the binding facts or ran the deep checks on them.</summary>
    [JsonConverter(typeof(BindingModeNames))]
    internal enum BindingMode
    {
        /// <summary>The run trusted every binding fact.</summary>
        Default,
        /// <summary>The run ran the deep checks.</summary>
        Deep
    }

    /// <summary>Reads and writes an enum as one exact name per value; any other token is a `JsonException`.</summary>
    abstract class ExactNames<T>(params (T Value, string Name)[] names) : JsonConverter<T> where T : struct, Enum
    {
        readonly Dictionary<string, T> values = names.ToDictionary(entry => entry.Name, entry => entry.Value,
            StringComparer.Ordinal);
        readonly Dictionary<T, string> texts = names.ToDictionary(entry => entry.Value, entry => entry.Name);

        public override T Read(ref Utf8JsonReader reader, Type typeToConvert, JsonSerializerOptions options) =>
            reader.TokenType == JsonTokenType.String && values.TryGetValue(reader.GetString()!, out var value) ? value
                : throw new JsonException($"a {typeof(T).Name} is one of {string.Join(", ", texts.Values)}");

        public override void Write(Utf8JsonWriter writer, T value, JsonSerializerOptions options) =>
            writer.WriteStringValue(texts[value]);
    }

    sealed class BindingFactNames() : ExactNames<BindingFact>(
        (BindingFact.BodyBytes, "body-bytes"), (BindingFact.MetadataRows, "metadata-rows"),
        (BindingFact.MemberLinks, "member-links"),
        (BindingFact.PlatformTypeKinds, "platform-type-kinds"),
        (BindingFact.EnumUnderlyingTypes, "enum-underlying-types"),
        (BindingFact.ValueTupleFieldOrder, "value-tuple-field-order"), (BindingFact.ObjectFields, "object-fields"),
        (BindingFact.LayoutContent, "layout-content"), (BindingFact.DispatchCatalogs, "dispatch-catalogs"),
        (BindingFact.StaticData, "static-data"), (BindingFact.GenericConstraints, "generic-constraints"),
        (BindingFact.PublicKeyTokens, "public-key-tokens"), (BindingFact.ImportIdentities, "import-identities"),
        (BindingFact.ImportedLayouts, "imported-layouts"));

    sealed class BindingStatusNames() : ExactNames<BindingStatus>((BindingStatus.Trusted, "trusted"),
        (BindingStatus.Reconfirmed, "reconfirmed"), (BindingStatus.NotCovered, "not covered"),
        (BindingStatus.Failed, "failed"));

    sealed class BindingModeNames() : ExactNames<BindingMode>((BindingMode.Default, "default"),
        (BindingMode.Deep, "deep"));

    /// <summary>Why a deep run read an assembly image.</summary>
    [JsonConverter(typeof(ImageRoleNames))]
    internal enum ImageRole
    {
        /// <summary>An assembly `identity.json` pins: the selected assembly or one it references.</summary>
        Pinned,
        /// <summary>A platform reference assembly a binding fact's claims name.</summary>
        Platform,
        /// <summary>An additional image whose definition key is compared with a direct AssemblyRef.</summary>
        Reference,
        /// <summary>An image of the digest file that no pin and no claim names.</summary>
        Unused
    }

    sealed class ImageRoleNames() : ExactNames<ImageRole>((ImageRole.Pinned, "pinned"),
        (ImageRole.Platform, "platform"), (ImageRole.Reference, "reference"), (ImageRole.Unused, "unused"));

    /// <summary>The digest file a deep run read, by its path and its own SHA-256.</summary>
    internal sealed record DigestFile([property: JsonRequired] string path, [property: JsonRequired] string sha256);

    /// <summary>The sources a deep run's statements were checked with: StrictBinding's key and the Lean toolchain.
    /// </summary>
    internal sealed record StatementSources([property: JsonRequired] string strictBinding,
        [property: JsonRequired] string leanToolchain, [property: JsonRequired] string lean);

    /// <summary>
    /// One image a deep run read: its display identity, SHA-256, role and status, with the theorem that reconfirmed
    /// its digest or why it is not covered.
    /// </summary>
    internal sealed record ImageResult([property: JsonRequired] string identity,
        [property: JsonRequired] string sha256, [property: JsonRequired] ImageRole role,
        [property: JsonRequired] BindingStatus status, string? theorem, string? reason);

    /// <summary>One binding fact's status, with the theorem that reconfirmed it or why it is not covered.</summary>
    internal sealed record BindingFactResult([property: JsonRequired] BindingFact id,
        [property: JsonRequired] BindingStatus status, string? theorem, string? reason);

    /// <summary>
    /// The binding section of a certificate: the run's mode, the digest file, statement sources and images a deep
    /// run read, and the status of every binding fact, each listed once, in the order `BindingFact` declares them.
    /// </summary>
    internal sealed record BindingSection([property: JsonRequired] BindingMode mode,
        [property: JsonRequired] DigestFile? digests, [property: JsonRequired] StatementSources? sources,
        [property: JsonRequired] ImageResult[] images,
        [property: JsonRequired] BindingFactResult[] facts)
    {
        /// <summary>The section of a default run, which reads no image and trusts every fact.</summary>
        internal static BindingSection Default => new(BindingMode.Default, null, null, [],
            [.. Enum.GetValues<BindingFact>().Select(fact => new BindingFactResult(fact, BindingStatus.Trusted,
                null, null))]);
    }

    /// <summary>
    /// Why `binding` is not the section of a certificate that a run of mode `required` accepts, or null when it
    /// is: every fact once and in order; in a default run no digest file, sources or image and every fact
    /// trusted; in a deep one the digest file and sources named and each fact and image reconfirmed with its
    /// theorem or not covered with its reason.
    /// </summary>
    static string? BindingProblem(BindingSection? binding, BindingMode required)
    {
        if (binding?.facts is not { } facts || binding.images is not { } images) return "it has no binding section";
        if (binding.mode != required)
            return $"its binding section is from a {binding.mode} run, and this run accepts only {required}";
        if (required == BindingMode.Default
            ? binding.digests is not null || binding.sources is not null || images.Length != 0
            : binding.digests is null || string.IsNullOrWhiteSpace(binding.digests.path) ||
                !Sha256Text(binding.digests.sha256) || binding.sources is null ||
                string.IsNullOrWhiteSpace(binding.sources.leanToolchain) ||
                !Sha256Text(binding.sources.strictBinding) || !Sha256Text(binding.sources.lean) ||
                images.Any(image => image is null || string.IsNullOrWhiteSpace(image.identity) ||
                    !Sha256Text(image.sha256) || !Settled(image.status, image.theorem, image.reason)))
            return $"its binding section's digest file, sources or images do not fit a {required} run";
        var declared = Enum.GetValues<BindingFact>().Select(fact => (BindingFact?)fact);
        if (!facts.Select(fact => fact?.id).SequenceEqual(declared))
            return "its binding section does not list every binding fact once, in order";
        var wrong = facts.FirstOrDefault(fact => required == BindingMode.Default
            ? fact.status != BindingStatus.Trusted || fact.theorem is not null || fact.reason is not null
            : !Settled(fact.status, fact.theorem, fact.reason));
        return wrong is null ? null
            : $"its binding fact {wrong.id} is {wrong.status} with theorem {wrong.theorem ?? "none"} and reason " +
                $"{wrong.reason ?? "none"}, which a {required} run does not issue";
    }

    /// <summary>Whether a digest contains exactly the 64 hexadecimal digits of a SHA-256 value.</summary>
    static bool Sha256Text(string? digest) => digest is { Length: 64 } && digest.All(char.IsAsciiHexDigit);

    /// <summary>
    /// Whether a deep run's verified certificate can report this outcome: reconfirmed by a named theorem, or not
    /// covered for a stated reason.
    /// </summary>
    static bool Settled(BindingStatus status, string? theorem, string? reason) => status switch
    {
        BindingStatus.Reconfirmed => !string.IsNullOrWhiteSpace(theorem) && reason is null,
        BindingStatus.NotCovered => !string.IsNullOrWhiteSpace(reason) && theorem is null,
        _ => false
    };

    /// <summary>
    /// The certificate `text` holds when a run of mode `required` accepts it; otherwise null, with `problem`
    /// saying why. A certificate of another schema, mode or fact list is never read.
    /// </summary>
    static Report? ReadCertificate(string text, BindingMode required, out string? problem)
    {
        Report? report;
        try { report = JsonSerializer.Deserialize<Report>(text); }
        catch (JsonException error)
        {
            problem = "it is not a certificate: " + error.Message;
            return null;
        }
        problem = report is null ? "it is empty"
            : report.schema != CertificateSchema ? $"its schema is {report.schema}, not {CertificateSchema}"
            : BindingProblem(report.binding, required);
        return problem is null ? report : null;
    }

    /// <summary>Why `text` is not a certificate a run of mode `required` accepts, or null when it is.</summary>
    internal static string? CertificateProblem(string text, BindingMode required)
    {
        ReadCertificate(text, required, out var problem);
        return problem;
    }

    sealed record Report(int schema, string assemblySha256, string identitySha256, string theorem, string[] axioms,
        string theoremAudit, SortedDictionary<string, string> inputs, BindingSection binding,
        string? libraryKey = null, string? libraryBuild = null,
        string? extractionAudit = null, string[]? initializedTypes = null,
        string? batchSourceSha256 = null, string? batchTheorem = null, string? consumerSupportSha256 = null,
        string[]? staticValues = null, string[]? contractImports = null, PublishedImport[]? imports = null,
        DeploymentDependency[]? contractDependencies = null, string? compositionTheorem = null, string? compositionAudit = null,
        JsonElement[]? initializationAssumptions = null, string[]? opaqueStaticValues = null,
        StatementDefinition[]? specification = null, string[]? libraryModules = null,
        StatementIdentity? statementIdentity = null, VerifiedRefutation? refutation = null);

    static JsonElement[] InitializationAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("initializationAssumptions", out var assumptions)
            ? assumptions.EnumerateArray().ToArray() : [];

    static string[] StaticValueAssumptions(JsonElement extraction) =>
        extraction.TryGetProperty("staticValues", out var values) ? values.Deserialize<string[]>() ?? [] : [];

    // Fields the theorem reads from the caller's static bindings instead of a computed constant.
    static string[] OpaqueStaticValues(JsonElement extraction) =>
        extraction.TryGetProperty("opaqueStaticValues", out var values) ? values.Deserialize<string[]>() ?? [] : [];

    /// <summary>The module the statement display imports beside the proof's own imports.</summary>
    const string StatementModule = "CIL.MethodIdentity";

    /// <summary>
    /// Every module that single-file verification of this proof compiles against or loads: the imports of the
    /// proof, of the extraction and of its symbols, the statement display's, and the observer, which the proof
    /// is checked against under `--goals`, so the closure is the same with it. Null when the proof needs the
    /// whole library: contract imports, a full-import audit, or an import that is neither the extraction nor
    /// a framework module.
    /// </summary>
    string[]? ClosureRoots(string proofSource, string output, string? symbolsSource, ExtractionIdentity extraction)
    {
        if (!importClosureFirst || fullImportAudit is not null || forceFullVerification ||
            extraction.Sources.Count > 0 || HasContractImports(extraction)) return null;
        static IEnumerable<string> Imports(string source) =>
            SourceImport.Matches(source).Select(import => import.Groups[1].Value);
        var proofImports = Imports(proofSource).ToArray();
        static bool Generated(string module) =>
            module is "Extracted" or "ExtractedSymbols" || SelectionModules.Is(module);
        if (proofImports.Any(module => !Generated(module) && !IsFrameworkModule(module) &&
                module.Split('.')[0] is not ("Init" or "Lean" or "Std")))
            return null;
        return [.. proofImports.Concat(Imports(File.ReadAllText(Path.Combine(output, "Extracted.lean"))))
            .Concat(symbolsSource is null ? [] : Imports(File.ReadAllText(symbolsSource)))
            .Concat([StatementModule, ObservedProof.Module]).Where(IsFrameworkModule).Distinct(StringComparer.Ordinal)];
    }

    Report Verify(string assembly, string identity, string entry, string proof, string output,
        string profile = "scalar", string theorem = "ExampleProof.correctness", bool check = false, bool existingArtifacts = false,
        string? settings = null, Action<string>? stage = null, DeepCheckInputs? deepChecks = null,
        DeepCheckRun? deepRun = null, Func<Sha256Digest, Sha256Digest>? receiveDigest = null,
        StatementRequest? statement = null, Action<string>? onCleanExtractionCompiled = null)
    {
        Sha256Digest RunCheck(string[] command) => CheckManifest(command, receiveDigest);
        deepRun = DeepCheckRun.Claim(deepChecks, deepRun);
        assembly = Path.GetFullPath(assembly);
        proof = Path.GetFullPath(proof);
        output = Path.GetFullPath(output);

        if (!Regex.IsMatch(theorem, @"\A[A-Za-z_][A-Za-z0-9_.]*\z"))
            throw new ArgumentException("Invalid theorem name");

        Directory.CreateDirectory(output);

        var reportPath = Path.Combine(output, "verified.json");

        if (check && deepChecks is null && statement is null)
        {
            var old = ReadCertificate(File.ReadAllText(reportPath), BindingMode.Default, out var problem) ??
                throw new InvalidOperationException("Stale verification report: " + problem);
            var accepted = RunCheck(Extract("check", assembly, identity, entry, output, profile));

            if (string.IsNullOrWhiteSpace(old.extractionAudit) || !Same(old.inputs, Inputs(proof, settings)) ||
                old.identitySha256 != accepted.ToString() ||
                old.theorem != theorem || old.assemblySha256 != Sha(assembly) ||
                (old.batchSourceSha256 is not null && (string.IsNullOrWhiteSpace(old.batchTheorem) ||
                    old.batchSourceSha256 != Sha(Path.Combine(output, "Batch.lean")))))
                throw new InvalidOperationException("Stale verification report or changed proof inputs");

            return old;
        }

        // A failed attempt must not leave an earlier successful report behind.
        File.Delete(reportPath);
        ProofMessages = null;
        VerifiedStatement = null;
        stage?.Invoke("extraction integrity");
        string[] checkCommand = existingArtifacts ? ["dotnet", ExtractorPath, "check", output]
            : Extract("check", assembly, identity, entry, output, profile);
        Sha256Digest? initialDigest = existingArtifacts ? RunCheck(checkCommand) : null;
        if (!existingArtifacts)
        {
            EnsureExtractorBuilt();
            Run(Extract("extract", assembly, identity, entry, output, profile));
        }
        byte[] proofSourceBytes = File.ReadAllBytes(proof);
        string proofSourceHash = Convert.ToHexStringLower(SHA256.HashData(proofSourceBytes));
        string proofSource;
        using (StreamReader reader = new(new MemoryStream(proofSourceBytes)))
        {
            proofSource = reader.ReadToEnd();
        }
        bool symbols = ImportsSymbols(proofSource);
        string? symbolsSource = symbols ? SymbolsFor(output) : null;
        byte[]? symbolsSourceBytes = symbolsSource is null ? null : File.ReadAllBytes(symbolsSource);
        string? symbolsSourceHash = symbolsSourceBytes is null ? null : Convert.ToHexStringLower(SHA256.HashData(symbolsSourceBytes));
        var before = Inputs(proof, settings);
        if (before["proof:" + proof] != proofSourceHash)
            throw new InvalidOperationException("Proof inputs changed before their source snapshot");
        ExtractionIdentity extraction = ExtractionIdentity.Read(output);
        if (initialDigest is { } acceptedDigest) extraction.RequireDigest(acceptedDigest);
        Sha256Digest RecheckManifest()
        {
            var digest = RunCheck(checkCommand);
            extraction.RequireDigest(digest);
            return digest;
        }
        referenceOnlyAuthoring = ReferenceOnlyImports(extraction);
        string[] selected = SelectionModules.Selected(
            SourceImport.Matches(proofSource).Select(import => import.Groups[1].Value), extraction.Root, proof);
        IReadOnlyList<DeepCheckInputs.Pin>? matchedPins = null;
        if (deepRun is not null)
        {
            stage?.Invoke("arguments");
            matchedPins = deepRun.Begin(extraction);
        }

        // Retain the selected bytes before support or interface builds can run code.
        void RequireOriginalProofSources()
        {
            if (!File.Exists(proof) || Sha(proof) != proofSourceHash ||
                symbolsSource is not null && (!File.Exists(symbolsSource) || Sha(symbolsSource) != symbolsSourceHash))
                throw new InvalidOperationException("Proof inputs changed during verification");
        }

        // Use a source-bound build; CI and --rebuild-library bypass the local library cache.
        stage?.Invoke("Lean library build");
        // A closure entry holds no StrictBinding build, so deep checks open the whole library.
        var closureRoots = deepChecks is null ? ClosureRoots(proofSource, output, symbolsSource, extraction) : null;
        var session = Library(before, closureRoots: closureRoots);
        if (deepChecks is not null) PrepareBindingLibrary(session);
        void RequireDeepBindingStable()
        {
            if (deepChecks is not null) RequirePreparedBindingLibrary();
        }
        RequireReplayedImports(closureRoots ?? []);
        HashSet<string> importSourceNames = extraction.Sources.Keys.ToHashSet(StringComparer.Ordinal);
        var support = Regex.Matches(proofSource, @"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", RegexOptions.Multiline)
            .Select(m => m.Groups[1].Value)
            .Where(n => n is not ("Extracted" or "ExtractedSymbols") && !SelectionModules.Is(n) &&
                !importSourceNames.Contains(n) && n.Split('.')[0] is not ("Init" or "Lean" or "Std")).ToArray();

        if (support.Length > 0)
        {
            // Lean's dependency query supplies the import closure. When dependencies
            // are not built yet, a conservative source snapshot safely widens the key.
            var supportSources = SupportInputs(session, support, before);
            var supportKey = ContentKey("support-audit-v1\n" + VerificationPolicy + "\n" + libraryKey + "\n" +
                extraction.Sha256 + "\n" +
                string.Join("\n", support.Order(StringComparer.Ordinal)) + "\n" + JsonSerializer.Serialize(supportSources));
            if (!preparedSupport.Contains(supportKey))
            {
                var staging = Path.Combine(Path.GetTempPath(), "leancil-support-" + Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(staging);
                try
                {
                    if (RestoreSuccess(supportKey, staging))
                    {
                        var restored = ModuleArtifacts(staging);
                        CopyTree(staging, session);
                        RequireDeepBindingStable();
                        foreach (var (name, hash) in restored) certifiedModules![name] = hash;
                        supportCacheHits++;
                        CacheProgress("certified dependencies: " + entry);
                    }
                    else
                    {
                        Run(["lake", "build", .. support], session, progress: "Building proof dependencies: " + entry);
                        RequireDeepBindingStable();
                        var current = SessionModules(session);
                        var altered = certifiedModules!.Any(pair => !current.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
                        var changed = (altered ? current : current.Where(pair => !certifiedModules!.ContainsKey(pair.Key)))
                            .Select(pair => ModuleName(pair.Key)).Distinct().ToArray();
                        if (changed.Length > 0)
                        {
                            stage?.Invoke("kernel replay");
                            Run([Path.Combine(Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker"), .. changed],
                                leanPath: SessionLeanPath(session), progress: "Kernel replay of proof dependencies: " + entry);
                        }
                        RequireDeepBindingStable();
                        certifiedModules = current;
                        CopySupportArtifacts(session, staging, supportSources);
                        PublishSuccess(supportKey, staging);
                    }
                }
                finally { Directory.Delete(staging, true); }
                preparedSupport.Add(supportKey);
            }
        }
        RequireDeepBindingStable();

        RequireOriginalProofSources();

        // Isolate generated code and the selected proof, then audit the named theorem.
        var fresh = Path.Combine(output, "proof-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(fresh);
        string audit;
        VerifiedRefutation? refutation;
        string extractionAudit = "";
        string[] axioms;
        FullImportResult? fullResult = null;
        string stagedProof = Path.Combine(fresh, "Proof.lean");
        string stagedSymbols = Path.Combine(fresh, "ExtractedSymbols.lean");
        // Diagnostics in these copies cite the files they were copied from.
        var copies = new SourceCopies(fresh);
        byte[] stagedProofBytes = CheckedProofBytes(proofSourceBytes);
        string stagedProofHash = Convert.ToHexStringLower(SHA256.HashData(stagedProofBytes));
        void RequireStagedProofSources()
        {
            if (!File.Exists(stagedProof) || Sha(stagedProof) != stagedProofHash)
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (symbols && (!File.Exists(stagedSymbols) || Sha(stagedSymbols) != symbolsSourceHash))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
        }

        try
        {
            File.Copy(Path.Combine(output, "Extracted.lean"), Path.Combine(fresh, "Extracted.lean"));
            if (Sha(Path.Combine(fresh, "Extracted.lean")) != extraction.GeneratedSha256)
                throw new InvalidOperationException("Inputs changed during verification");
            copies.Add(Path.Combine(fresh, "Extracted.lean"), Path.Combine(output, "Extracted.lean"));
            string[] importModules = StageImportSources(extraction, fresh);
            var leanPath = fresh + Path.PathSeparator + SessionLeanPath(session);

            var currentModules = SessionModules(session);
            var alteredExisting = certifiedModules!.Any(pair => !currentModules.TryGetValue(pair.Key, out var hash) || hash != pair.Value);
            var changedModules = (alteredExisting ? currentModules.Keys : currentModules.Keys.Where(name => !certifiedModules!.ContainsKey(name)))
                .Select(ModuleName).Distinct().ToArray();
            if (changedModules.Length > 0)
            {
                stage?.Invoke("kernel replay");
                ReplayCheckedModules(changedModules, leanPath, "Kernel replay of proof dependencies: " + entry);
                RequireDeepBindingStable();
                certifiedModules = currentModules;
            }
            RequireDeepBindingStable();
            // Full artifact identities include transitive support dependencies and every
            // olean part. Cached success is never inferred from an unsigned manifest.
            var environmentKey = StandaloneEnvironmentKey(libraryKey!, currentModules);
            var extractionSuffix = "\n" + Sha(Path.Combine(fresh, "Extracted.lean"));
            var extractedKey = StandaloneExtractionKey(environmentKey, extractionSuffix);
            string? extractionPublication = null;
            bool cleanExtractionCompiled = false;
            if (RestoreSuccess(extractedKey, fresh))
            {
                extractionCacheHits++;
                CacheProgress("certified extraction: " + entry);
            }
            else
            {
                // The native audit checks this theorem's exact type after independent kernel replay.
                stage?.Invoke("proof checking");
                var diagnostics = Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "Extracted.olean"),
                    Path.Combine(fresh, "Extracted.lean")], leanPath: leanPath, progress: "Checking Extracted: " + entry);
                cleanExtractionCompiled = onCleanExtractionCompiled is not null &&
                    !diagnostics.Contains("sorryAx", StringComparison.Ordinal);
                var publication = Path.Combine(fresh, "extraction-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Extracted.olean", StringComparison.Ordinal)))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                extractionPublication = publication;
            }
            var bound = OleanHashes(fresh, session);
            Dictionary<string, AuditedClosure>? checkedClosures = deepChecks is null ? null : [];
            // Interfaces, symbols and the proof each run code when built: each build may add only its own oleans.
            // A keyed module only re-exports its plain one, which is what the audits below read.
            void BuildSelected(bool symbolsModules)
            {
                foreach (var module in selected.Where(module => SelectionModules.IsSymbols(module) == symbolsModules))
                {
                    var path = Path.Combine(fresh, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                    File.WriteAllText(path, SelectionModules.Source(module));
                    Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(path, ".olean"), path],
                        leanPath: leanPath, progress: "Checking " + module);
                    var next = OleanHashes(fresh, session);
                    RequireOnlyAdded(bound, next, module.Replace('.', '/'));
                    bound = next;
                }
            }
            BuildSelected(symbolsModules: false);
            foreach (string module in importModules.Where(module => module != "ExtractedImports"))
            {
                string source = Path.Combine(fresh, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(source, ".olean"), source], leanPath: leanPath,
                    progress: "Checking contract interface: " + module);
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, module.Replace('.', '/'));
                bound = next;
            }
            if (importModules.Contains("ExtractedImports", StringComparer.Ordinal))
            {
                string assumptionsSource = Path.Combine(fresh, "ExtractedImports.lean");
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.ChangeExtension(assumptionsSource, ".olean"), assumptionsSource],
                    leanPath: leanPath, progress: "Checking App import assumptions");
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, "ExtractedImports");
                bound = next;
            }
            // The audit, the replay and the proof must all read the bytes compiled here.
            SortedDictionary<string, string> acceptedInterfaceArtifacts = ContractInterfaceArtifacts(fresh, importModules);
            if (importModules.Length > 0)
            {
                stage?.Invoke("kernel replay");
                string InterfaceArtifact(string module) => Path.Combine(fresh, module.Replace('.', '/') + ".olean");
                if (!TryReplayContractInterfaces(extraction, importModules, leanPath, InterfaceArtifact, checkedClosures))
                {
                    ReplayCheckedModules(importModules, leanPath,
                        "Kernel replay of published contract interfaces and App import assumptions");
                    CheckContractInterfaces(extraction, importModules, leanPath, InterfaceArtifact, checkedClosures: checkedClosures);
                }
                if (!Same(bound, OleanHashes(fresh, session)))
                    throw new InvalidOperationException("Compiled artifacts changed during verification");
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            }
            DeepSessionContribution? deep = null;
            if (deepChecks is not null)
            {
                stage?.Invoke("deep checks");
                deep = BuildDeepSession(fresh, leanPath, Path.Combine(fresh, "Extracted.olean"),
                    extraction, matchedPins!, () => stage?.Invoke("deep-check sources"), extractedKey, checkedClosures);
                if (deep.Restored)
                {
                    deepCacheHits++;
                    CacheProgress("certified deep checks: " + entry);
                }
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next,
                    [.. deep.Modules.Where(module => module != "Extracted")
                        .Select(module => module.Replace('.', '/'))]);
                bound = next;
            }
            if (File.Exists(stagedProof))
                throw new InvalidOperationException("Proof sources changed during verification: Proof.lean");
            if (File.Exists(stagedSymbols))
                throw new InvalidOperationException("Proof sources changed during verification: ExtractedSymbols.lean");
            RequireOriginalProofSources();
            File.WriteAllBytes(stagedProof, stagedProofBytes);
            if (symbols) File.WriteAllBytes(stagedSymbols, symbolsSourceBytes!);
            RequireStagedProofSources();
            if (ObservesProof) copies.AddObserved(stagedProof, proof);
            else copies.Add(stagedProof, proof);
            if (symbols) copies.Add(stagedSymbols, symbolsSource!);
            if (symbols)
            {
                Run([LeanExecutable, "--root=" + fresh, "-o", Path.Combine(fresh, "ExtractedSymbols.olean"), stagedSymbols],
                    leanPath: leanPath, progress: "Checking ExtractedSymbols: " + entry);
                var next = OleanHashes(fresh, session);
                RequireOnlyAdded(bound, next, "ExtractedSymbols");
                bound = next;
                BuildSelected(symbolsModules: true);
                RequireStagedProofSources();
            }
            RequireStagedProofSources();
            // Cached proofs carry their Lean messages and statement display.
            var proofSuffix = "\n" + proofSourceHash + "\n" +
                (symbols ? symbolsSourceHash + "\n" : "") +
                SemanticExtractionIdentity(extraction) + "\n" + JsonSerializer.Serialize(extraction.Sources) + "\n" +
                JsonSerializer.Serialize(acceptedInterfaceArtifacts) + "\n" + theorem + ProofOptionsKey;
            var proofKey = StandaloneProofKey(extractedKey, proofSuffix);
            var proofRestored = RestoreSuccess(proofKey, fresh);
            if (proofRestored)
            {
                proofCacheHits++;
                CacheProgress("certified proof: " + entry);
                var cachedMessages = Path.Combine(fresh, ProofMessagesFile);
                ProofMessages = copies.Relocate(proof, File.Exists(cachedMessages)
                    ? JsonSerializer.Deserialize<ProofMessage[]>(File.ReadAllText(cachedMessages)) : null);
            }
            else
            {
                stage?.Invoke("proof checking");
                RequireStagedProofSources();
                string[] command = [LeanExecutable, "--json", .. ProofOptions, "--root=" + fresh, "-o",
                    Path.Combine(fresh, "Proof.olean"), stagedProof];
                var checkedProof = Execute(command, leanPath: leanPath, progress: "Checking Proof: " + entry);
                var (transcript, messages) = LeanJsonMessages(checkedProof.Output, stagedProof);
                ProofMessages = copies.Relocate(proof, messages);
                if (checkedProof.Code != 0)
                    throw new InvalidOperationException(
                        $"Command failed ({checkedProof.Code}): {string.Join(' ', command)}\n{transcript}");
                File.WriteAllText(Path.Combine(fresh, ProofMessagesFile), JsonSerializer.Serialize(messages));
            }
            RequireStagedProofSources();
            var built = OleanHashes(fresh, session);
            void RequireDeepStable(bool checkLibraryContents = false)
            {
                if (deep is null) return;
                var checkedLibrary = checkLibraryContents ? CheckCertifiedLibraryContents() : null;
                deep.RequireStable();
                if (!Same(built, OleanHashes(fresh, session)) ||
                    bindingSourcesKey != BindingSourcesKey(library!) ||
                    bindingPreparation!.Toolchain != BindingToolchainKey(session))
                    throw new InvalidOperationException("Deep-check sources, toolchain or compiled artifacts changed");
                RequirePreparedBindingLibrary(checkedLibrary);
                RequireStagedProofSources();
            }
            void RequireReplayDiagnosticInputs()
            {
                if (auditExecutable is not null) CheckedAuditExecutable();
                deepRun?.Attempt?.RequireIdentity(extraction);
                RequireOriginalProofSources();
                if (!Same(before, Inputs(proof, settings)))
                    throw new InvalidOperationException("Inputs changed during verification");
                RecheckManifest();
                RequireDeepStable(checkLibraryContents: true);
            }
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            RequireOnlyAdded(bound, built, "Proof");
            RequireReplayedImports(fresh, session);
            // Interface oleans were replayed above and RequireOnlyAdded kept them unchanged since.
            string[] unreplayed = [.. extractionPublication is null ? Array.Empty<string>() : ["Extracted"],
                .. symbols && !proofRestored ? ["ExtractedSymbols"] : Array.Empty<string>(),
                .. proofRestored ? Array.Empty<string>() : ["Proof"]];
            // Replaying every module from the extraction to the proof lets the audit read that environment without a
            // second import. ExtractedImports imports Extracted from outside the set, which a joint replay rejects.
            // The audit imports restored deep modules, so a full replay could not give it a fused environment.
            string[] replay = unreplayed.Length == 0 || importModules.Length > 0 ||
                deep?.Restored == true ? unreplayed :
                ["Extracted", .. selected.Where(module => !SelectionModules.IsSymbols(module)),
                    .. symbols ? ["ExtractedSymbols", .. selected.Where(SelectionModules.IsSymbols)]
                        : Array.Empty<string>(),
                    "Proof"];
            string[] auditModules = ["Proof", "Extracted",
                .. HasContractImports(extraction) ? ["ExtractedImports"] : Array.Empty<string>()];
            var proofAudit = ProofTheorem(theorem, extraction);
            AuditRequest[] proofAudits =
                [statement?.Apply(proofAudit) ?? proofAudit, ExtractionCertificate("Extracted.translation_valid")];
            if (deep is not null)
            {
                if (deep.Requests.Any(request => request.Audit.name == theorem))
                    throw new InvalidOperationException(
                        "Proof theorem collides with a deep-check request: " + theorem);
                // Restored deep modules were replayed by the run that published them, in the same keyed environment.
                if (!deep.Restored) replay = [.. replay.Concat(deep.Modules).Distinct(StringComparer.Ordinal)];
                auditModules = [.. auditModules.Concat(deep.Modules).Distinct(StringComparer.Ordinal)];
                proofAudits = [proofAudits[0], .. deep.Requests.Select(request => request.Audit)];
            }
            AuditedOleans? audited = null;
            // A caller that ends the run at the stage after the proof check must do so before the display starts.
            var replays = replay.Length > 0;
            stage?.Invoke(replays ? "kernel replay" : "theorem audit");
            RequireDeepBindingStable();
            // The display runs beside replay and audit; it feeds no check and is read only after all of them.
            var statementView = Path.Combine(fresh, StatementViewFile);
            var statementCached = proofRestored && File.Exists(statementView);
            var proofOlean = Path.Combine(fresh, "Proof.olean");
            var viewing = viewsStatement && !statementCached
                ? Task.Run(() => ViewStatement(fresh, proofOlean, leanPath, proofSource, theorem)) : null;
            StatementView? viewed;
            try
            {
                if (replays)
                {
                    RequireStagedProofSources();
                    bool jointReplayRejected = false;
                    if (Environment.GetEnvironmentVariable("LEANCIL_PROFILE_CONSUMER_REPLAY") != "true")
                    {
                        try
                        {
                            audited = AuditOleans(leanPath, auditModules, proofAudits,
                                ImportPremise(extraction), replayTargets: replay);
                        }
                        catch (InvalidOperationException error)
                        {
                            jointReplayRejected = error.Message.Contains(
                                "while replaying declaration", StringComparison.Ordinal);
                        }
                    }
                    if (audited is null)
                    {
                        if (deep is not null) RequireReplayDiagnosticInputs();
                        Dictionary<string, string>? isolatedFailures = null;
                        if (deep is not null && jointReplayRejected)
                        {
                            // The fused check already rejected this set. Replay each target against its own imports.
                            try { isolatedFailures = ReplayConsumerModulesSeparately(fresh, replay, leanPath, false); }
                            catch (InvalidOperationException) { }
                            RequireReplayDiagnosticInputs();
                        }
                        try
                        {
                            if (isolatedFailures is not { Count: > 0 })
                                ReplayCheckedModules(replay, leanPath,
                                    (proofRestored ? "Kernel replay of extraction: " : "Kernel replay: ") + entry);
                            else
                                throw new InvalidOperationException("Kernel replay rejected " +
                                    string.Join("\n", isolatedFailures.Select(pair => pair.Key + ": " + pair.Value)));
                        }
                        catch (InvalidOperationException) when (deep is not null)
                        {
                            RequireReplayDiagnosticInputs();
                            Dictionary<string, ReplayRejection>? rejections = null;
                            try
                            {
                                isolatedFailures ??= ReplayConsumerModulesSeparately(fresh, replay, leanPath, false);
                            }
                            catch (Exception) { }
                            RequireReplayDiagnosticInputs();
                            if (isolatedFailures is not null)
                            {
                                stage?.Invoke("replay diagnostics");
                                RequireReplayDiagnosticInputs();
                                try
                                {
                                    rejections = DiagnoseReplayFailures(fresh,
                                        deep.OwnedFailures(isolatedFailures.Keys), leanPath);
                                }
                                catch (Exception) { }
                                RequireReplayDiagnosticInputs();
                            }
                            if (rejections is not null) deep.RejectReplay(rejections, deepRun?.Attempt);
                            throw;
                        }
                    }
                    stage?.Invoke("theorem audit");
                }
                // The audit reads the replayed bytes; all source and artifact guards still follow it.
                RequireStagedProofSources();
                audited ??= AuditOleans(leanPath, auditModules, proofAudits, ImportPremise(extraction));
            }
            finally
            {
                // The display process must exit before the artifact guard below and before its files are deleted.
                try { viewing?.Wait(); }
                catch (AggregateException) { }
            }
            viewed = viewing?.GetAwaiter().GetResult();
            RequireStagedProofSources();
            if (!Same(built, OleanHashes(fresh, session)))
                throw new InvalidOperationException("Compiled artifacts changed during verification");
            RequireAuditedModule(audited, "Proof", Path.Combine(fresh, "Proof.olean"));
            RequireAuditedModule(audited, "Extracted", Path.Combine(fresh, "Extracted.olean"));
            if (HasContractImports(extraction))
                RequireAuditedModule(audited, "ExtractedImports", Path.Combine(fresh, "ExtractedImports.olean"));
            RequireAuditedConstants(audited);
            deep?.RequireAudited(audited);
            deepRun?.Attempt?.RequireIdentity(extraction);
            if (deep is not null)
            {
                RequireOriginalProofSources();
                if (!Same(before, Inputs(proof, settings)))
                    throw new InvalidOperationException("Inputs changed during verification");
                RecheckManifest();
                RequireDeepStable(checkLibraryContents: true);
            }
            deep?.RequireTheorems(audited, proofAudits, deepRun?.Attempt);
            var auditedTheorems = audited.theorems.ToDictionary(result => result.name, StringComparer.Ordinal);
            foreach (var request in proofAudits) AuditedAxioms(auditedTheorems[request.name]);
            stage?.Invoke("extraction certificate audit");
            extractionAudit = AuditText(auditedTheorems["Extracted.translation_valid"]);
            stage?.Invoke("theorem audit");
            axioms = AuditedAxioms(auditedTheorems[theorem]);
            audit = AuditText(auditedTheorems[theorem]);
            var proved = auditedTheorems[theorem];
            refutation = ExtractedRefutation(proved, extraction.Root);
            if (statement?.Expected is not null && proved.matches != true)
                throw new StatementMismatchException(proved.mismatch);
            if (statement?.Term == true && proved.term is null)
                throw new InvalidOperationException($"Cannot compare the verified statement: {proved.termError}");
            RequireOriginalProofSources();
            RequireStagedProofSources();
            if (!Same(before, Inputs(proof, settings)))
                throw new InvalidOperationException("Inputs changed during verification");
            // The display is published only here, after every check above, and never feeds a check.
            if (viewsStatement)
                VerifiedStatement = statementCached ? ReadStatementView(statementView) : viewed;
            RequireDeepStable();
            void PublishProof()
            {
                var publication = Path.Combine(fresh, "proof-cache");
                Directory.CreateDirectory(publication);
                foreach (var path in Directory.EnumerateFiles(fresh).Where(path =>
                    Path.GetFileName(path).StartsWith("Proof.olean", StringComparison.Ordinal) ||
                    Path.GetFileName(path) is ProofMessagesFile or StatementViewFile))
                    File.Copy(path, Path.Combine(publication, Path.GetFileName(path)));
                RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
                PublishSuccess(proofKey, publication);
            }
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            fullResult = fullImportAudit?.Invoke(output, fresh, "Proof", leanPath);

            // Bind the report only after confirming inputs stayed unchanged.
            stage?.Invoke("extraction integrity");
            var identityHash = RecheckManifest().ToString();

            RequireOriginalProofSources();
            if (!Same(before, Inputs(proof, settings)))
                throw new InvalidOperationException("Inputs changed during verification");
            // An editor package requires the same library by path and may have built into it meanwhile.
            RequireUnchangedLibrary();
            RequireDeepStable();

            var initializedTypes = extraction.Root.TryGetProperty("initializedTypes", out var assumptions)
                ? assumptions.Deserialize<string[]>() : [];
            RequireImplementationImports(extraction);
            var report = new Report(CertificateSchema, Sha(assembly), identityHash, theorem, axioms, audit, before,
                deepChecks is null ? BindingSection.Default : DeepBindingSection(deepChecks, matchedPins!,
                    deep!.Requests, new(bindingSourcesKey!,
                        File.ReadAllText(Path.Combine(session, "lean-toolchain")).Trim(), Sha(LeanExecutable)), audited,
                    deep.Uncovered),
                libraryKey, libraryBuild, extractionAudit, initializedTypes,
                staticValues: StaticValueAssumptions(extraction.Root),
                opaqueStaticValues: OpaqueStaticValues(extraction.Root),
                contractImports: ContractImportAssumptions(extraction.Root),
                imports: fullResult?.Imports ?? PublishedImports(extraction.Root),
                contractDependencies: fullResult?.Dependencies ?? DeploymentDependencies(extraction.Root),
                compositionTheorem: fullResult?.Theorem, compositionAudit: fullResult?.Audit,
                initializationAssumptions: InitializationAssumptions(extraction.Root), libraryModules: libraryModules,
                statementIdentity: statement is null ? null : Identity(proved), refutation: refutation);
            RequireContractInterfaceArtifacts(fresh, importModules, acceptedInterfaceArtifacts);
            var deepPublication = deep is null ? null : StageDeepResult(deep, fresh);
            if (!proofRestored) PublishProof();
            if (extractionPublication is not null)
                PublishSuccess(extractedKey, extractionPublication);
            if (deepPublication is not null) PublishSuccess(deep!.ResultKey!, deepPublication);
            File.WriteAllText(reportPath, JsonSerializer.Serialize(report, Json) + "\n");
            completesLibrary = libraryModules is not null;
            standaloneCachePromotion = completesLibrary && deep is null && UseSuccessCache
                ? new(fullLibraryKey!, new(currentModules, StringComparer.Ordinal),
                    extractedKey, extractionSuffix, proofKey, proofSuffix) : null;
            // A fixture can reuse the frontend and its axiom diagnostics only after the module passes audit.
            if (cleanExtractionCompiled) onCleanExtractionCompiled?.Invoke(extractedKey);
            return report;
        }
        catch (Exception error)
        {
            error.Data[SourceCopies.Key] = copies;
            throw;
        }
        finally
        {
            Directory.Delete(fresh, true);
        }
    }

    void IDisposable.Dispose()
    {
        if (session is not null && Directory.Exists(session))
            Directory.Delete(session, true);
        if (ownsLibrary && library is not null && Directory.Exists(library))
            Directory.Delete(library, true);
        foreach (var use in entryUses) use.Dispose();
    }

    /// <summary>
    /// After a result checked against a closure entry was reported and stands: builds, kernel-replays and
    /// caches the whole library, so later runs and editor packages use it. Does nothing otherwise. A failure
    /// leaves the reported result and its certificate standing and is thrown for the command to report.
    /// </summary>
    internal void CompleteLibrary()
    {
        if (!completesLibrary) return;
        completesLibrary = false;
        Console.Out.Flush();
        Console.Error.WriteLine($"The result above was checked against the {libraryModules!.Length} framework " +
            "modules the proof imports. Building the whole certified library for later runs.");
        try
        {
            using var whole = new Program();
            whole.Library(Inputs(At("CIL.lean")));
            var promotion = standaloneCachePromotion;
            standaloneCachePromotion = null;
            if (promotion is not null)
                PromoteStandaloneCache(promotion, whole.fullLibraryKey!, whole.SessionModules(whole.session!),
                    whole.RequireCertifiedLibraryContents);
        }
        // Whatever stopped the build, the caller reports it; nothing may escape as an unhandled error here.
        catch (Exception error)
        {
            throw new InvalidOperationException("The verified result above stands and its certificate is " +
                "written, but the whole certified library was not built: " + error.Message, error);
        }
    }

    /// <summary>Authenticated successes checked in an exact compiled environment before library completion.</summary>
    sealed record StandaloneCachePromotion(string FullLibraryKey, SortedDictionary<string, string> Modules,
        string ExtractionKey, string ExtractionSuffix, string ProofKey, string ProofSuffix);

    string StandaloneEnvironmentKey(string key, SortedDictionary<string, string> modules) =>
        ContentKey("certified-modules-v1\n" + VerificationPolicy + "\n" + key + "\n" +
            JsonSerializer.Serialize(modules));

    static string StandaloneExtractionKey(string environment, string suffix) =>
        ContentKey("extraction-audit-v3-direct-certificate\n" + environment + suffix);

    static string StandaloneProofKey(string extraction, string suffix) =>
        ContentKey("theorem-audit-v3\n" + extraction + suffix);

    /// <summary>
    /// Reuses authenticated successes only across a byte-identical extension of their module families.
    /// </summary>
    void PromoteStandaloneCache(StandaloneCachePromotion promotion, string completeKey,
        SortedDictionary<string, string> completeModules, Action requireStable)
    {
        if (!UseSuccessCache || promotion.FullLibraryKey != completeKey ||
            !ModuleArtifactsPreserved(promotion.Modules, completeModules)) return;
        var environment = StandaloneEnvironmentKey(completeKey, completeModules);
        var extraction = StandaloneExtractionKey(environment, promotion.ExtractionSuffix);
        var proof = StandaloneProofKey(extraction, promotion.ProofSuffix);
        var staging = Path.Combine(Path.GetTempPath(), "leancil-promotion-" + Guid.NewGuid().ToString("N"));
        try
        {
            foreach (var (original, promoted) in new[]
                { (promotion.ExtractionKey, extraction), (promotion.ProofKey, proof) })
            {
                var destination = Path.Combine(staging, promoted);
                Directory.CreateDirectory(destination);
                if (!RestoreSuccess(original, destination)) continue;
                // Completion must retain its authenticated inputs through cache publication.
                requireStable();
                PublishSuccess(promoted, destination);
            }
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or InvalidOperationException)
        {
            Console.Error.WriteLine("warning: completed-library success cache not updated: " + error.Message);
        }
        finally { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
    }
}
/// <summary>
/// Internal errors in the output of Lean, Lake or a Lean executable. Lean prints a panic and continues on a
/// default value, so a run that reports one can still exit 0; no result of such a run is trusted.
/// </summary>
internal static partial class LeanOutput
{
    /// <summary>Starts each line that summarizes internal errors above the output they were found in.</summary>
    internal const string SummaryPrefix = "Internal error: ";

    /// <summary>One internal-error message, the module Lake was building and the position Lean logged it at.</summary>
    internal sealed record InternalError(string? Module, string? Location, string Message);

    // Lake job headers: failed, warned, informational and built.
    [GeneratedRegex(@"^(?:✖|⚠|ℹ|✔) \[\d+/\d+\] \S+ (?<module>\S+)")]
    internal static partial Regex Job { get; }

    // The exact text Lean's runtime writes to stderr: `panic!` with its source position, runtime aborts, the C
    // array accessors, stack exhaustion and failed assertions. It counts only where a stderr line or a message
    // body starts with it, which is where the runtime writes it; the same words inside a sentence are a quote.
    [GeneratedRegex(@"\A(?:PANIC at \S+(?: \S+)?:\d+:\d+: .*|INTERNAL PANIC: .*|Error: index out of bounds\z|" +
        @"Stack overflow detected\. Aborting\.|LEAN ASSERTION VIOLATION.*)")]
    private static partial Regex Marker { get; }

    // A Lake log entry or a Lean message that starts at a source position.
    [GeneratedRegex(@"^(?:(?:error|warning|info|trace): (?<location>.+?\.lean:\d+:\d+): |" +
        @"(?<location>.+?\.lean:\d+:\d+): (?:error|warning|info)(?:\([^)]*\))?: )")]
    private static partial Regex Located { get; }

    [GeneratedRegex(@"^(?:error|warning|info|trace): ")]
    private static partial Regex Entry { get; }

    /// <summary>Whether `executable` is Lean, Lake or the audit executable built from Lean sources.</summary>
    internal static bool RunsLean(string executable)
    {
        // Either separator ends the directory, so a path written on another host still names its program.
        var name = executable[(executable.LastIndexOfAny(['/', '\\']) + 1)..];
        if (name.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) name = name[..^".exe".Length];
        return name is "lean" or "lake" or "leancil-audit";
    }

    /// <summary>
    /// Every internal error in `output`, in order: a line of stderr, or a line of a message Lean logged, that
    /// starts with the runtime's text. A logged one is at its message's position, in plain or `--json` output;
    /// one written straight to stderr has none. `hidden` omits the modules of other requests.
    /// </summary>
    internal static List<InternalError> InternalErrors(string output, IReadOnlyCollection<string>? hidden = null)
    {
        var found = new List<InternalError>();
        string? module = null;
        // The position of the entry the current lines continue, kept only while that entry is an internal error.
        string? continued = null;
        foreach (var line in output.ReplaceLineEndings("\n").Split('\n'))
        {
            if (line.StartsWith(SummaryPrefix, StringComparison.Ordinal)) continue;
            if (Job.Match(line) is { Success: true } job)
            {
                (module, continued) = (job.Groups["module"].Value, null);
                continue;
            }
            if (module is not null && hidden?.Contains(module) == true) continue;
            if (JsonMessage(line) is { } message)
            {
                foreach (var text in message.Data.ReplaceLineEndings("\n").Split('\n'))
                    if (Marker.Match(text) is { Success: true } match)
                        found.Add(new(module, message.Position, match.Value));
                continued = null;
                continue;
            }
            var located = Located.Match(line);
            var entry = located.Success ? located : Entry.Match(line);
            var location = located.Success ? located.Groups["location"].Value : entry.Success ? null : continued;
            // The body of a logged message starts after its level and position; any other line is read whole.
            var internalError = Marker.Match(line[entry.Length..]);
            if (internalError.Success) found.Add(new(module, location, internalError.Value));
            if (entry.Success) continued = internalError.Success ? location : null;
        }
        return found;
    }

    // The position and text of one `lean --json` message line.
    static (string? Position, string Data)? JsonMessage(string line)
    {
        if (!line.StartsWith('{')) return null;
        try
        {
            var message = JsonSerializer.Deserialize<JsonElement>(line);
            if (message.ValueKind != JsonValueKind.Object || !message.TryGetProperty("data", out var data) ||
                data.ValueKind != JsonValueKind.String)
                return null;
            var position = message.TryGetProperty("fileName", out var file) && file.ValueKind == JsonValueKind.String &&
                message.TryGetProperty("pos", out var pos) && pos.ValueKind == JsonValueKind.Object &&
                pos.TryGetProperty("line", out var row) && pos.TryGetProperty("column", out var column)
                ? $"{file.GetString()}:{row.GetInt32()}:{column.GetInt32()}" : null;
            return (position, data.GetString()!);
        }
        catch (Exception error) when (error is JsonException or InvalidOperationException) { return null; }
    }

    /// <summary>
    /// The errors each request's proof module printed, in the order of `modules`, or null when a module the
    /// requests share printed one, which no single request owns.
    /// </summary>
    internal static InternalError[][]? ByRequest(IReadOnlyList<InternalError> errors, IReadOnlyList<string> modules) =>
        errors.Any(error => error.Module is null || !modules.Contains(error.Module)) ? null
            : [.. modules.Select(module => errors.Where(error => error.Module == module).ToArray())];

    /// <summary>
    /// The failure of a Lean command that exited 0 after printing an internal error, or null for any other run:
    /// a failed command already fails, and other programs print such text only when they quote it.
    /// </summary>
    internal static InvalidOperationException? RejectedSuccess(IReadOnlyList<string> command, int code,
        string output) =>
        code == 0 && RunsLean(command[0]) && InternalErrors(output) is { Count: > 0 } errors
            ? Failure(command, code, output, errors) : null;

    /// <summary>
    /// The failure of a command whose output holds `errors`: one summary line for each distinct message, naming
    /// its module and position, then the whole output.
    /// </summary>
    internal static InvalidOperationException Failure(IEnumerable<string> command, int code, string output,
        IReadOnlyList<InternalError> errors)
    {
        var text = new StringBuilder(
            $"Lean reported an internal error (exit {code}): {string.Join(' ', command)}\n");
        foreach (var group in errors.GroupBy(error => error))
        {
            var count = group.Count();
            text.Append(SummaryPrefix).Append(group.Key.Message);
            if (count > 1) text.Append($" ({count} times)");
            if (group.Key.Location is { } location) text.Append(" at ").Append(location);
            if (group.Key.Module is { } module) text.Append(" (building ").Append(module).Append(')');
            text.Append('\n');
        }
        return new InvalidOperationException(text.Append(output).ToString());
    }
}
/// <summary>
/// The developer's files a verification session copied, by the path of each copy, so diagnostics cite the file
/// the developer edits. Only byte-identical copies are recorded, so a copy's lines and columns are the original's.
/// </summary>
internal sealed partial class SourceCopies(string directory)
{
    /// <summary>Exception.Data key holding the session's copies when verification fails.</summary>
    internal const string Key = "LeanCIL.SourceCopies";

    readonly Dictionary<string, string> originals = new(Program.LocationComparer);
    readonly Dictionary<string, string> modules = new(StringComparer.Ordinal);
    // An observed copy's line holding the inserted import, by the copy's path.
    readonly Dictionary<string, int> observedLines = new(Program.LocationComparer);

    [GeneratedRegex(@"\A(?<file>.+?\.lean):(?<line>\d+):(?<column>\d+)\z")]
    private static partial Regex Location { get; }

    /// <summary>
    /// Records `copy` as a copy of `original` when their bytes are equal; a copy that differs keeps its own path,
    /// since its locations would point elsewhere in the original.
    /// </summary>
    internal bool Add(string copy, string original)
    {
        if (!File.Exists(copy) || !File.Exists(original) ||
            !File.ReadAllBytes(copy).AsSpan().SequenceEqual(File.ReadAllBytes(original)))
            return false;
        originals[Path.GetFullPath(copy, directory)] = Path.GetFullPath(original);
        return true;
    }

    /// <summary>
    /// <see cref="Add(string, string)"/> for a copy built as module `copyModule`, which Lake's progress lines name,
    /// of the original's module `originalModule`.
    /// </summary>
    internal bool Add(string copy, string original, string copyModule, string originalModule)
    {
        if (!Add(copy, original)) return false;
        modules[copyModule] = originalModule;
        return true;
    }

    /// <summary>
    /// Records `copy` as <see cref="ObservedProof"/> of `original` when its bytes are exactly that; positions on the
    /// line of the inserted import are read back past it, and every other position is the original's.
    /// </summary>
    internal bool AddObserved(string copy, string original)
    {
        if (!File.Exists(copy) || !File.Exists(original)) return false;
        var (observed, line) = ObservedProof.Insert(File.ReadAllBytes(original));
        if (!File.ReadAllBytes(copy).AsSpan().SequenceEqual(observed)) return false;
        var key = Path.GetFullPath(copy, directory);
        originals[key] = Path.GetFullPath(original);
        observedLines[key] = line;
        return true;
    }

    /// <summary><see cref="AddObserved(string, string)"/> for a copy Lake builds as module `copyModule`.</summary>
    internal bool AddObserved(string copy, string original, string copyModule, string originalModule)
    {
        if (!AddObserved(copy, original)) return false;
        modules[copyModule] = originalModule;
        return true;
    }

    /// <summary>
    /// The file, line and column in the original of a position Lean printed in `file`, or the position as printed
    /// when `file` is no copy. A column inside an inserted import reads as the start of its line.
    /// </summary>
    internal (string File, int Line, int Column) Position(string file, int line, int column)
    {
        var key = Path.GetFullPath(file, directory);
        if (!originals.TryGetValue(key, out var original)) return (file, line, column);
        var shifted = observedLines.TryGetValue(key, out var observed) && observed == line;
        return (original, line, shifted ? Math.Max(0, column - ObservedProof.Import.Length) : column);
    }

    /// <summary>
    /// `messages` Lean reported for the copy of `original`, each at its position in the original, with the error a
    /// failure record cites read the same way; unchanged when `original` has no observed copy.
    /// </summary>
    internal Program.ProofMessage[]? Relocate(string original, Program.ProofMessage[]? messages)
    {
        var full = Path.GetFullPath(original);
        var copy = observedLines.Keys.FirstOrDefault(key => Program.LocationComparer.Equals(originals[key], full));
        if (messages is null || copy is null) return messages;
        int Column(int line, int column) => Position(copy, line, column).Column;
        return [.. messages.Select(message => message with
        {
            column = Column(message.line, message.column),
            text = message.text.StartsWith(Program.FailureMarker, StringComparison.Ordinal) &&
                System.Text.Json.Nodes.JsonNode.Parse(message.text[Program.FailureMarker.Length..]) is
                    System.Text.Json.Nodes.JsonObject { } record &&
                record["error"] is System.Text.Json.Nodes.JsonObject { } error &&
                error["line"]?.GetValue<int>() is { } line && error["column"]?.GetValue<int>() is { } column
                    ? Program.FailureMarker + Relocated(record, line, Column(line, column)) : message.text
        })];
    }

    // The record with the error it cites moved to `column`.
    static string Relocated(System.Text.Json.Nodes.JsonObject record, int line, int column)
    {
        record["error"] = new System.Text.Json.Nodes.JsonObject { ["line"] = line, ["column"] = column };
        return record.ToJsonString();
    }

    /// <summary>
    /// `text` with each copy's path read as its original and the workspace's other paths shown as
    /// <see cref="Workspace"/>, its `--root` argument left out: the workspace is deleted when verification ends.
    /// </summary>
    internal string Displayed(string text, Func<string, string>? display = null)
    {
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        // Longer paths first, so a copy inside another copy's directory keeps its own original.
        foreach (var (copy, original) in originals.OrderByDescending(pair => pair.Key.Length))
            text = text.Replace(copy, display?.Invoke(original) ?? original, comparison);
        var workspace = Path.GetFullPath(directory)
            .TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
        return text.Replace(" --root=" + workspace, "", comparison).Replace(workspace, Workspace, comparison);
    }

    /// <summary>How <see cref="Displayed"/> shows the deleted verification workspace.</summary>
    internal const string Workspace = "<verification workspace>";

    /// <summary>The original module of `module`, a copy's module as Lake named it, or `module` itself.</summary>
    internal string ModuleOf(string module) => modules.GetValueOrDefault(module, module);

    /// <summary>The original of `file`, a path as Lean or Lake printed it, or null when it is no copy.</summary>
    internal string? OriginalOf(string file) => originals.GetValueOrDefault(Path.GetFullPath(file, directory));

    /// <summary>`location`, a `file:line:column`, citing through `display` the original of a copied file.</summary>
    internal string Locate(string location, Func<string, string>? display = null)
    {
        var match = Location.Match(location);
        if (!match.Success || OriginalOf(match.Groups["file"].Value) is not { } original) return location;
        var (_, line, column) = Position(match.Groups["file"].Value, int.Parse(match.Groups["line"].Value),
            int.Parse(match.Groups["column"].Value));
        return $"{display?.Invoke(original) ?? original}:{line}:{column}";
    }
}

/// <summary>
/// The proof `verify` checks when asked for failure records or a trace: the developer's proof with
/// <see cref="Import"/> inserted at the start of its first import line, so the observer runs on it and every
/// other line and column is the original's.
/// </summary>
internal static partial class ObservedProof
{
    /// <summary>The observer module, which a proof asked for records, a trace or goals is checked against.</summary>
    internal const string Module = "CIL.Observe";
    /// <summary>The text inserted, which imports the observer ahead of the proof's own imports.</summary>
    internal const string Import = "import " + Module + " ";

    // An import command, plain or with module-system modifiers, at the start of a line.
    [GeneratedRegex(@"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b", RegexOptions.Multiline)]
    private static partial Regex ImportLine { get; }

    /// <summary>`source` with <see cref="Import"/> inserted, and the 1-based line it was inserted on.</summary>
    internal static (byte[] Bytes, int Line) Insert(byte[] source)
    {
        var preamble = source.AsSpan().StartsWith(Encoding.UTF8.Preamble) ? Encoding.UTF8.Preamble.Length : 0;
        var text = Encoding.UTF8.GetString(source, preamble, source.Length - preamble);
        var match = ImportLine.Match(text);
        // A multiline `^` matches at a line start, so the match starts the import's line.
        var start = match.Success ? match.Index : 0;
        var at = preamble + Encoding.UTF8.GetByteCount(text.AsSpan(0, start));
        var line = 1 + text.AsSpan(0, start).Count('\n');
        return ([.. source.AsSpan(0, at), .. Encoding.UTF8.GetBytes(Import), .. source.AsSpan(at)], line);
    }
}
