using System.Text.Json;

namespace Nethermind.LeanCIL;

/// <summary>An argument kept in a local slot, with the kind of that slot.</summary>
internal sealed record ParameterHome(int Argument, LocalKind Kind)
{
    internal string ToLean() => $"({Argument}, {Kind.ToLean()})";
}

/// <summary>What a static site reads: its value, an opaque binding, or the data block it addresses.</summary>
internal abstract record StaticSiteDetail;

/// <summary>A load whose value the caller binds; the zero bytes of the site fix only the load width.</summary>
internal sealed record OpaqueStaticValue(bool? Signed) : StaticSiteDetail;

/// <summary>
/// A load of a value an initializer computes; <paramref name="Signed"/> is null for aggregates and
/// <paramref name="Initializer"/>, a method index, is null when a literal gives the value, which the term
/// spells as method 0.
/// </summary>
internal sealed record InitializedStaticValue(bool? Signed, int? Initializer, ValueList<string> Arguments,
    string? Literal, bool Construct) : StaticSiteDetail;

/// <summary>The address of static data aligned to <paramref name="Alignment"/> bytes.</summary>
internal sealed record StaticDataBlock(int Alignment) : StaticSiteDetail;

/// <summary>An instruction of a method that reads or addresses a static field.</summary>
internal sealed record StaticSite(int Pc, StaticIdentityRecord Identity, string FieldName, ValueList<byte> Bytes,
    StaticSiteDetail Detail)
{
    internal string ToLean() => ToLean(LeanText.MethodNumber);

    /// <summary>The initializer method this site reads through, or none.</summary>
    internal IEnumerable<int> Methods => Detail is InitializedStaticValue { Initializer: { } method } ? [method] : [];

    /// <summary>This site with its initializer method replaced by <paramref name="map"/> of it.</summary>
    internal StaticSite Renumber(Func<int, int> map) =>
        Detail is InitializedStaticValue { Initializer: { } method } value
            ? this with { Detail = value with { Initializer = map(method) } } : this;

    /// <summary>The Lean site term, with the initializer written as <paramref name="calleeName"/> of it.</summary>
    internal string ToLean(Func<int, string> calleeName)
    {
        var header = $"({Pc}, {{ identity := {Identity.Identity}, " +
            $"assemblyIdentity := {JsonSerializer.Serialize(Identity.AssemblyIdentity)}, " +
            $"fieldName := {JsonSerializer.Serialize(FieldName)}, bytes := {StaticData.LeanBytes(Bytes)}, ";
        return Detail switch
        {
            OpaqueStaticValue opaque => header + $"scalar := {Scalar(opaque.Signed)}, opaqueValue := true }})",
            InitializedStaticValue value => header + $"scalar := {Scalar(value.Signed)}, " +
                $"initializer := some {{ method := {(value.Initializer is { } method ? calleeName(method) : "0")}, " +
                $"arguments := [{string.Join(", ", value.Arguments)}]" +
                (value.Literal is null ? "" : $", literal := some ({value.Literal})") +
                (value.Construct ? ", construct := true" : "") + " } })",
            StaticDataBlock block => header + $"alignment := {block.Alignment} }})",
            _ => throw new InvalidOperationException("Unknown static site detail")
        };
    }

    static string Scalar(bool? signed) => signed is { } value ? "some " + LeanText.Bool(value) : "none";
}

/// <summary>
/// The frame of one method: whether it returns a value, its locals with their initial values and kinds, the
/// arguments held in locals, the vector locals whose value stays opaque, the static sites its code reads and
/// the Lean term of its declared signature. The shared layout environment is named by the emitted file.
/// </summary>
internal sealed record FrameMetadata(bool ReturnsValue, ValueList<InitialValue> Locals,
    ValueList<LocalKind> LocalKinds, ValueList<int> OpaqueVectorLocals,
    ValueList<ParameterHome> ParameterHomes, ValueList<StaticSite> StaticSites, string Declared)
{
    /// <summary>The environment value: the file's shared constant, or a template's parameter.</summary>
    internal const string EnvironmentLean = "environment";

    /// <summary>The method reads or addresses at least one static field.</summary>
    internal bool HasStaticSites => StaticSites.Count != 0;

    /// <summary>The method declares no locals.</summary>
    internal bool HasNoLocals => Locals.Count == 0;

    internal string ReturnsValueLean => LeanText.Bool(ReturnsValue);

    internal string LocalsLean => string.Join(", ", Locals.Select(value => value.ToLean()));

    internal string LocalKindsLean => string.Join(", ", LocalKinds.Select(kind => kind.ToLean()));

    internal string OpaqueVectorLocalsLean => string.Join(", ", OpaqueVectorLocals);

    internal string ParameterHomesLean => string.Join(", ", ParameterHomes.Select(home => home.ToLean()));

    internal string StaticSitesLean => StaticSitesLeanWith(LeanText.MethodNumber);

    /// <summary>The index of every method the static sites read initial values through.</summary>
    internal IEnumerable<int> Methods => StaticSites.SelectMany(site => site.Methods);

    /// <summary>This frame with every initializer method index replaced by <paramref name="map"/> of it.</summary>
    internal FrameMetadata Renumber(Func<int, int> map) => this with
    {
        StaticSites = [.. StaticSites.Select(site => site.Renumber(map))]
    };

    /// <summary>The frame fields of a Lean <c>Method</c> structure.</summary>
    internal string ToLean() => ToLean(LeanText.MethodNumber);

    /// <summary>The frame fields, with each initializer written as <paramref name="calleeName"/> of it.</summary>
    internal string ToLean(Func<int, string> calleeName) =>
        $"returnsValue := {ReturnsValueLean}, locals := [{LocalsLean}], localKinds := [{LocalKindsLean}], " +
        $"opaqueVectorLocals := [{OpaqueVectorLocalsLean}], parameterHomes := [{ParameterHomesLean}], " +
        $"staticSites := [{StaticSitesLeanWith(calleeName)}], declared := {Declared}, " +
        $"environment := {EnvironmentLean}";

    string StaticSitesLeanWith(Func<int, string> calleeName) =>
        string.Join(", ", StaticSites.Select(site => site.ToLean(calleeName)));
}
