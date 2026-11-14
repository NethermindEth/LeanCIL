using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The identities of CIL/Identity.lean, built from metadata columns. ToLean() elaborates against the expected Lean
// type; ToDisplay() is the text CIL/Identity.lean shows for the value, escapes and raw fallbacks included.

/// <summary>One metadata name, the UTF-8 bytes of a <c>#Strings</c> entry (<c>CIL.MetadataName</c>).</summary>
internal sealed record MetadataName
{
    readonly byte[] bytes;

    MetadataName(byte[] bytes) => this.bytes = bytes;

    /// <summary>The empty name, which a neutral culture and the global namespace hold.</summary>
    internal static readonly MetadataName Empty = new([]);

    /// <summary>The name whose UTF-8 bytes are <paramref name="bytes"/>.</summary>
    internal static MetadataName FromBytes(ReadOnlySpan<byte> bytes) => new(bytes.ToArray());

    /// <summary>The name of a <c>#Strings</c> entry as Cecil decodes it. Its bytes are the entry's bytes when the
    /// entry is UTF-8, as ECMA-335 requires; Cecil replaces the bytes of an entry that is not.</summary>
    internal static MetadataName OfEntry(string entry) => new(IdentityText.Utf8(entry));

    /// <summary>The UTF-8 bytes of the name.</summary>
    internal ReadOnlySpan<byte> Bytes => bytes;

    /// <summary>The number <c>CIL.MetadataName.code</c> holds: the bytes after a leading 1, in base 256.</summary>
    internal BigInteger Code => IdentityText.Code(bytes);

    string? Text => IdentityText.DecodeUtf8(bytes);

    // MetadataName.literal?: no #Strings entry holds a NUL, so name! refuses one.
    string? Literal => Text is { } text && !text.Contains('\0') ? IdentityText.Quoted(text) : null;

    /// <summary>The <c>name!</c> literal, or the constructor of the code when no literal shows the name.</summary>
    internal string ToLean() => Literal is { } quoted ? "name!" + quoted : $"(CIL.MetadataName.mk 0x{Code:x})";

    /// <summary>The text of <c>MetadataName.display</c>.</summary>
    internal string ToDisplay() => Readable() ?? IdentityText.RawCode(Code);

    /// <summary>The text of <c>MetadataName.readable?</c>, or null when the bytes are not UTF-8 or hold an
    /// invisible character above U+FFFF.</summary>
    internal string? Readable() => Text is { } text ? IdentityText.Readable(text) : null;

    /// <summary>The <c>Repr</c> of the name: its literal, or the raw structure of its code.</summary>
    internal LeanDoc Repr() => LeanDoc.Of(Literal is { } quoted ? "name!" + quoted : IdentityText.RawCode(Code));

    /// <summary>Equal names have equal bytes.</summary>
    public bool Equals(MetadataName? other) => other is not null && bytes.AsSpan().SequenceEqual(other.bytes);

    /// <summary>A hash of every byte of the name.</summary>
    public override int GetHashCode()
    {
        HashCode hash = new();
        hash.AddBytes(bytes);
        return hash.ToHashCode();
    }
}

/// <summary>One <c>#US</c> literal, its UTF-16 code units (<c>CIL.UserString</c>).</summary>
internal sealed record UserString
{
    readonly char[] units;

    UserString(char[] units) => this.units = units;

    /// <summary>The literal of an <c>ldstr</c> operand, whose UTF-16 code units Cecil reads unchanged.</summary>
    internal static UserString OfLiteral(string literal) => new(literal.ToCharArray());

    /// <summary>The UTF-16 code units of the literal.</summary>
    internal ReadOnlySpan<char> Units => units;

    /// <summary>The number <c>CIL.UserString.code</c> holds: the units after a leading 1, in base 65536.</summary>
    internal BigInteger Code => IdentityText.Code(units);

    // UserString.text?: none at an unpaired surrogate.
    string? Text => IdentityText.WellFormed(units) ? new string(units) : null;

    string? Literal => Text is { } text ? IdentityText.Quoted(text) : null;

    /// <summary>The <c>str!</c> literal, or the constructor of the code when no literal shows the literal.</summary>
    internal string ToLean() => Literal is { } quoted ? "str!" + quoted : $"(CIL.UserString.mk 0x{Code:x})";

    /// <summary>The text of <c>UserString.display</c>.</summary>
    internal string ToDisplay() =>
        Text is { } text && IdentityText.Readable(text) is { } readable ? readable : IdentityText.RawCode(Code);

    /// <summary>Equal literals have equal code units.</summary>
    public bool Equals(UserString? other) => other is not null && units.AsSpan().SequenceEqual(other.units);

    /// <summary>A hash of every code unit of the literal.</summary>
    public override int GetHashCode()
    {
        HashCode hash = new();
        hash.AddBytes(MemoryMarshal.AsBytes(units.AsSpan()));
        return hash.ToHashCode();
    }
}

/// <summary>The four version columns of an <c>Assembly</c> or <c>AssemblyRef</c> row (<c>CIL.Version</c>).
/// </summary>
internal readonly record struct AssemblyVersion(ushort Major, ushort Minor, ushort Build, ushort Revision)
{
    /// <summary>The columns Cecil read into <paramref name="version"/>, or null when a component is outside a
    /// column's range, which no row can hold.</summary>
    internal static AssemblyVersion? Of(Version? version) =>
        version is { Major: >= 0 and <= ushort.MaxValue, Minor: >= 0 and <= ushort.MaxValue,
            Build: >= 0 and <= ushort.MaxValue, Revision: >= 0 and <= ushort.MaxValue }
            ? new((ushort)version.Major, (ushort)version.Minor, (ushort)version.Build, (ushort)version.Revision)
            : null;

    /// <summary>The structure literal of the version.</summary>
    internal string ToLean() => string.Create(CultureInfo.InvariantCulture,
        $"{{ major := {Major}, minor := {Minor}, build := {Build}, revision := {Revision} }}");

    /// <summary>The text of <c>Version.display</c>, such as <c>11.0.0.0</c>.</summary>
    internal string ToDisplay() => string.Create(CultureInfo.InvariantCulture, $"{Major}.{Minor}.{Build}.{Revision}");

    /// <summary>The derived <c>Repr</c> of the version.</summary>
    internal LeanDoc Repr() => LeanDoc.Structure(("major", LeanDoc.Of(Major)), ("minor", LeanDoc.Of(Minor)),
        ("build", LeanDoc.Of(Build)), ("revision", LeanDoc.Of(Revision)));
}

/// <summary>An assembly by the name, version, culture and public key token of its row (<c>CIL.AssemblyName</c>).
/// The token is the eight token bytes read big-endian, or null for a row without a key.</summary>
internal sealed record AssemblyName(MetadataName Name, AssemblyVersion Version, MetadataName Culture,
    ulong? PublicKeyToken)
{
    /// <summary>The columns of an <c>Assembly</c> or <c>AssemblyRef</c> row, the token computed from the key when
    /// the row holds one; null for a version Cecil did not read from a row or a token that is not eight bytes.
    /// </summary>
    internal static AssemblyName? Of(AssemblyNameReference row)
    {
        byte[] token = row.PublicKeyToken;
        if (AssemblyVersion.Of(row.Version) is not { } version || token is { Length: not (0 or TokenBytes) })
            return null;
        return new(MetadataName.OfEntry(row.Name), version, MetadataName.OfEntry(row.Culture ?? ""),
            token is { Length: TokenBytes } ? BinaryPrimitives.ReadUInt64BigEndian(token) : null);
    }

    /// <summary>The assembly a type's scope names: the referenced row, or the assembly of the module that
    /// defines the type; null for a module reference or a row <see cref="Of(AssemblyNameReference)"/> refuses.
    /// </summary>
    internal static AssemblyName? OfScope(TypeReference type) => type.Scope switch
    {
        AssemblyNameReference row => Of(row),
        ModuleDefinition module => Of(module.Assembly.Name),
        _ => null
    };

    const int TokenBytes = 8;

    /// <summary>The structure literal of the assembly.</summary>
    internal string ToLean() =>
        $"{{ name := {Name.ToLean()}, version := {Version.ToLean()}, culture := {Culture.ToLean()}, " +
        $"publicKeyToken := {(PublicKeyToken is { } token ? $"some 0x{token:x16}" : "none")} }}";

    /// <summary>The text of <c>AssemblyName.display</c>, such as
    /// <c>System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a</c>.</summary>
    internal string ToDisplay() => Parts() is (string name, string culture)
        ? $"{name}, Version={Version.ToDisplay()}, Culture={culture}, PublicKeyToken={TokenText()}"
        : LeanDoc.Pretty(Repr());

    // AssemblyName.parts?: text that splits back at its separators into exactly this assembly.
    (string Name, string Culture)? Parts()
    {
        if (Name.Readable() is not { } name || Culture.Readable() is not { } culture ||
            name.Contains(',') || name.Contains(']') || culture.Contains(',') || culture.Contains(']') ||
            culture == Neutral) return null;
        return (name, culture.Length == 0 ? Neutral : culture);
    }

    const string Neutral = "neutral";

    string TokenText() => PublicKeyToken is { } token ? token.ToString("x16", CultureInfo.InvariantCulture) : "null";

    /// <summary>The text of <c>AssemblyName.scopeText?</c>, which a type display starts with.</summary>
    internal string? ScopeText()
    {
        if (Parts() is not (string name, string culture)) return null;
        return Culture == MetadataName.Empty && PublicKeyToken is null
            ? $"[{name},{Version.ToDisplay()}]" : $"[{name},{Version.ToDisplay()},{culture},{TokenText()}]";
    }

    /// <summary>The derived <c>Repr</c> of the assembly.</summary>
    internal LeanDoc Repr() => LeanDoc.Structure(("name", Name.Repr()), ("version", Version.Repr()),
        ("culture", Culture.Repr()),
        ("publicKeyToken", PublicKeyToken is { } token ? LeanDoc.Of("some ") + LeanDoc.Of(token) : LeanDoc.Of("none")));
}

/// <summary>One row of a type's nesting chain: its namespace and name columns (<c>CIL.TypeLevel</c>).</summary>
internal sealed record TypeLevel(MetadataName Namespace, MetadataName Name)
{
    /// <summary>The level of a type definition's own row.</summary>
    internal static TypeLevel Of(TypeDefinition definition) =>
        new(MetadataName.OfEntry(definition.Namespace), MetadataName.OfEntry(definition.Name));

    /// <summary>The structure literal of the level.</summary>
    internal string ToLean() => $"{{ typeNamespace := {Namespace.ToLean()}, name := {Name.ToLean()} }}";

    /// <summary>The <c>Repr</c> text of the level, which is how Lean shows a <c>TypeLevel</c>.</summary>
    internal string ToDisplay() => LeanDoc.Pretty(Repr());

    // TypeLevel.text?: a level that splits back at its last '.'.
    internal string? Text()
    {
        if (Namespace.Readable() is not { } space || Name.Readable() is not { } name ||
            space.Contains('/') || name.Contains('.') || name.Contains('/')) return null;
        return space.Length == 0 ? name : space + "." + name;
    }

    /// <summary>The derived <c>Repr</c> of the level.</summary>
    internal LeanDoc Repr() => LeanDoc.Structure(("typeNamespace", Namespace.Repr()), ("name", Name.Repr()));
}

/// <summary>A type by the assembly that holds its <c>TypeDef</c> row, its namespace and name columns, and the
/// levels of its enclosing types from the outermost (<c>CIL.TypeIdentity</c>).</summary>
internal sealed record TypeIdentity(AssemblyName Assembly, MetadataName Namespace,
    ImmutableArray<TypeLevel> Enclosing, MetadataName Name)
{
    /// <summary>The identity of a type definition, read from its row, its enclosing rows and its assembly row.
    /// A reference names the same identity once it is resolved to its definition.</summary>
    internal static TypeIdentity Of(TypeDefinition definition)
    {
        AssemblyName assembly = AssemblyName.Of(definition.Module.Assembly.Name) ??
            throw new InvalidDataException("Assembly row without a version or an eight-byte public key token: " +
                definition.Module.Assembly.Name.FullName);
        var enclosing = ImmutableArray.CreateBuilder<TypeLevel>();
        for (TypeDefinition? outer = definition.DeclaringType; outer is not null; outer = outer.DeclaringType)
            enclosing.Add(TypeLevel.Of(outer));
        enclosing.Reverse();
        return new(assembly, MetadataName.OfEntry(definition.Namespace), enclosing.ToImmutable(),
            MetadataName.OfEntry(definition.Name));
    }

    /// <summary>The structure literal of the type, without <c>enclosing</c> when the type is not nested.</summary>
    internal string ToLean() =>
        $"{{ assembly := {Assembly.ToLean()}, typeNamespace := {Namespace.ToLean()}, " +
        (Enclosing.IsEmpty ? "" : $"enclosing := [{string.Join(", ", Enclosing.Select(level => level.ToLean()))}], ") +
        $"name := {Name.ToLean()} }}";

    /// <summary>The text of <c>TypeIdentity.display</c>, such as <c>[Examples,1.0.0.0]Examples.Point</c>.</summary>
    internal string ToDisplay()
    {
        if (Assembly.ScopeText() is { } scope)
        {
            string?[] levels = [.. Enclosing.Select(level => level.Text()), new TypeLevel(Namespace, Name).Text()];
            if (levels.All(level => level is not null)) return scope + string.Join("/", levels);
        }
        return LeanDoc.Pretty(LeanDoc.Structure(("assembly", Assembly.Repr()), ("typeNamespace", Namespace.Repr()),
            ("enclosing", LeanDoc.List(Enclosing.Select(level => level.Repr()).ToArray())), ("name", Name.Repr())));
    }

    /// <summary>Equal types have equal assemblies, columns and levels.</summary>
    public bool Equals(TypeIdentity? other) => other is not null && Assembly == other.Assembly &&
        Namespace == other.Namespace && Name == other.Name && Enclosing.SequenceEqual(other.Enclosing);

    /// <summary>A hash of every component of the type.</summary>
    public override int GetHashCode()
    {
        HashCode hash = new();
        hash.Add(Assembly);
        hash.Add(Namespace);
        hash.Add(Name);
        foreach (TypeLevel level in Enclosing) hash.Add(level);
        return hash.ToHashCode();
    }
}

/// <summary>A value type ECMA-335 encodes by element type (II.23.1.16), without an assembly
/// (<c>CIL.PrimitiveType</c>).</summary>
internal closed record PrimitiveType(MetadataType ElementType, string Constructor, string Name)
{
    internal sealed record Boolean() : PrimitiveType(MetadataType.Boolean, "boolean", "Boolean");
    internal sealed record Char() : PrimitiveType(MetadataType.Char, "char", "Char");
    internal sealed record SByte() : PrimitiveType(MetadataType.SByte, "sbyte", "SByte");
    internal sealed record Byte() : PrimitiveType(MetadataType.Byte, "byte", "Byte");
    internal sealed record Int16() : PrimitiveType(MetadataType.Int16, "int16", "Int16");
    internal sealed record UInt16() : PrimitiveType(MetadataType.UInt16, "uint16", "UInt16");
    internal sealed record Int32() : PrimitiveType(MetadataType.Int32, "int32", "Int32");
    internal sealed record UInt32() : PrimitiveType(MetadataType.UInt32, "uint32", "UInt32");
    internal sealed record Int64() : PrimitiveType(MetadataType.Int64, "int64", "Int64");
    internal sealed record UInt64() : PrimitiveType(MetadataType.UInt64, "uint64", "UInt64");
    internal sealed record Single() : PrimitiveType(MetadataType.Single, "single", "Single");
    internal sealed record Double() : PrimitiveType(MetadataType.Double, "double", "Double");
    internal sealed record IntPtr() : PrimitiveType(MetadataType.IntPtr, "intPtr", "IntPtr");
    internal sealed record UIntPtr() : PrimitiveType(MetadataType.UIntPtr, "uintPtr", "UIntPtr");

    /// <summary>Every primitive, in the order of <c>CIL.PrimitiveType</c>'s constructors.</summary>
    internal static readonly ImmutableArray<PrimitiveType> All =
    [
        new Boolean(), new Char(), new SByte(), new Byte(), new Int16(), new UInt16(), new Int32(), new UInt32(),
        new Int64(), new UInt64(), new Single(), new Double(), new IntPtr(), new UIntPtr()
    ];

    /// <summary>The primitive an element type code encodes, or null for any other code.</summary>
    internal static PrimitiveType? OfElementType(MetadataType elementType) =>
        All.FirstOrDefault(primitive => primitive.ElementType == elementType);

    /// <summary>The primitive a type encodes: an element type code, or a reference into a core library, which
    /// Cecil reads as the same code. Cecil also gives that code to a type of that name in any other assembly,
    /// which is a named type and gives null here.</summary>
    internal static PrimitiveType? Of(TypeReference type) =>
        type is not (TypeSpecification or GenericParameter) && OfElementType(type.MetadataType) is { } primitive &&
        AssemblyName.OfScope(type) is { } scope && PlatformAssemblies.CoreLibraries.Contains(scope)
            ? primitive : null;

    /// <summary>The constructor term, such as <c>.int32</c>.</summary>
    internal string ToLean() => "." + Constructor;

    /// <summary>The text of <c>PrimitiveType.display</c>, such as <c>System.Int32</c>.</summary>
    internal string ToDisplay() => "System." + Name;
}

/// <summary>What metadata says a named type is (<c>CIL.TypeKind</c>).</summary>
internal closed record TypeKind
{
    internal sealed record ValueType : TypeKind;
    internal sealed record EnumType(PrimitiveType Underlying) : TypeKind;
    internal sealed record ClassType : TypeKind;
    internal sealed record InterfaceType : TypeKind;

    /// <summary>The kind of a definition from its flags and the core-library type it extends: an enumeration
    /// holds its underlying primitive, and <c>System.Enum</c> itself is a class.</summary>
    internal static TypeKind Of(TypeDefinition definition)
    {
        if (definition.IsInterface) return new InterfaceType();
        if (definition.BaseType is not { } baseType || CoreType(definition, EnumName)) return new ClassType();
        if (CoreType(baseType, EnumName)) return new EnumType(UnderlyingOf(definition));
        return CoreType(baseType, ValueTypeName) ? new ValueType() : new ClassType();
    }

    static readonly MetadataName SystemNamespace = MetadataName.OfEntry("System");
    static readonly MetadataName EnumName = MetadataName.OfEntry("Enum");
    static readonly MetadataName ValueTypeName = MetadataName.OfEntry("ValueType");

    // A top-level type of the System namespace defined or referenced in a core library.
    static bool CoreType(TypeReference type, MetadataName name) => type is not TypeSpecification &&
        type.DeclaringType is null && MetadataName.OfEntry(type.Namespace) == SystemNamespace &&
        MetadataName.OfEntry(type.Name) == name && AssemblyName.OfScope(type) is { } scope &&
        PlatformAssemblies.CoreLibraries.Contains(scope);

    // ECMA-335 II.14.3: an enumeration has exactly one instance field, of its underlying primitive type.
    static PrimitiveType UnderlyingOf(TypeDefinition definition)
    {
        var instance = definition.Fields.Where(field => !field.IsStatic).ToArray();
        return instance is [var field] && PrimitiveType.Of(field.FieldType) is { } primitive ? primitive :
            throw new InvalidDataException("Enumeration without one primitive instance field: " + definition.FullName);
    }

    /// <summary>The constructor term, such as <c>.valueType</c> or <c>(.enumType .int32)</c>.</summary>
    internal string ToLean() => this switch
    {
        ValueType => ".valueType",
        EnumType kind => $"(.enumType {kind.Underlying.ToLean()})",
        ClassType => ".classType",
        InterfaceType => ".interfaceType"
    };

    /// <summary>The <c>Repr</c> text of the kind, which is how Lean shows a <c>TypeKind</c>.</summary>
    internal string ToDisplay() => this switch
    {
        ValueType => "CIL.TypeKind.valueType",
        EnumType kind => $"CIL.TypeKind.enumType (CIL.PrimitiveType.{kind.Underlying.Constructor})",
        ClassType => "CIL.TypeKind.classType",
        InterfaceType => "CIL.TypeKind.interfaceType"
    };
}

/// <summary>The assemblies of the .NET 11 platform the extractor models, as <c>AssemblyRef</c> rows name them.
/// System.Runtime forwards its types to System.Private.CoreLib, which holds their <c>TypeDef</c> rows.</summary>
internal static class PlatformAssemblies
{
    /// <summary>The version every platform assembly carries.</summary>
    internal static readonly AssemblyVersion Version = new(11, 0, 0, 0);

    /// <summary>The token of the key that signs System.Runtime.</summary>
    internal const ulong MicrosoftKeyToken = 0xb03f5f7f11d50a3a;

    /// <summary>The token of the key that signs System.Memory and System.Runtime.Intrinsics.</summary>
    internal const ulong OpenKeyToken = 0xcc7b13ffcd2ddd51;

    /// <summary>The token of the key that signs System.Private.CoreLib.</summary>
    internal const ulong CoreLibraryKeyToken = 0x7cec85d7bea7798e;

    /// <summary>The token of the ECMA key, which signs mscorlib and other platform facades.</summary>
    internal const ulong EcmaKeyToken = 0xb77a5c561934e089;

    /// <summary>The tokens of every key that signs a platform assembly; only the runtime answers their names.
    /// </summary>
    internal static readonly ImmutableArray<ulong> KeyTokens =
        [MicrosoftKeyToken, OpenKeyToken, CoreLibraryKeyToken, EcmaKeyToken];

    /// <summary>System.Runtime, the core library a .NET 11 assembly references.</summary>
    internal static readonly AssemblyName SystemRuntime = Signed("System.Runtime", MicrosoftKeyToken);

    /// <summary>System.Memory.</summary>
    internal static readonly AssemblyName SystemMemory = Signed("System.Memory", OpenKeyToken);

    /// <summary>System.Runtime.Intrinsics.</summary>
    internal static readonly AssemblyName SystemRuntimeIntrinsics = Signed("System.Runtime.Intrinsics", OpenKeyToken);

    /// <summary>System.Private.CoreLib, which defines the types System.Runtime forwards.</summary>
    internal static readonly AssemblyName CoreLibrary = Signed("System.Private.CoreLib", CoreLibraryKeyToken);

    /// <summary>The assemblies whose <c>System</c> types are the primitives and the bases of value types.
    /// </summary>
    internal static readonly ImmutableArray<AssemblyName> CoreLibraries = [SystemRuntime, CoreLibrary];

    /// <summary>The modelled platform assemblies a reference's simple name can claim.</summary>
    internal static readonly ImmutableArray<AssemblyName> Modelled =
        [SystemRuntime, SystemMemory, SystemRuntimeIntrinsics];

    /// <summary>The modelled platform assembly whose simple name a scope carries, or null.</summary>
    internal static AssemblyName? Claimed(IMetadataScope scope)
    {
        MetadataName name = MetadataName.OfEntry(scope.Name);
        return Modelled.FirstOrDefault(platform => platform.Name == name);
    }

    static AssemblyName Signed(string name, ulong token) =>
        new(MetadataName.OfEntry(name), Version, MetadataName.Empty, token);
}

/// <summary>A Lean <c>Std.Format</c> document of text, line breaks, nesting and all-or-none groups, laid out by
/// Lean's algorithm, so a <c>Repr</c> built here prints as <c>reprStr</c> prints it.</summary>
internal closed record LeanDoc
{
    internal sealed record Text(string Value) : LeanDoc;
    internal sealed record Line : LeanDoc;
    internal sealed record Nest(int Indent, LeanDoc Body) : LeanDoc;
    internal sealed record Group(LeanDoc Body) : LeanDoc;
    internal sealed record Append(LeanDoc Left, LeanDoc Right) : LeanDoc;

    /// <summary>Text without a line break.</summary>
    internal static LeanDoc Of(string text) => new Text(text);

    /// <summary>A natural number, as <c>Repr Nat</c> writes it.</summary>
    internal static LeanDoc Of(ulong value) => new Text(value.ToString(CultureInfo.InvariantCulture));

    /// <summary>Two documents one after the other.</summary>
    public static LeanDoc operator +(LeanDoc left, LeanDoc right) => new Append(left, right);

    // Std.Format.bracket: a group nested by the width of its opening text.
    static LeanDoc Bracket(string open, LeanDoc body, string close) =>
        new Group(new Nest(IdentityText.Columns(open), Of(open) + body + Of(close)));

    static readonly LeanDoc Separator = Of(",") + new Line();

    /// <summary>The derived <c>Repr</c> of a structure with these fields.</summary>
    internal static LeanDoc Structure(params (string Field, LeanDoc Value)[] fields)
    {
        LeanDoc body = Of("");
        for (int index = 0; index < fields.Length; index++)
        {
            if (index != 0) body += Separator;
            var (field, value) = fields[index];
            body += Of(field) + Of(FieldSeparator) + new Group(new Nest(field.Length + FieldSeparator.Length, value));
        }
        return Bracket("{ ", body, " }");
    }

    const string FieldSeparator = " := ";

    /// <summary>The <c>Repr</c> of a list of values that are not atoms.</summary>
    internal static LeanDoc List(IReadOnlyList<LeanDoc> items) => items.Count == 0 ? Of("[]") :
        Bracket("[", items.Skip(1).Aggregate(items[0], (joined, item) => joined + Separator + item), "]");

    /// <summary>The width <c>Std.Format.defWidth</c> that <c>reprStr</c> lays text out in.</summary>
    internal const int DefaultWidth = 120;

    // Std.Format.prettyM: work groups, each flattened when it and the text up to the next break fit.
    enum Flatten { Disallowed, Fits, Overflows }

    sealed record Item(LeanDoc Document, int Indent);

    sealed record Cons<T>(T Head, Cons<T>? Tail);

    sealed record WorkGroup(Flatten Flatten, Cons<Item>? Items);

    readonly record struct Space(bool FoundLine, int Width);

    /// <summary>The text Lean's <c>Format.pretty</c> lays <paramref name="document"/> out as.</summary>
    internal static string Pretty(LeanDoc document, int width = DefaultWidth)
    {
        StringBuilder output = new();
        int column = 0;
        Cons<WorkGroup>? groups = new(new(Flatten.Disallowed, new(new(document, 0), null)), null);
        while (groups is not null)
        {
            WorkGroup group = groups.Head;
            if (group.Items is null)
            {
                groups = groups.Tail;
                continue;
            }
            Item item = group.Items.Head;
            Cons<WorkGroup>? rest = groups.Tail;
            Cons<WorkGroup> With(Cons<Item>? items) => new(group with { Items = items }, rest);
            switch (item.Document)
            {
                case Text text:
                    output.Append(text.Value);
                    column += IdentityText.Columns(text.Value);
                    groups = With(group.Items.Tail);
                    break;
                case Append append:
                    groups = With(new(item with { Document = append.Left },
                        new(item with { Document = append.Right }, group.Items.Tail)));
                    break;
                case Nest nest:
                    groups = With(new(new(nest.Body, item.Indent + nest.Indent), group.Items.Tail));
                    break;
                case Line when group.Flatten == Flatten.Fits:
                    output.Append(' ');
                    column++;
                    groups = With(group.Items.Tail);
                    break;
                case Line:
                    output.Append('\n').Append(' ', item.Indent);
                    column = item.Indent;
                    groups = With(group.Items.Tail);
                    break;
                case Group inner when group.Flatten == Flatten.Fits:
                    groups = With(new(item with { Document = inner.Body }, group.Items.Tail));
                    break;
                case Group inner:
                    groups = Push(new(item with { Document = inner.Body }, null), With(group.Items.Tail), width,
                        column);
                    break;
            }
        }
        return output.ToString();
    }

    // pushGroup: the group flattens when it and what follows it up to the next line break fit the line.
    static Cons<WorkGroup> Push(Cons<Item> items, Cons<WorkGroup> groups, int width, int column)
    {
        int available = Math.Max(0, width - column);
        WorkGroup group = new(Flatten.Fits, items);
        Space own = UpToLine(new(group, null), available);
        Space total = Merge(available, own, remaining => UpToLine(groups, remaining));
        return new(group with { Flatten = total.Width <= available ? Flatten.Fits : Flatten.Overflows }, groups);
    }

    static Space Merge(int width, Space first, Func<int, Space> rest)
    {
        if (first.Width > width || first.FoundLine) return first;
        Space second = rest(width - first.Width);
        return second with { Width = first.Width + second.Width };
    }

    static Space UpToLine(Cons<WorkGroup>? groups, int width)
    {
        if (groups is null) return default;
        if (groups.Head.Items is not { } items) return UpToLine(groups.Tail, width);
        return Merge(width, UpToLine(items.Head.Document, groups.Head.Flatten == Flatten.Fits, width),
            remaining => UpToLine(new(groups.Head with { Items = items.Tail }, groups.Tail), remaining));
    }

    static Space UpToLine(LeanDoc document, bool flatten, int width) => document switch
    {
        Text text => new(false, IdentityText.Columns(text.Value)),
        Line => flatten ? new(false, 1) : new(true, 0),
        Nest nest => UpToLine(nest.Body, flatten, width),
        Group group => UpToLine(group.Body, true, width),
        Append append => Merge(width, UpToLine(append.Left, flatten, width),
            remaining => UpToLine(append.Right, flatten, remaining))
    };
}

/// <summary>The codes, escapes and fallbacks CIL/Identity.lean gives names and literals.</summary>
internal static class IdentityText
{
    static readonly UTF8Encoding StrictUtf8 = new(false, true);

    /// <summary>The UTF-8 bytes of a name; a lone surrogate, which no <c>#Strings</c> entry decodes to, fails.
    /// </summary>
    internal static byte[] Utf8(string text)
    {
        try
        {
            return StrictUtf8.GetBytes(text);
        }
        catch (EncoderFallbackException error)
        {
            throw new InvalidDataException("Metadata name without UTF-8 bytes: " + error.Message, error);
        }
    }

    /// <summary>The text of UTF-8 bytes, or null when they are not UTF-8, as <c>String.fromUTF8?</c> decides.
    /// </summary>
    internal static string? DecodeUtf8(byte[] bytes)
    {
        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException)
        {
            return null;
        }
    }

    /// <summary>Whether every surrogate in <paramref name="units"/> is a high one followed by a low one.</summary>
    internal static bool WellFormed(ReadOnlySpan<char> units)
    {
        for (int index = 0; index < units.Length; index++)
        {
            if (!char.IsSurrogate(units[index])) continue;
            if (!char.IsHighSurrogate(units[index]) || index + 1 == units.Length ||
                !char.IsLowSurrogate(units[index + 1])) return false;
            index++;
        }
        return true;
    }

    /// <summary>The bytes after a leading 1 as one big-endian number.</summary>
    internal static BigInteger Code(ReadOnlySpan<byte> bytes)
    {
        byte[] digits = new byte[bytes.Length + 1];
        digits[0] = 1;
        bytes.CopyTo(digits.AsSpan(1));
        return new(digits, isUnsigned: true, isBigEndian: true);
    }

    /// <summary>The UTF-16 code units after a leading 1 as one big-endian number in base 65536.</summary>
    internal static BigInteger Code(ReadOnlySpan<char> units)
    {
        byte[] digits = new byte[2 * units.Length + 2];
        digits[1] = 1;
        for (int index = 0; index < units.Length; index++)
            BinaryPrimitives.WriteUInt16BigEndian(digits.AsSpan(2 * index + 2), units[index]);
        return new(digits, isUnsigned: true, isBigEndian: true);
    }

    /// <summary>The raw structure of a code, <c>rawCodeDisplay</c>.</summary>
    internal static string RawCode(BigInteger code) =>
        "{ code := " + code.ToString(CultureInfo.InvariantCulture) + " }";

    /// <summary>The number of characters Lean counts in <paramref name="text"/>: its Unicode scalar values.
    /// </summary>
    internal static int Columns(string text)
    {
        int count = 0;
        foreach (Rune _ in text.EnumerateRunes()) count++;
        return count;
    }

    /// <summary>Inclusive code point ranges of <c>CIL.invisibleRanges</c>: Unicode categories Cc, Cf, Zl and Zp
    /// and the non-ASCII characters of Zs.</summary>
    internal static readonly ImmutableArray<(int Low, int High)> InvisibleRanges =
    [
        (0x0000, 0x001F), (0x007F, 0x00A0), (0x00AD, 0x00AD), (0x0600, 0x0605), (0x061C, 0x061C),
        (0x06DD, 0x06DD), (0x070F, 0x070F), (0x0890, 0x0891), (0x08E2, 0x08E2), (0x1680, 0x1680),
        (0x180E, 0x180E), (0x2000, 0x200F), (0x2028, 0x202F), (0x205F, 0x2064), (0x2066, 0x206F),
        (0x3000, 0x3000), (0xFEFF, 0xFEFF), (0xFFF9, 0xFFFB), (0x110BD, 0x110BD), (0x110CD, 0x110CD),
        (0x13430, 0x1343F), (0x1BCA0, 0x1BCA3), (0x1D173, 0x1D17A), (0xE0001, 0xE0001), (0xE0020, 0xE007F)
    ];

    static bool Invisible(Rune rune)
    {
        foreach (var (low, high) in InvisibleRanges)
            if (low <= rune.Value && rune.Value <= high) return true;
        return false;
    }

    const int UnicodeEscapeLimit = 0x10000;

    // escapedText?: null when an invisible character lies above U+FFFF, which a Lean string cannot escape.
    static string? Escaped(string text, bool quoted)
    {
        StringBuilder escaped = new(text.Length);
        foreach (Rune rune in text.EnumerateRunes())
        {
            bool invisible = Invisible(rune);
            if (invisible && rune.Value >= UnicodeEscapeLimit) return null;
            if (rune.Value == '\\') escaped.Append(@"\\");
            else if (quoted && rune.Value == '"') escaped.Append("\\\"");
            else if (invisible) escaped.Append(CultureInfo.InvariantCulture, $"\\u{rune.Value:X4}");
            else escaped.Append(rune.ToString());
        }
        return escaped.ToString();
    }

    /// <summary>The text <c>readableText?</c> writes: escaped, with a leading <c>{</c> written <c>\{</c>.
    /// </summary>
    internal static string? Readable(string text) =>
        Escaped(text, false) is { } escaped ? (text.StartsWith('{') ? "\\" + escaped : escaped) : null;

    /// <summary>The Lean string literal <c>quotedText?</c> writes for <paramref name="text"/>.</summary>
    internal static string? Quoted(string text) => Escaped(text, true) is { } escaped ? "\"" + escaped + "\"" : null;
}
