using Mono.Cecil;

namespace Nethermind.LeanCIL;

/// <summary>Exact signature nodes owned by one live pinned metadata session.</summary>
internal sealed class StructuralSignatures(PinnedAssemblies owner)
{
    /// <summary>A canonical node whose identity is meaningful only in its owning live session.</summary>
    internal readonly struct Signature(StructuralSignatures session, int id) : IEquatable<Signature>,
        IComparable<Signature>
    {
        internal int Id { get; } = id;
        internal StructuralSignatures Session { get; } = session;
        public bool Equals(Signature other)
        {
            Session.RequireLive();
            if (!ReferenceEquals(Session, other.Session))
                throw new InvalidDataException("Signature belongs to another pinned session");
            return Id == other.Id;
        }
        public override bool Equals(object? other) => other is Signature signature && Equals(signature);
        public override int GetHashCode() { Session.RequireLive(); return Id; }
        public int CompareTo(Signature other)
        {
            _ = Equals(other);
            return Id.CompareTo(other.Id);
        }
        public static bool operator ==(Signature left, Signature right) => left.Equals(right);
        public static bool operator !=(Signature left, Signature right) => !left.Equals(right);
    }

    sealed class Trie
    {
        internal readonly SortedDictionary<long, Trie> Children = [];
        internal int Id;
    }

    /// <summary>An immutable TypeSystem object's admitted module, row or implicit named scope.</summary>
    internal sealed record Primitive(TypeReference Type, ModuleDefinition Module, MetadataImage Image,
        uint Token, uint Assembly, string Name);

    readonly Trie root = new();
    readonly SortedDictionary<(byte Value, int Suffix), int> nameNodes = [];
    readonly Dictionary<MetadataImage, SortedDictionary<int, int>> heapNames = [];
    readonly Dictionary<MetadataImage, SortedDictionary<uint, int>> namedTypes = [];
    readonly Dictionary<MetadataImage, SortedDictionary<uint, int>> assemblies = [];
    readonly Dictionary<TypeReference, Primitive> primitives = new(ReferenceEqualityComparer.Instance);
    readonly Dictionary<MethodDefinition, int> methods = new(ReferenceEqualityComparer.Instance);
    int nextId;
    int nextName;
    bool disposed;
    internal long HeapBytes { get; private set; }
    internal long RawRows { get; private set; }
    internal long NodeVisits { get; private set; }
    internal long EdgeVisits { get; private set; }
    internal long TrieProbes { get; private set; }

    internal static StructuralSignatures Current => (PinnedAssemblies.Active ??
        throw new InvalidDataException("Signature requires a pinned metadata session")).Signatures;

    void RequireLive()
    {
        if (disposed || !ReferenceEquals(PinnedAssemblies.Active, owner))
            throw new InvalidDataException("Signature session is not active");
    }

    int Intern(IEnumerable<long> tokens)
    {
        Trie node = root;
        foreach (long token in tokens)
        {
            TrieProbes++;
            if (!node.Children.TryGetValue(token, out var child)) node.Children.Add(token, child = new());
            node = child;
        }
        if (node.Id == 0) node.Id = checked(++nextId);
        return node.Id;
    }

    int Cons(byte value, int suffix)
    {
        if (nameNodes.TryGetValue((value, suffix), out int id)) return id;
        nameNodes.Add((value, suffix), id = checked(++nextName));
        return id;
    }

    int Name(ReadOnlySpan<byte> bytes)
    {
        int id = 0;
        for (int index = bytes.Length - 1; index >= 0; index--) id = Cons(bytes[index], id);
        return id;
    }

    int Name(MetadataImage image, int offset)
    {
        if (!heapNames.TryGetValue(image, out var cache)) heapNames.Add(image, cache = []);
        int cursor = offset;
        var pending = new List<byte>();
        while (!cache.TryGetValue(cursor, out _))
        {
            byte value = image.StringByte(cursor);
            HeapBytes++;
            if (value == 0) { cache.Add(cursor, 0); break; }
            pending.Add(value);
            cursor = checked(cursor + 1);
        }
        int id = cache[cursor];
        for (int index = pending.Count - 1; index >= 0; index--)
            cache.Add(--cursor, id = Cons(pending[index], id));
        return id;
    }

    int Assembly(MetadataImage image, uint token)
    {
        if (!assemblies.TryGetValue(image, out var cache)) assemblies.Add(image, cache = []);
        if (cache.TryGetValue(token, out int id)) return id;
        var identity = image.AssemblyColumns(token) ?? throw new InvalidDataException("Invalid assembly identity");
        var version = identity.Version;
        ulong key = identity.PublicKeyToken ?? 0;
        id = Intern([1, Name(image, identity.Name), Name(image, identity.Culture), version.Major, version.Minor,
            version.Build, version.Revision, identity.PublicKeyToken.HasValue ? 1 : 0, (uint)(key >> 32), (uint)key]);
        cache.Add(token, id);
        return id;
    }

    int Named(MetadataImage image, uint token)
    {
        if (!namedTypes.TryGetValue(image, out var cache)) namedTypes.Add(image, cache = []);
        var pending = new List<(uint Token, MetadataImage.NamedRow Row)>();
        var visiting = new SortedSet<uint>();
        int parent = 0;
        while (!cache.TryGetValue(token, out parent))
        {
            if (!visiting.Add(token)) throw new InvalidDataException("Cyclic named type identity");
            var row = image.NamedType(token);
            RawRows++;
            pending.Add((token, row));
            if (row.Parent == 0) break;
            token = row.Parent;
        }
        for (int index = pending.Count - 1; index >= 0; index--)
        {
            var entry = pending[index];
            parent = Intern([2, entry.Row.Parent == 0 ? Assembly(image, entry.Row.Assembly) : 0,
                parent, Name(image, entry.Row.Namespace), Name(image, entry.Row.Name)]);
            cache.Add(entry.Token, parent);
        }
        return parent;
    }

    int Leaf(TypeReference type)
    {
        if (primitives.TryGetValue(type, out var primitive))
        {
            owner.RequireRegistered(primitive.Module);
            return primitive.Token != 0 ? Named(primitive.Image, primitive.Token) :
                Intern([2, Assembly(primitive.Image, primitive.Assembly), 0,
                    Name("System"u8), Name(IdentityText.Utf8(primitive.Name))]);
        }
        owner.RequireRegistered(type.Module);
        var image = owner.IdentityMetadata(type.Module);
        IdentityRows.RequireModule(image, type.Module);
        return Named(image, type.MetadataToken.ToUInt32());
    }

    sealed record Snapshot(long[] Prefix, TypeReference[] Children);

    Snapshot Describe(TypeReference type)
    {
        switch (type)
        {
            case GenericParameter parameter:
                var module = parameter.Owner switch
                {
                    MethodReference { DeclaringType: not null } method => method.Module,
                    TypeReference declaring => declaring.Module,
                    _ => null
                };
                if (module is null) throw new InvalidDataException("Generic parameter owner has no module");
                owner.RequireRegistered(module);
                if (parameter.Position < 0 || parameter.Position >= parameter.Owner.GenericParameters.Count ||
                    parameter.Type is not (GenericParameterType.Method or
                    GenericParameterType.Type)) throw new InvalidDataException("Malformed generic parameter");
                return new([3, (int)parameter.Type, parameter.Position], []);
            case GenericInstanceType instance:
                if (instance.ElementType is TypeSpecification or GenericParameter)
                    throw new InvalidDataException("Generic application requires a named constructor");
                return new([4, instance.GenericArguments.Count], [instance.ElementType, .. instance.GenericArguments]);
            case RequiredModifierType modifier: return new([5], [modifier.ModifierType, modifier.ElementType]);
            case OptionalModifierType modifier: return new([6], [modifier.ModifierType, modifier.ElementType]);
            case ByReferenceType reference: return new([7], [reference.ElementType]);
            case PointerType pointer: return new([8], [pointer.ElementType]);
            case PinnedType pinned: return new([9], [pinned.ElementType]);
            case SentinelType sentinel: return new([10], [sentinel.ElementType]);
            case ArrayType { IsVector: true } array: return new([11], [array.ElementType]);
            case ArrayType array:
                var bounds = new List<long> { 12, array.Rank };
                foreach (var dimension in array.Dimensions)
                {
                    bounds.Add(dimension.LowerBound.HasValue ? 1 : 0);
                    bounds.Add(dimension.LowerBound ?? 0);
                    bounds.Add(dimension.UpperBound.HasValue ? 1 : 0);
                    bounds.Add(dimension.UpperBound ?? 0);
                }
                return new([.. bounds], [array.ElementType]);
            case FunctionPointerType pointer:
                return new([13, (int)pointer.CallingConvention, pointer.HasThis ? 1 : 0,
                    pointer.ExplicitThis ? 1 : 0, pointer.Parameters.Count],
                    [pointer.ReturnType, .. pointer.Parameters.Select(parameter => parameter.ParameterType)]);
            case TypeSpecification:
                throw new InvalidDataException("Unsupported structural type specification");
            default: return new([], []);
        }
    }

    /// <summary>A fresh iterative snapshot observes every mutable wrapper once and rejects cycles.</summary>
    internal Signature Type(TypeReference type)
        => new(this, Types([type])[0]);

    /// <summary>An ordered signature list shares one snapshot across all of its roots.</summary>
    internal Signature Ordered(IEnumerable<TypeReference> roots)
    {
        int[] types = Types([.. roots]);
        return new(this, Intern(new long[] { 16, types.Length }.Concat(types.Select(id => (long)id))));
    }

    /// <summary>All roots in one read-only layout collection share their completed descendants.</summary>
    internal Func<TypeReference, Signature> LayoutSnapshot()
    {
        Dictionary<TypeReference, int> complete = new(ReferenceEqualityComparer.Instance);
        return type => new(this, Types([type], complete)[0]);
    }

    int[] Types(TypeReference[] roots, Dictionary<TypeReference, int>? complete = null)
    {
        RequireLive();
        complete ??= new(ReferenceEqualityComparer.Instance);
        var visiting = new HashSet<TypeReference>(ReferenceEqualityComparer.Instance);
        var work = new Stack<(TypeReference Type, Snapshot? Snapshot)>();
        for (int index = roots.Length - 1; index >= 0; index--) work.Push((roots[index], null));
        while (work.TryPop(out var entry))
        {
            if (complete.ContainsKey(entry.Type)) continue;
            if (entry.Snapshot is { } snapshot)
            {
                int id = snapshot.Prefix.Length == 0 ? Leaf(entry.Type) :
                    Intern(snapshot.Prefix.Concat(snapshot.Children.Select(child => (long)complete[child])));
                complete.Add(entry.Type, id);
                visiting.Remove(entry.Type);
                continue;
            }
            if (!visiting.Add(entry.Type)) throw new InvalidDataException("Cyclic structural signature");
            NodeVisits++;
            var description = Describe(entry.Type);
            EdgeVisits += description.Children.Length;
            work.Push((entry.Type, description));
            for (int index = description.Children.Length - 1; index >= 0; index--)
                work.Push((description.Children[index], null));
        }
        return roots.Select(type => complete[type]).ToArray();
    }

    /// <summary>The original method, closed owner and ordered method arguments form one exact key.</summary>
    internal Signature Specialization(MethodDefinition method, TypeReference declaring,
        IEnumerable<TypeReference> arguments)
    {
        RequireLive();
        method = MethodSpecialization.Definition(method);
        owner.RequireRegistered(method.Module);
        if (!methods.TryGetValue(method, out int definition)) methods.Add(method, definition = methods.Count + 1);
        int[] types = Types([declaring, .. arguments]);
        return new(this, Intern(new long[] { 14, definition, types[0], types.Length - 1 }
            .Concat(types.Skip(1).Select(id => (long)id))));
    }

    /// <summary>A method signature erases only the separately validated in and init tags.</summary>
    internal Signature ErasedMethod(MethodDefinition method)
    {
        RequireLive();
        int[] types = Types([InitAccessors.Return(method.ReturnType),
            .. method.Parameters.Select(parameter => InReferences.Parameter(parameter.ParameterType))]);
        return new(this, Intern(new long[] { 15, method.HasThis ? 1 : 0, method.ExplicitThis ? 1 : 0,
            (int)method.CallingConvention, method.GenericParameters.Count, types[0], types.Length - 1 }
            .Concat(types.Skip(1).Select(id => (long)id))));
    }

    /// <summary>Whether Cecil read an implicit element type through its module's TypeSystem.</summary>
    internal bool IsPrimitiveElement(TypeReference type) => primitives.ContainsKey(type);

    internal Primitive[] Prepare(ModuleDefinition module, MetadataImage image, AssemblyNameReference[] scopes)
    {
        var system = module.TypeSystem;
        // Core-library types have definition rows and need no implicit primitive registration.
        if (ReferenceEquals(system.CoreLibrary, module)) return [];
        (TypeReference Type, string Name)[] entries = [(system.Void, "Void"), (system.Boolean, "Boolean"),
            (system.Char, "Char"), (system.SByte, "SByte"), (system.Byte, "Byte"), (system.Int16, "Int16"),
            (system.UInt16, "UInt16"), (system.Int32, "Int32"), (system.UInt32, "UInt32"),
            (system.Int64, "Int64"), (system.UInt64, "UInt64"), (system.Single, "Single"),
            (system.Double, "Double"), (system.IntPtr, "IntPtr"), (system.UIntPtr, "UIntPtr"),
            (system.String, "String"), (system.Object, "Object"), (system.TypedReference, "TypedReference")];
        var result = new List<Primitive>();
        var scopeTokens = new Dictionary<AssemblyNameReference, uint>(ReferenceEqualityComparer.Instance);
        foreach (var scope in scopes) scopeTokens.Add(scope, scope.MetadataToken.ToUInt32());
        if (system.CoreLibrary is AssemblyNameReference { MetadataToken.RID: 0 } synthetic &&
            !scopeTokens.ContainsKey(synthetic))
            module.AssemblyReferences.Remove(synthetic);
        foreach (var (type, name) in entries)
        {
            if (primitives.ContainsKey(type) || !ReferenceEquals(type.Module, module))
                throw new InvalidDataException("TypeSystem object lacks unique module provenance");
            uint token = type.MetadataToken.ToUInt32();
            uint assembly = 0;
            if (type.MetadataToken.RID == 0)
            {
                if (type.Namespace != "System" || type.Name != name || type.DeclaringType is not null)
                    throw new InvalidDataException("Invalid implicit TypeSystem identity");
                if (ReferenceEquals(type.Scope, module)) assembly = 0x20000001;
                else if (type.Scope is AssemblyNameReference reference &&
                    scopeTokens.TryGetValue(reference, out var row))
                    assembly = row;
                // Cecil synthesizes a core scope for images with no core-library reference.
                else if (ReferenceEquals(type.Scope, system.CoreLibrary) &&
                    type.Scope is AssemblyNameReference { MetadataToken.RID: 0 })
                    continue;
                else throw new InvalidDataException("TypeSystem scope lacks image provenance");
                if (image.AssemblyColumns(assembly) is null)
                    throw new InvalidDataException("Invalid TypeSystem scope");
                token = 0;
            }
            else _ = image.NamedType(token);
            result.Add(new(type, module, image, token, assembly, name));
        }
        return [.. result];
    }

    internal void Publish(Primitive[] entries)
    {
        int added = 0;
        try { foreach (var entry in entries) { primitives.Add(entry.Type, entry); added++; } }
        catch { for (int index = 0; index < added; index++) primitives.Remove(entries[index].Type); throw; }
    }

    internal void Remove(Primitive[] entries)
    {
        foreach (var entry in entries) primitives.Remove(entry.Type);
    }

    internal void Dispose()
    {
        disposed = true;
        root.Children.Clear();
        nameNodes.Clear();
        heapNames.Clear();
        namedTypes.Clear();
        assemblies.Clear();
        primitives.Clear();
        methods.Clear();
    }
}
