using System.Collections.Immutable;
using System.Globalization;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using MemberReference = Mono.Cecil.MemberReference;
using TypeReference = Mono.Cecil.TypeReference;
using MethodDefinition = Mono.Cecil.MethodDefinition;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;
using SrmTypeDefinition = System.Reflection.Metadata.TypeDefinition;

namespace Nethermind.LeanCIL;

/// <summary>
/// The metadata tables and heaps of one module image, read with System.Reflection.Metadata: the raw bytes of
/// a table row or heap entry at the position the image gives it.
/// </summary>
internal sealed class MetadataImage
{
    readonly ImmutableArray<byte> bytes;

    internal MetadataImage(PEReader image)
    {
        Reader = image.GetMetadataReader();
        bytes = image.GetMetadata().GetContent();
    }

    internal MetadataReader Reader { get; }

    internal int Count(int table) => Reader.GetTableRowCount((TableIndex)table);

    Dictionary<int, uint>? nesting;

    /// <summary>The NestedClass row of a nested type, from a map of the table built on first use.</summary>
    internal uint? NestedClassRow(int typeRow)
    {
        if (nesting is null)
        {
            nesting = [];
            var width = Reader.GetTableRowSize(TableIndex.NestedClass) / 2;
            for (var row = 1; row <= Count(0x29); row++)
            {
                var bytes = Row(0x29000000 + (uint)row);
                var nested = 0;
                for (var index = width - 1; index >= 0; index--) nested = nested * 256 + bytes[index];
                nesting.TryAdd(nested, 0x29000000 + (uint)row);
            }
        }
        return nesting.TryGetValue(typeRow, out var found) ? found : null;
    }

    /// <summary>The bytes of the row a token names.</summary>
    internal byte[] Row(uint token)
    {
        var table = (TableIndex)(token >> 24);
        var size = Reader.GetTableRowSize(table);
        var at = Reader.GetTableMetadataOffset(table) + ((int)(token & 0xFFFFFF) - 1) * size;
        var row = bytes.AsSpan(at, size).ToArray();
        // A MethodDef row's first column is the body's address, which moves whenever an earlier body changes
        // size; the carried row has it zeroed so that no method's evidence depends on another method's body.
        if (table == TableIndex.MethodDef) row.AsSpan(0, sizeof(uint)).Clear();
        return row;
    }

    /// <summary>The first <c>Field</c> row of a <c>TypeDef</c> row: its <c>FieldList</c> column.</summary>
    internal uint FieldList(byte[] typeDefRow)
    {
        var width = Reader.GetTableRowCount(TableIndex.Field) < 0x10000 ? 2 : 4;
        var methodWidth = Reader.GetTableRowCount(TableIndex.MethodDef) < 0x10000 ? 2 : 4;
        var at = typeDefRow.Length - width - methodWidth;
        return width == 2 ? BitConverter.ToUInt16(typeDefRow, at) : BitConverter.ToUInt32(typeDefRow, at);
    }

    /// <summary>A <c>#Strings</c> entry through its terminating zero.</summary>
    internal byte[] StringEntry(int offset)
    {
        var start = Reader.GetHeapMetadataOffset(HeapIndex.String) + offset;
        var end = start;
        while (bytes[end] != 0) end++;
        return bytes.AsSpan(start, end - start + 1).ToArray();
    }

    /// <summary>A <c>#Blob</c> or <c>#US</c> entry with its compressed length.</summary>
    internal byte[] SizedEntry(HeapIndex heap, int offset)
    {
        var start = Reader.GetHeapMetadataOffset(heap) + offset;
        var first = bytes[start];
        var (header, length) = first switch
        {
            < 0x80 => (1, (int)first),
            < 0xC0 => (2, ((first & 0x3F) << 8) | bytes[start + 1]),
            _ => (4, ((first & 0x1F) << 24) | (bytes[start + 1] << 16) | (bytes[start + 2] << 8) | bytes[start + 3])
        };
        return bytes.AsSpan(start, header + length).ToArray();
    }

    /// <summary>The table stream header: the bytes from the reserved word through the last row count.</summary>
    internal byte[] TableHeader()
    {
        var tables = Enumerable.Range(0, 64).Where(table => Count(table) > 0).ToArray();
        var length = 24 + 4 * tables.Length;
        var start = tables.Min(table => Reader.GetTableMetadataOffset((TableIndex)table)) - length;
        var header = bytes.AsSpan(start, length).ToArray();
        if (header[4] != 2 || header[5] != 0)
            throw new InvalidDataException("The metadata table stream header was not found where its tables imply.");
        return header;
    }
}

/// <summary>
/// The table rows and heap entries a method's tokens, its own definition and its locals reach, with one small
/// header block per pinned assembly. Lean decodes the rows and checks every token operand, local type and the
/// method's identity against them; that the copied bytes are the image's bytes stays the extractor's claim.
/// </summary>
internal sealed class MetadataSlices(PinnedAssemblies pinned)
{
    /// <summary>The identity block of a pinned module: its table stream header and <c>Assembly</c> row.</summary>
    internal string AssemblyBlock(ModuleDefinition module)
    {
        var image = pinned.Metadata(module);
        var reader = image.Reader;
        var assembly = reader.GetAssemblyDefinition();
        var strings = new SortedDictionary<int, byte[]>();
        var blobs = new SortedDictionary<int, byte[]>();
        foreach (var handle in new[] { assembly.Name, assembly.Culture })
            strings[reader.GetHeapOffset(handle)] = image.StringEntry(reader.GetHeapOffset(handle));
        blobs[reader.GetHeapOffset(assembly.PublicKey)] =
            image.SizedEntry(HeapIndex.Blob, reader.GetHeapOffset(assembly.PublicKey));
        var identity = pinned.Original(module).Assembly.Name.FullName;
        return $"{{ identity := {System.Text.Json.JsonSerializer.Serialize(identity)}, " +
            $"tableHeader := {Bytes(image.TableHeader())}, assemblyRow := {Bytes(image.Row(0x20000001))}, " +
            $"strings := {Entries(strings)}, blobs := {Entries(blobs)} }}";
    }

    readonly Dictionary<ModuleDefinition, Collection> collections = [];

    /// <summary>Add one method's definition and tokens to the slices of its module.</summary>
    internal void Add(MethodDefinition original, IEnumerable<uint> tokens, bool classOwner)
    {
        var module = pinned.Original(original.Module);
        if (!collections.TryGetValue(module, out var collection)) collections[module] = collection = new Collection(pinned);
        var own = collection.SliceOf(original.Module);
        own.Method(original, classOwner);
        foreach (var token in tokens) own.Token(token);
    }

    /// <summary>The Lean name of the slices every method of a module shares.</summary>
    internal string Name(ModuleDefinition module) =>
        $"module{pinned.Index(pinned.Working(pinned.Original(module)))}Metadata";

    /// <summary>
    /// The slices of each module a method was added for, as Lean <c>MethodMetadata</c> values with their lookup tables.
    /// </summary>
    internal IEnumerable<(string Name, string Lean, string Tables)> Modules() =>
        collections.OrderBy(entry => pinned.Index(pinned.Working(entry.Key))).Select(entry =>
        {
            var lean = entry.Value.Lean();
            return (Name(entry.Key), lean, entry.Value.Tables());
        });

    internal static string Bytes(IEnumerable<byte> bytes) =>
        "[" + string.Join(", ", bytes.Select(value => value.ToString(CultureInfo.InvariantCulture))) + "]";

    internal static string Entries<TKey>(SortedDictionary<TKey, byte[]> entries) where TKey : notnull =>
        "[" + string.Join(", ", entries.Select(entry =>
            $"({Convert.ToString(entry.Key, CultureInfo.InvariantCulture)}, {Bytes(entry.Value)})")) + "]";

    /// <summary>The slices of the pinned modules one method reaches, its own first.</summary>
    sealed class Collection(PinnedAssemblies pinned)
    {
        readonly List<Slice> slices = [];

        internal PinnedAssemblies Pinned => pinned;

        internal Slice SliceOf(ModuleDefinition module)
        {
            var original = pinned.Original(module);
            var existing = slices.Find(slice => slice.Module == original);
            if (existing is not null) return existing;
            var created = new Slice(this, original, slices.Count);
            slices.Add(created);
            return created;
        }

        internal Slice At(int position) => slices[position];

        internal string Lean()
        {
            // Closing a slice can reach another module, so the list is read by index while it grows.
            for (var position = 0; position < slices.Count; position++) slices[position].Finish();
            return $"{{ own := {slices[0].Lean()}, others := [{string.Join(", ", slices.Skip(1).Select(slice => slice.Lean()))}] }}";
        }

        /// <summary>The lookup tables of each slice, in slice order; read after <see cref="Lean"/> has closed them.</summary>
        internal string Tables() => "[" + string.Join(", ", slices.Select(slice => slice.Tables())) + "]";
    }

    /// <summary>The rows, heap entries and links of one module the method reaches.</summary>
    sealed class Slice(Collection collection, ModuleDefinition module, int position)
    {
        readonly MetadataImage image = collection.Pinned.Metadata(module);
        readonly SortedDictionary<uint, byte[]> rows = [];
        readonly SortedDictionary<int, byte[]> strings = [];
        readonly SortedDictionary<int, byte[]> blobs = [];
        readonly SortedDictionary<int, byte[]> userStrings = [];
        readonly List<(int Kind, uint Source, int Slice, uint Target)> links = [];
        readonly Dictionary<(int Kind, uint Source), (int Slice, uint Target)> linked = [];
        readonly HashSet<uint> visited = [];
        readonly HashSet<uint> modifierVisited = [];
        readonly HashSet<uint> fieldsAdded = [];
        readonly HashSet<uint> chained = [];
        int corlib;

        internal ModuleDefinition Module => module;

        MetadataReader Reader => image.Reader;

        static uint TokenOf(EntityHandle handle) => (uint)MetadataTokens.GetToken(handle);

        static int RowOf(uint token) => (int)(token & 0xFFFFFF);

        void Row(uint token)
        {
            if (!rows.ContainsKey(token)) rows[token] = image.Row(token);
        }

        void Text(StringHandle handle)
        {
            var offset = Reader.GetHeapOffset(handle);
            if (!strings.ContainsKey(offset)) strings[offset] = image.StringEntry(offset);
        }

        void Blob(BlobHandle handle)
        {
            var offset = Reader.GetHeapOffset(handle);
            if (!blobs.ContainsKey(offset)) blobs[offset] = image.SizedEntry(HeapIndex.Blob, offset);
        }

        void UserString(int offset)
        {
            if (!userStrings.ContainsKey(offset)) userStrings[offset] = image.SizedEntry(HeapIndex.UserString, offset);
        }

        void Link(int kind, uint source, int slice, uint target)
        {
            if (!linked.TryAdd((kind, source), (slice, target))) return;
            links.Add((kind, source, slice, target));
        }

        /// <summary>
        /// The tokens a signature blob names, in the signature's order. A form the Lean checker has no place for
        /// stops the extraction with its name: a general array, a typed reference, a pinned local, a function
        /// pointer in a member reference and a custom modifier other than the two Roslyn writes on `in` parameters
        /// and `init` accessors.
        /// </summary>
        sealed class TokenCollector(MetadataReader reader, bool member) : ISignatureTypeProvider<int, object?>
        {
            internal readonly List<uint> Tokens = [];
            readonly Dictionary<uint, int> uses = [];
            readonly Dictionary<uint, int> modifierUses = [];

            /// <summary>
            /// Whether the signature names the type only as a custom modifier, which the checker reads by scope
            /// and name alone, so the type needs no link to a definition.
            /// </summary>
            internal bool OnlyModifier(uint token) =>
                modifierUses.TryGetValue(token, out var asModifier) && asModifier == uses[token];

            int Named(EntityHandle handle)
            {
                var token = TokenOf(handle);
                Tokens.Add(token);
                uses[token] = uses.GetValueOrDefault(token) + 1;
                return (int)token;
            }

            static InvalidDataException Unsupported(string form) =>
                new($"Unsupported metadata signature: {form}. The metadata binding check reads neither this form nor its identity.");

            public int GetPrimitiveType(PrimitiveTypeCode typeCode) =>
                typeCode == PrimitiveTypeCode.TypedReference ? throw Unsupported("typed reference") : 0;
            public int GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle,
                byte rawTypeKind) => Named(handle);
            public int GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle,
                byte rawTypeKind) => Named(handle);
            public int GetTypeFromSpecification(MetadataReader reader, object? context,
                TypeSpecificationHandle handle, byte rawTypeKind) => Named(handle);
            public int GetSZArrayType(int elementType) => 0;
            public int GetArrayType(int elementType, ArrayShape shape) => throw Unsupported("general array");
            public int GetByReferenceType(int elementType) => 0;
            public int GetPointerType(int elementType) => 0;
            public int GetGenericInstantiation(int genericType, ImmutableArray<int> typeArguments) => 0;
            public int GetGenericMethodParameter(object? context, int index) => 0;
            public int GetGenericTypeParameter(object? context, int index) => 0;
            public int GetFunctionPointerType(MethodSignature<int> signature) =>
                member ? throw Unsupported("function pointer in a member reference") : 0;

            public int GetModifiedType(int modifier, int unmodifiedType, bool isRequired)
            {
                var handle = MetadataTokens.EntityHandle(modifier);
                modifierUses[(uint)modifier] = modifierUses.GetValueOrDefault((uint)modifier) + 1;
                var name = handle.Kind switch
                {
                    HandleKind.TypeReference =>
                        reader.GetString(reader.GetTypeReference((TypeReferenceHandle)handle).Name),
                    HandleKind.TypeDefinition =>
                        reader.GetString(reader.GetTypeDefinition((TypeDefinitionHandle)handle).Name),
                    _ => ""
                };
                return isRequired && name is "InAttribute" or "IsExternalInit" ? 0
                    : throw Unsupported("custom modifier " + (name.Length == 0 ? "of a specification" : name));
            }

            public int GetPinnedType(int elementType) => throw Unsupported("pinned local");
        }

        enum Form { Method, Field, Locals, Type, Instantiation, Standalone }

        /// <summary>A signature blob and every token its types name.</summary>
        void Signature(BlobHandle handle, Form form, bool member = false)
        {
            Blob(handle);
            var collector = new TokenCollector(Reader, form is Form.Method or Form.Field && member);
            var decoder = new SignatureDecoder<int, object?>(collector, Reader, null);
            var blob = Reader.GetBlobReader(handle);
            if (form == Form.Standalone)
            {
                var first = Reader.GetBlobBytes(handle);
                form = first.Length > 0 && first[0] == 0x07 ? Form.Locals : Form.Method;
            }
            switch (form)
            {
                case Form.Method: decoder.DecodeMethodSignature(ref blob); break;
                case Form.Field: decoder.DecodeFieldSignature(ref blob); break;
                case Form.Locals: decoder.DecodeLocalSignature(ref blob); break;
                case Form.Type: decoder.DecodeType(ref blob); break;
                default: decoder.DecodeMethodSpecificationSignature(ref blob); break;
            }
            foreach (var token in collector.Tokens) Token(token, collector.OnlyModifier(token));
        }

        /// <summary>Add a token with every row and heap entry the checker reads for it.</summary>
        internal void Token(uint token, bool onlyModifier = false)
        {
            if (onlyModifier && token >> 24 == 0x01)
            {
                // Read by scope and name alone: its rows, and no link, whether or not the type resolves.
                if (!visited.Contains(token) && modifierVisited.Add(token)) TypeRef(token, linked: false);
                return;
            }
            if (!visited.Add(token)) return;
            switch (token >> 24)
            {
                case 0x01: TypeRef(token, linked: true); break;
                case 0x02: TypeDef(token); break;
                case 0x04: Field(token); break;
                case 0x06: MethodDef(token); break;
                case 0x0A: MemberRef(token); break;
                case 0x11: Standalone(token); break;
                case 0x1B: TypeSpec(token); break;
                case 0x23: AssemblyRef(token); break;
                case 0x2B: MethodSpec(token); break;
                case 0x70: UserString(RowOf(token)); break;
                default:
                    throw new InvalidDataException($"Unsupported metadata table of token 0x{token:X8} in {module.Name}.");
            }
        }

        void AssemblyRef(uint token)
        {
            Row(token);
            var reference = Reader.GetAssemblyReference(MetadataTokens.AssemblyReferenceHandle(RowOf(token)));
            if (reference.Flags != 0)
                throw new InvalidDataException("Unsupported assembly reference flags 0x" +
                    ((int)reference.Flags).ToString("X", CultureInfo.InvariantCulture) + " on " +
                    Reader.GetString(reference.Name) + ": a full public key or a retargetable reference has no kernel-checked identity.");
            Text(reference.Name);
            Text(reference.Culture);
            Blob(reference.PublicKeyOrToken);
        }

        void TypeRef(uint token, bool linked)
        {
            Row(token);
            var reference = Reader.GetTypeReference(MetadataTokens.TypeReferenceHandle(RowOf(token)));
            Text(reference.Name);
            Text(reference.Namespace);
            var scope = reference.ResolutionScope;
            if (scope.Kind == HandleKind.ModuleReference)
                throw new InvalidDataException("Unsupported type scope: " + Reader.GetString(reference.Name) +
                    " is resolved through a module reference.");
            if (!scope.IsNil && scope.Kind != HandleKind.ModuleDefinition) Token(TokenOf(scope));
            var typeReference = (TypeReference)module.LookupToken(new MetadataToken(token));
            if (!linked || !IsPinned(typeReference)) return;
            var definition = typeReference.Resolve();
            if (definition is null)
                throw new InvalidDataException("Unresolved pinned type: " + typeReference.FullName);
            if (typeReference.Scope is AssemblyNameReference named && named.FullName != definition.Module.Assembly.Name.FullName)
                throw new InvalidDataException("Unsupported forwarded type: " + typeReference.FullName +
                    " is defined in " + definition.Module.Assembly.Name.FullName + ", not in the assembly that names it.");
            var target = collection.SliceOf(definition.Module);
            Link(0, token, target.PositionOf, definition.MetadataToken.ToUInt32());
            target.Token(definition.MetadataToken.ToUInt32());
        }

        /// <summary>Whether a type is declared by a pinned module: a module-scoped type of the untouched copy counts.</summary>
        bool IsPinned(TypeReference type) => type.Scope is ModuleDefinition scope
            ? collection.Pinned.Contains(collection.Pinned.Working(scope)) : collection.Pinned.ModuleOf(type) is not null;

        bool Extends(SrmTypeDefinition definition, string name)
        {
            if (definition.BaseType.Kind != HandleKind.TypeReference) return false;
            var parent = Reader.GetTypeReference((TypeReferenceHandle)definition.BaseType);
            return Reader.GetString(parent.Namespace) == "System" && Reader.GetString(parent.Name) == name;
        }

        bool IsClass(SrmTypeDefinition definition) =>
            (definition.Attributes & System.Reflection.TypeAttributes.Interface) == 0 &&
            !definition.BaseType.IsNil && !Extends(definition, "ValueType") && !Extends(definition, "Enum");

        void TypeDef(uint token)
        {
            Row(token);
            var definition = Reader.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(RowOf(token)));
            Text(definition.Name);
            Text(definition.Namespace);
            if (RowOf(token) < image.Count(0x02)) Row(token + 1);
            if (!definition.BaseType.IsNil) Token(TokenOf(definition.BaseType));
            if (Extends(definition, "Enum")) FieldRows(definition, signatures: true);
            var enclosing = definition.GetDeclaringType();
            if (enclosing.IsNil) return;
            var nesting = NestedClassRow(token);
            Row(nesting);
            Link(2, token, position, nesting);
            Token(TokenOf(enclosing));
        }

        /// <summary>The <c>NestedClass</c> row that names a nested type.</summary>
        uint NestedClassRow(uint token) => image.NestedClassRow(RowOf(token)) ??
            throw new InvalidDataException($"No NestedClass row for type 0x{token:X8} in {module.Name}.");

        /// <summary>Every field row of a type, and for an enum the signature of its instance field.</summary>
        void FieldRows(SrmTypeDefinition definition, bool signatures)
        {
            foreach (var handle in definition.GetFields())
            {
                Row(TokenOf(handle));
                if (signatures) Blob(Reader.GetFieldDefinition(handle).Signature);
            }
        }

        void Declared(uint member, TypeDefinitionHandle declaring)
        {
            Link(1, member, position, TokenOf(declaring));
            Token(TokenOf(declaring));
        }

        /// <summary>The base classes of a class definition, with their field rows, through any slice they live in.</summary>
        void Chain(SrmTypeDefinition definition)
        {
            if (!IsClass(definition) || definition.BaseType.IsNil) return;
            var parent = TokenOf(definition.BaseType);
            Token(parent);
            if ((parent >> 24) == 0x02)
            {
                var baseDefinition = Reader.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(RowOf(parent)));
                FieldRows(baseDefinition, signatures: false);
                Chain(baseDefinition);
            }
            else if ((parent >> 24) == 0x01 && linked.TryGetValue((0, parent), out var target))
                collection.At(target.Slice).ClassChain(target.Target);
        }

        void ClassChain(uint token)
        {
            if (!chained.Add(token)) return;
            var definition = Reader.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(RowOf(token)));
            FieldRows(definition, signatures: false);
            Chain(definition);
        }

        void Field(uint token)
        {
            Row(token);
            var handle = MetadataTokens.FieldDefinitionHandle(RowOf(token));
            var field = Reader.GetFieldDefinition(handle);
            Text(field.Name);
            Signature(field.Signature, Form.Field);
            var declaring = field.GetDeclaringType();
            Declared(token, declaring);
            var owner = Reader.GetTypeDefinition(declaring);
            if (fieldsAdded.Add(TokenOf(declaring)))
            {
                FieldRows(owner, signatures: false);
                if (IsClass(owner)) Chain(owner);
            }
        }

        void MethodDef(uint token)
        {
            Row(token);
            var method = Reader.GetMethodDefinition(MetadataTokens.MethodDefinitionHandle(RowOf(token)));
            Text(method.Name);
            Signature(method.Signature, Form.Method);
            Declared(token, method.GetDeclaringType());
        }

        void MemberRef(uint token)
        {
            Row(token);
            var member = Reader.GetMemberReference(MetadataTokens.MemberReferenceHandle(RowOf(token)));
            Text(member.Name);
            Signature(member.Signature, member.GetKind() == MemberReferenceKind.Field ? Form.Field : Form.Method, true);
            Token(TokenOf(member.Parent));
            var reference = (MemberReference)module.LookupToken(new MetadataToken(token));
            var declaring = reference.DeclaringType is GenericInstanceType generic ? generic.ElementType : reference.DeclaringType;
            if (!IsPinned(declaring)) return;
            (ModuleDefinition definingModule, uint definitionToken) = reference switch
            {
                MethodReference method when method.Resolve() is { } resolved =>
                    (resolved.Module, resolved.MetadataToken.ToUInt32()),
                FieldReference field when field.Resolve() is { } resolved =>
                    (resolved.Module, resolved.MetadataToken.ToUInt32()),
                _ => throw new InvalidDataException("Unresolved pinned member: " + reference.FullName)
            };
            var target = collection.SliceOf(definingModule);
            Link(0, token, target.PositionOf, definitionToken);
            target.Token(definitionToken);
        }

        void MethodSpec(uint token)
        {
            Row(token);
            var specification = Reader.GetMethodSpecification(MetadataTokens.MethodSpecificationHandle(RowOf(token)));
            Signature(specification.Signature, Form.Instantiation);
            Token(TokenOf(specification.Method));
        }

        void Standalone(uint token)
        {
            Row(token);
            Signature(Reader.GetStandaloneSignature(MetadataTokens.StandaloneSignatureHandle(RowOf(token))).Signature,
                Form.Standalone);
        }

        void TypeSpec(uint token)
        {
            Row(token);
            Signature(Reader.GetTypeSpecification(MetadataTokens.TypeSpecificationHandle(RowOf(token))).Signature,
                Form.Type);
        }

        /// <summary>
        /// A method definition with what its identity check reads: its owner's and its own generic parameter rows,
        /// and for a class receiver the fields of its owner and bases.
        /// </summary>
        internal void Method(MethodDefinition original, bool classOwner)
        {
            var token = original.MetadataToken.ToUInt32();
            Token(token);
            var method = Reader.GetMethodDefinition(MetadataTokens.MethodDefinitionHandle(RowOf(token)));
            GenericRun(token, method.GetGenericParameters());
            var owner = Reader.GetTypeDefinition(method.GetDeclaringType());
            GenericRun(TokenOf(method.GetDeclaringType()), owner.GetGenericParameters());
            if (!classOwner) return;
            if (fieldsAdded.Add(TokenOf(method.GetDeclaringType())))
            {
                FieldRows(owner, signatures: false);
                Chain(owner);
            }
        }

        /// <summary>The generic parameter rows of an owner, the rows around them and the link to the first.</summary>
        void GenericRun(uint owner, GenericParameterHandleCollection parameters)
        {
            if (parameters.Count == 0) return;
            var numbers = parameters.Select(handle => MetadataTokens.GetRowNumber(handle)).Order().ToArray();
            Link(3, owner, position, 0x2A000000 + (uint)numbers[0]);
            foreach (var number in numbers) Row(0x2A000000 + (uint)number);
            if (numbers[0] > 1) Row(0x2A000000 + (uint)numbers[0] - 1);
            if (numbers[^1] < image.Count(0x2A)) Row(0x2A000000 + (uint)numbers[^1] + 1);
        }

        /// <summary>The primitive types' assembly reference, which Lean names the scope of integer types by.</summary>
        internal void Finish()
        {
            var core = module.TypeSystem.CoreLibrary as AssemblyNameReference;
            var index = core is null ? -1 : module.AssemblyReferences.ToList().FindIndex(reference =>
                reference.FullName == core.FullName);
            if (index < 0) return;
            corlib = index + 1;
            Token(0x23000000 + (uint)corlib);
        }

        internal string Lean()
        {
            var assembly = $"assembly{collection.Pinned.Index(collection.Pinned.Working(module))}Metadata";
            var linkList = string.Join(", ", SortedLinks().Select(link => $"⟨{link.Kind}, {link.Source}, {link.Slice}, {link.Target}⟩"));
            return $"{{ assembly := {assembly}, rows := {Entries(rows)}, strings := {Entries(strings)}, " +
                $"blobs := {Entries(blobs)}, userStrings := {Entries(userStrings)}, corlib := {corlib}, " +
                $"links := [{linkList}] }}";
        }

        IEnumerable<(int Kind, uint Source, int Slice, uint Target)> SortedLinks() =>
            links.OrderBy(link => ((ulong)link.Kind << 32) + link.Source);

        /// <summary>
        /// A balanced search tree over entries in ascending key order, as Lean's <c>SearchTree.ofSorted</c> builds
        /// it: the first <c>count / 2</c> entries go left of the root.
        /// </summary>
        static string Tree(IReadOnlyList<(ulong Key, string Value)> entries)
        {
            string Build(int start, int count)
            {
                if (count == 0) return ".leaf";
                var left = count / 2;
                var root = entries[start + left];
                return $"(.node {Build(start, left)} {root.Key} {root.Value} {Build(start + left + 1, count - 1 - left)})";
            }
            return Build(0, entries.Count);
        }

        static (ulong, string) Entry<TKey>(KeyValuePair<TKey, byte[]> entry) where TKey : struct, IConvertible =>
            (Convert.ToUInt64(entry.Key, CultureInfo.InvariantCulture), Bytes(entry.Value));

        /// <summary>
        /// The instance field counts Lean derives from the carried rows: for each field of a carried type whose
        /// fields and following type are carried, the instance fields before it, and for the type their total.
        /// </summary>
        (string Before, string Total) FieldCounts()
        {
            var before = new List<(ulong, string)>();
            var total = new List<(ulong, string)>();
            var typeCount = (uint)Reader.GetTableRowCount(TableIndex.TypeDef);
            var fieldCount = (uint)Reader.GetTableRowCount(TableIndex.Field);
            foreach (var (token, row) in rows.Where(entry => entry.Key >> 24 == 0x02))
            {
                var first = image.FieldList(row);
                uint stop;
                if ((token & 0xFFFFFF) == typeCount) stop = fieldCount + 1;
                else if (rows.TryGetValue(token + 1, out var next)) stop = image.FieldList(next);
                else continue;
                var found = new List<(ulong, string)>();
                uint instances = 0;
                var complete = true;
                for (uint index = 0; index < (stop > first ? stop - first : 0) && complete; index++)
                {
                    var field = 0x04000000u + first + index;
                    complete = rows.TryGetValue(field, out var bytes);
                    if (!complete) break;
                    found.Add((field, instances.ToString(CultureInfo.InvariantCulture)));
                    if (bytes![0] / 0x10 % 2 == 0) instances++;
                }
                if (!complete) continue;
                before.AddRange(found);
                total.Add((token, instances.ToString(CultureInfo.InvariantCulture)));
            }
            return (Tree(before), Tree(total));
        }

        /// <summary>The Lean <c>IndexTables</c> of this slice, equal to what the decoder builds from its bytes.</summary>
        internal string Tables()
        {
            var (before, total) = FieldCounts();
            var linkEntries = SortedLinks().Select(link =>
                (((ulong)link.Kind << 32) + link.Source, $"({link.Slice}, {link.Target})")).ToList();
            return $"{{ rows := {Tree([.. rows.Select(Entry)])}, strings := {Tree([.. strings.Select(Entry)])}, " +
                $"blobs := {Tree([.. blobs.Select(Entry)])}, userStrings := {Tree([.. userStrings.Select(Entry)])}, " +
                $"links := {Tree(linkEntries)}, instanceBefore := {before}, instanceTotal := {total} }}";
        }

        internal int PositionOf => position;
    }
}
