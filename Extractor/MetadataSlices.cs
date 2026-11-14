using System.Collections.Immutable;
using System.Globalization;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Mono.Cecil;
using MemberReference = Mono.Cecil.MemberReference;
using TypeReference = Mono.Cecil.TypeReference;
using MethodDefinition = Mono.Cecil.MethodDefinition;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;
using SrmTypeDefinition = System.Reflection.Metadata.TypeDefinition;

namespace Nethermind.LeanCIL;

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
        // Numbered by rank in bytes, as the slices' heaps are, so the block does not move with the image's offsets.
        var row = image.Row(0x20000001);
        var textWidth = reader.GetHeapSize(HeapIndex.String) > 0xFFFF ? 4 : 2;
        var blobWidth = reader.GetHeapSize(HeapIndex.Blob) > 0xFFFF ? 4 : 2;
        var ranked = new SortedDictionary<int, byte[]>[] { [], [] };
        var numbers = new Dictionary<int, int>[] { new() { [0] = 0 }, new() { [0] = 0 } };
        foreach (var (heap, source) in new[] { (0, strings), (1, blobs) })
        {
            var rank = 1;
            foreach (var entry in source.Where(entry => entry.Key != 0)
                         .OrderBy(entry => Convert.ToHexString(entry.Value), StringComparer.Ordinal))
            {
                numbers[heap][entry.Key] = rank;
                ranked[heap][rank++] = entry.Value;
            }
            if (source.TryGetValue(0, out var empty)) ranked[heap][0] = empty;
        }
        var at = 4 + 8 + 4;
        foreach (var (heap, width) in new[] { (1, blobWidth), (0, textWidth), (0, textWidth) })
        {
            var offset = width == 2 ? BitConverter.ToUInt16(row, at) : (int)BitConverter.ToUInt32(row, at);
            Array.Copy(BitConverter.GetBytes(numbers[heap][offset]), 0, row, at, width);
            at += width;
        }
        // The token is the SHA-1 of the public key, which Lean does not compute: it is stated, and checked only
        // to be sixteen hexadecimal digits when the row has a key.
        const string TokenMarker = "PublicKeyToken=";
        var token = identity[(identity.LastIndexOf(TokenMarker, StringComparison.Ordinal) + TokenMarker.Length)..];
        var hasKey = !assembly.PublicKey.IsNil && reader.GetBlobBytes(assembly.PublicKey).Length > 0;
        var keyToken = !hasKey ? ""
            : $"keyToken := {Bytes(System.Text.Encoding.ASCII.GetBytes(token))}, ";
        return $"{{ identity := {System.Text.Json.JsonSerializer.Serialize(identity)}, {keyToken}" +
            $"tableHeader := {Bytes(image.TableHeader())}, header := {image.DecodedHeader()}, " +
            $"assemblyRow := {Bytes(row)}, " +
            $"strings := {Entries(ranked[0])}, blobs := {Entries(ranked[1])} }}";
    }

    /// <summary>
    /// The slices of one method's body, as a Lean <c>MethodMetadata</c> value, and the lookup tables of those slices.
    /// They hold what this method reaches and nothing else, with heap entries numbered by rank among the entries
    /// carried, so the method's evidence is a function of the method and its assemblies alone.
    /// </summary>
    internal (string Metadata, string Tables, int[] Assemblies) Method(MethodDefinition original,
        IEnumerable<uint> tokens, bool classOwner)
    {
        var collection = new Collection(pinned);
        var own = collection.SliceOf(original.Module);
        own.Method(original, classOwner);
        foreach (var token in tokens) own.Token(token);
        var metadata = collection.Lean();
        return (metadata, collection.Tables(), collection.Assemblies());
    }

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
            foreach (var slice in slices) slice.Canonicalize();
            var others = string.Join(", ", slices.Skip(1).Select(slice => slice.Lean()));
            return $"{{ own := {slices[0].Lean()}, others := [{others}] }}";
        }

        /// <summary>The pinned assembly index of each slice, in slice order.</summary>
        internal int[] Assemblies() => [.. slices.Select(slice => slice.AssemblyIndex())];

        /// <summary>
        /// The lookup tables of each slice, in slice order; read after <see cref="Lean"/> has closed them.
        /// </summary>
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
        readonly Dictionary<uint, MetadataFieldPrefix> fieldPrefixes = [];
        readonly HashSet<uint> fieldSignaturesAdded = [];
        readonly HashSet<uint> chainedOwners = [];
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
                new($"Unsupported metadata signature: {form}. " +
                    "The metadata binding check reads neither this form nor its identity.");

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
                    throw new InvalidDataException(
                        $"Unsupported metadata table of token 0x{token:X8} in {module.Name}.");
            }
        }

        void AssemblyRef(uint token)
        {
            Row(token);
            var reference = Reader.GetAssemblyReference(MetadataTokens.AssemblyReferenceHandle(RowOf(token)));
            if (reference.Flags != 0)
                throw new InvalidDataException("Unsupported assembly reference flags 0x" +
                    ((int)reference.Flags).ToString("X", CultureInfo.InvariantCulture) + " on " +
                    Reader.GetString(reference.Name) +
                    ": a full public key or a retargetable reference has no kernel-checked identity.");
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
            var definedIn = definition.Module.Assembly.Name.FullName;
            if (typeReference.Scope is AssemblyNameReference named && named.FullName != definedIn)
                throw new InvalidDataException("Unsupported forwarded type: " + typeReference.FullName +
                    " is defined in " + definedIn + ", not in the assembly that names it.");
            var target = collection.SliceOf(definition.Module);
            Link(0, token, target.PositionOf, definition.MetadataToken.ToUInt32());
            target.Token(definition.MetadataToken.ToUInt32());
        }

        /// <summary>
        /// Whether a type is declared by a pinned module: a module-scoped type of the untouched copy counts.
        /// </summary>
        bool IsPinned(TypeReference type) => type.Scope is ModuleDefinition scope
            ? collection.Pinned.Contains(collection.Pinned.Working(scope))
            : collection.Pinned.ModuleOf(type) is not null;

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
            if (Extends(definition, "Enum")) FieldRows(token, definition, signatures: true);
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

        /// <summary>The shared field enumeration of one declaring type.</summary>
        MetadataFieldPrefix Fields(uint owner, SrmTypeDefinition definition)
        {
            if (!fieldPrefixes.TryGetValue(owner, out var prefix))
                fieldPrefixes.Add(owner, prefix = new(definition.GetFields().Select(handle => TokenOf(handle))));
            return prefix;
        }

        /// <summary>Every field row of a type, and for an enum the signature of its instance field.</summary>
        void FieldRows(uint owner, SrmTypeDefinition definition, bool signatures)
        {
            var prefix = Fields(owner, definition);
            prefix.All(Row);
            if (!signatures || !fieldSignaturesAdded.Add(owner)) return;
            foreach (var token in prefix.Carried)
                Blob(Reader.GetFieldDefinition(MetadataTokens.FieldDefinitionHandle(RowOf(token))).Signature);
        }

        void Declared(uint member, TypeDefinitionHandle declaring)
        {
            Link(1, member, position, TokenOf(declaring));
            Token(TokenOf(declaring));
        }

        /// <summary>
        /// The base classes of a class definition, with their field rows, through any slice they live in.
        /// </summary>
        void Chain(SrmTypeDefinition definition)
        {
            if (!IsClass(definition) || definition.BaseType.IsNil) return;
            var parent = TokenOf(definition.BaseType);
            Token(parent);
            if ((parent >> 24) == 0x02)
                ClassChain(parent);
            else if ((parent >> 24) == 0x01 && linked.TryGetValue((0, parent), out var target))
                collection.At(target.Slice).ClassChain(target.Target);
        }

        void ClassChain(uint token)
        {
            if (!chained.Add(token)) return;
            var definition = Reader.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(RowOf(token)));
            FieldRows(token, definition, signatures: false);
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
            // The owner's fields up to this one: Lean counts the instance fields before it over the carried rows
            // from the owner's first field. Base classes, whose totals the index needs, stay whole.
            Fields(TokenOf(declaring), owner).Through(token, Row);
            if (IsClass(owner) && chainedOwners.Add(TokenOf(declaring))) Chain(owner);
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
            Signature(member.Signature,
                member.GetKind() == MemberReferenceKind.Field ? Form.Field : Form.Method, true);
            Token(TokenOf(member.Parent));
            var reference = (MemberReference)module.LookupToken(new MetadataToken(token));
            var declaring = reference.DeclaringType is GenericInstanceType generic
                ? generic.ElementType : reference.DeclaringType;
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
                FieldRows(TokenOf(method.GetDeclaringType()), owner, signatures: false);
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

        enum Heap { None, Text, Blob }

        /// <summary>
        /// The columns of a carried row, each with its width and the heap it indexes. The widths follow the
        /// table stream header, as Lean's decoder reads them.
        /// </summary>
        (int Width, Heap Heap)[] Columns(TableIndex table)
        {
            int Rows(TableIndex index) => Reader.GetTableRowCount(index);
            int Simple(TableIndex index) => Rows(index) > 0xFFFF ? 4 : 2;
            int Coded(int bits, params TableIndex[] tables) => tables.Max(Rows) < 1 << (16 - bits) ? 2 : 4;
            var text = Reader.GetHeapSize(HeapIndex.String) > 0xFFFF ? 4 : 2;
            var blob = Reader.GetHeapSize(HeapIndex.Blob) > 0xFFFF ? 4 : 2;
            var scope = Coded(2, TableIndex.Module, TableIndex.ModuleRef, TableIndex.AssemblyRef, TableIndex.TypeRef);
            var typeDefOrRef = Coded(2, TableIndex.TypeDef, TableIndex.TypeRef, TableIndex.TypeSpec);
            return table switch
            {
                TableIndex.TypeRef => [(scope, Heap.None), (text, Heap.Text), (text, Heap.Text)],
                TableIndex.TypeDef => [(4, Heap.None), (text, Heap.Text), (text, Heap.Text),
                    (typeDefOrRef, Heap.None), (Simple(TableIndex.Field), Heap.None),
                    (Simple(TableIndex.MethodDef), Heap.None)],
                TableIndex.Field => [(2, Heap.None), (text, Heap.Text), (blob, Heap.Blob)],
                TableIndex.MethodDef => [(4, Heap.None), (2, Heap.None), (2, Heap.None), (text, Heap.Text),
                    (blob, Heap.Blob), (Simple(TableIndex.Param), Heap.None)],
                TableIndex.MemberRef => [(Coded(3, TableIndex.TypeDef, TableIndex.TypeRef, TableIndex.ModuleRef,
                    TableIndex.MethodDef, TableIndex.TypeSpec), Heap.None), (text, Heap.Text), (blob, Heap.Blob)],
                TableIndex.StandAloneSig or TableIndex.TypeSpec => [(blob, Heap.Blob)],
                TableIndex.GenericParam => [(2, Heap.None), (2, Heap.None),
                    (Coded(1, TableIndex.TypeDef, TableIndex.MethodDef), Heap.None), (text, Heap.Text)],
                TableIndex.MethodSpec => [(Coded(1, TableIndex.MethodDef, TableIndex.MemberRef), Heap.None),
                    (blob, Heap.Blob)],
                TableIndex.AssemblyRef => [(8, Heap.None), (4, Heap.None), (blob, Heap.Blob), (text, Heap.Text),
                    (text, Heap.Text), (blob, Heap.Blob)],
                TableIndex.NestedClass => [(Simple(TableIndex.TypeDef), Heap.None),
                    (Simple(TableIndex.TypeDef), Heap.None)],
                _ => throw new InvalidDataException($"No column layout for table {table}.")
            };
        }

        /// <summary>
        /// Renumber the <c>#Strings</c> and <c>#Blob</c> offsets in the rows and the heap keys: the number of a
        /// carried entry is its rank among the carried entries of its heap by bytes, from 1, and 0 stays 0. Lean
        /// reads a heap entry only through the offset a row names, so any consistent numbering decodes the same
        /// rows. The image's own offsets move whenever an earlier name changes length, and its entry order is a
        /// hash or suffix sort that one changed name can reshuffle, so either would change the evidence of every
        /// method that merely shares the module; the rank depends only on what the extraction carries.
        /// </summary>
        internal void Canonicalize()
        {
            // By content, not by image order: the image orders its heaps by a hash or a suffix sort, so one
            // changed name can move the position of every other entry.
            Dictionary<int, int> Numbering(SortedDictionary<int, byte[]> heap)
            {
                var next = 1;
                var numbers = new Dictionary<int, int> { [0] = 0 };
                foreach (var entry in heap.Where(entry => entry.Key != 0)
                             .OrderBy(entry => Convert.ToHexString(entry.Value), StringComparer.Ordinal))
                    numbers[entry.Key] = next++;
                return numbers;
            }
            var textNumbers = Numbering(strings);
            var blobNumbers = Numbering(blobs);
            foreach (var token in rows.Keys.ToArray())
            {
                var row = rows[token];
                var at = 0;
                foreach (var (width, heap) in Columns((TableIndex)(token >> 24)))
                {
                    if (heap != Heap.None)
                    {
                        var offset = width == 2 ? BitConverter.ToUInt16(row, at) : (int)BitConverter.ToUInt32(row, at);
                        var numbers = heap == Heap.Text ? textNumbers : blobNumbers;
                        // A row carried only for its position, such as the next type's, may name entries that are
                        // not carried; they become 0, which Lean reads as a missing entry if it ever looks.
                        numbers.TryGetValue(offset, out var number);
                        var bytes = BitConverter.GetBytes(number);
                        Array.Copy(bytes, 0, row, at, width);
                    }
                    at += width;
                }
                if (at != row.Length)
                    throw new InvalidDataException($"The columns of row 0x{token:X8} do not add up to its length.");
            }
            Renumber(strings, textNumbers);
            Renumber(blobs, blobNumbers);
            RequireRanked(strings, "#Strings");
            RequireRanked(blobs, "#Blob");
        }

        /// <summary>
        /// The emitted numbering is the rank by bytes; a change back to the image's order stops here.
        /// </summary>
        static void RequireRanked(SortedDictionary<int, byte[]> heap, string name)
        {
            var rank = 1;
            string? previous = null;
            foreach (var (key, value) in heap.Where(entry => entry.Key != 0))
            {
                var hex = Convert.ToHexString(value);
                if (key != rank++ || previous is not null && string.CompareOrdinal(previous, hex) > 0)
                    throw new InvalidDataException(
                        $"The carried {name} entries are not numbered by their rank in bytes.");
                previous = hex;
            }
        }

        static void Renumber(SortedDictionary<int, byte[]> heap, Dictionary<int, int> numbers)
        {
            var entries = heap.ToArray();
            heap.Clear();
            foreach (var (key, value) in entries) heap[numbers[key]] = value;
        }

        internal int AssemblyIndex() => collection.Pinned.Index(collection.Pinned.Working(module));

        internal string Lean()
        {
            var assembly = $"assembly{AssemblyIndex()}Metadata";
            var linkList = string.Join(", ", SortedLinks().Select(link =>
                $"⟨{link.Kind}, {link.Source}, {link.Slice}, {link.Target}⟩"));
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
                var right = Build(start + left + 1, count - 1 - left);
                return $"(.node {Build(start, left)} {root.Key} {root.Value} {right})";
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
                before.AddRange(found);
                if (complete) total.Add((token, instances.ToString(CultureInfo.InvariantCulture)));
            }
            return (Tree(before), Tree(total));
        }

        /// <summary>Each owner's first carried parameter and count, ordered by owner token.</summary>
        string GenericOwners()
        {
            var ownerWidth = Columns(TableIndex.GenericParam)[2].Width;
            var genericOwners = new SortedDictionary<uint, (uint First, int Count)>();
            foreach (var (token, bytes) in rows.Where(entry => entry.Key >> 24 == 0x2A))
            {
                uint codedOwner = 0;
                for (var offset = 0; offset < ownerWidth; offset++)
                    codedOwner |= (uint)bytes[4 + offset] << (8 * offset);
                var owner = (codedOwner % 2 == 0 ? 0x02000000u : 0x06000000u) + codedOwner / 2;
                genericOwners[owner] = genericOwners.TryGetValue(owner, out var previous)
                    ? (previous.First, previous.Count + 1) : (token, 1);
            }
            var ownerEntries = genericOwners.Select(entry =>
                ((ulong)entry.Key, $"({entry.Value.First}, {entry.Value.Count})")).ToList();
            return Tree(ownerEntries);
        }

        /// <summary>
        /// The Lean <c>IndexTables</c> of this slice, equal to what the decoder builds from its bytes.
        /// </summary>
        internal string Tables()
        {
            var (before, total) = FieldCounts();
            var linkEntries = SortedLinks().Select(link =>
                (((ulong)link.Kind << 32) + link.Source, $"({link.Slice}, {link.Target})")).ToList();
            return $"{{ rows := {Tree([.. rows.Select(Entry)])}, strings := {Tree([.. strings.Select(Entry)])}, " +
                $"blobs := {Tree([.. blobs.Select(Entry)])}, userStrings := {Tree([.. userStrings.Select(Entry)])}, " +
                $"links := {Tree(linkEntries)}, instanceBefore := {before}, instanceTotal := {total}, " +
                $"genericOwners := {GenericOwners()} }}";
        }

        internal int PositionOf => position;
    }
}
