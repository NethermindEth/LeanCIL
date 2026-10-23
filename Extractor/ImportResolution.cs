using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal sealed class ImportResolution : IDisposable
{
    // A discovered sidecar is read only when a call site needs its library, so unused sidecars need no pins.
    internal sealed record Source(string SidecarPath, string ImplementationPath, string ExpectedSha256, string ExpectedInterfaceDigest, bool Discovered = false);
    internal sealed record Binding(int Slot, string Identity, string ImplementationPath, string ImplementationSha256,
        string Kind, string SidecarPath, string SidecarSha256, string InterfaceDigest, string ContractConstant,
        string ClosureDigest, string Signature, int ParameterCount, bool ReturnsValue, string Profile, string ExpectedInterfaceDigest, string ContractKind,
        string CertificationTheorem, string CertificationStatement, string CertificationStatementDigest, bool IsReferenceAssembly,
        StaticIdentityRecord[] StaticIdentities,
        string? DefinitionSignature, string[] TypeArguments, ContractMethodSignature? TypedSignature,
        ContractLayout[] PublishedLayouts, ContractLayout[] ActualLayouts, string ComputedLayouts);
    sealed record Library(Source Source, ContractInterface Interface, string SidecarSha256, ModuleDefinition Module);
    internal sealed record Node(string AssemblyIdentity, string ImplementationSha256, string InterfaceDigest,
        string SidecarPath, string ImplementationPath, string ExpectedInterfaceDigest, bool IsReferenceAssembly,
        ContractDependency[] Dependencies);
    readonly List<Library> libraries = [];
    readonly Dictionary<(string Identity, string Profile), int> implementationState = [];
    readonly HashSet<string>? allowedDependencies;
    readonly string? validatingAssembly;
    readonly bool ownsLibraries = true;
    readonly HashSet<Library> used = [];
    readonly Dictionary<string, Source> discovered = new(StringComparer.Ordinal);
    readonly List<Binding> bindings = [];
    readonly Dictionary<Instruction, int> sites = [];
    internal IReadOnlyList<Binding> Bindings => bindings;
    internal Node[] Nodes => libraries.OrderBy(library => library.Interface.AssemblyIdentity, StringComparer.Ordinal)
        .Select(library => new Node(library.Interface.AssemblyIdentity, library.Interface.ImplementationSha256,
            library.Interface.InterfaceDigest, Path.GetFullPath(library.Source.SidecarPath),
            Path.GetFullPath(library.Source.ImplementationPath), library.Source.ExpectedInterfaceDigest,
            library.Interface.IsReferenceAssembly, library.Interface.Dependencies)).ToArray();

    internal ImportResolution(IEnumerable<Source> sources)
    {
        try
        {
            foreach (Source source in sources)
            {
                if (source.Discovered) discovered[Path.GetFileName(source.SidecarPath)[..^".leancil.contracts".Length]] = source;
                else Load(source);
            }
            ValidateGraph();
        }
        catch { Dispose(); throw; }
    }

    void Load(Source source)
    {
                byte[] sidecar = File.ReadAllBytes(source.SidecarPath);
                ContractInterface contract = ContractInterface.Read(sidecar);
                byte[] implementation = File.ReadAllBytes(source.ImplementationPath);
                string actual = ContractInterface.Hash(implementation);
                if (!ContractInterface.Digest(source.ExpectedSha256))
                    throw new InvalidDataException("Import requires an independently supplied SHA-256: --import-sha256 Lib=<hex>.");
                if (actual != source.ExpectedSha256)
                    throw new InvalidDataException($"Import implementation SHA-256 mismatch: expected {source.ExpectedSha256}, actual {actual}.");
                if (actual != contract.ImplementationSha256)
                    throw new InvalidDataException($"Import certified SHA-256 mismatch: expected {contract.ImplementationSha256}, actual {actual}.");
                if (!ContractInterface.Digest(source.ExpectedInterfaceDigest))
                    throw new InvalidDataException("Import requires an independently supplied interface digest: --import-interface-sha256 Lib=<hex>.");
                if (source.ExpectedInterfaceDigest != contract.InterfaceDigest)
                    throw new InvalidDataException($"Import interface SHA-256 mismatch: expected {source.ExpectedInterfaceDigest}, actual {contract.InterfaceDigest}.");
                ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(implementation));
                try
                {
                    bool referenceAssembly = module.Assembly.CustomAttributes.Any(attribute =>
                        attribute.AttributeType.FullName == "System.Runtime.CompilerServices.ReferenceAssemblyAttribute");
                    if (referenceAssembly && !contract.IsReferenceAssembly)
                        throw new InvalidDataException("Import reference assembly flag mismatch; reference assemblies are authoring-only.");
                    if (module.Assembly.Name.FullName != contract.AssemblyIdentity)
                        throw new InvalidDataException("Import assembly identity mismatch.");
                    if (module.Mvid != contract.Mvid)
                        throw new InvalidDataException("Import implementation MVID mismatch.");
                    string? framework = module.Assembly.CustomAttributes.SingleOrDefault(attribute =>
                        attribute.AttributeType.FullName == "System.Runtime.Versioning.TargetFrameworkAttribute")?.ConstructorArguments.Single().Value as string;
                    if (framework != contract.TargetFramework || framework != ".NETCoreApp,Version=v10.0")
                        throw new InvalidDataException("Import target framework mismatch.");
                    Library? existing = libraries.SingleOrDefault(library => library.Interface.AssemblyIdentity == contract.AssemblyIdentity);
                    if (existing is not null)
                    {
                        if (existing.Interface.ImplementationSha256 != contract.ImplementationSha256)
                            throw new InvalidDataException("Conflicting contract dependency implementation hashes: " + contract.AssemblyIdentity);
                        if (existing.Interface.InterfaceDigest != contract.InterfaceDigest || existing.SidecarSha256 != ContractInterface.Hash(sidecar))
                            throw new InvalidDataException("Conflicting contract dependency interface or certification: " + contract.AssemblyIdentity);
                        module.Dispose();
                        return;
                    }
                    if (libraries.Any(library => library.Module.Assembly.Name.Name == module.Assembly.Name.Name))
                        throw new InvalidDataException("Ambiguous import assembly simple name: " + module.Assembly.Name.Name);
                    libraries.Add(new(source, contract, ContractInterface.Hash(sidecar), module));
                }
                catch { module.Dispose(); throw; }
    }

    void ValidateGraph()
    {
        for (int index = 0; index < libraries.Count; index++)
            foreach (ContractDependency dependency in libraries[index].Interface.Dependencies)
            {
                if (libraries.Any(library => library.Interface.AssemblyIdentity == dependency.AssemblyIdentity)) continue;
                string name = AssemblyNameReference.Parse(dependency.AssemblyIdentity).Name;
                if (discovered.Remove(name, out Source? pending)) Load(pending);
            }
        ContractDependencyGraph.Validate(libraries.Select(library => library.Interface));
        Modules(libraries);
    }

    ImportResolution(List<Library> libraries, Dictionary<(string Identity, string Profile), int> implementationState,
        ContractInterface contract)
    {
        this.libraries = libraries;
        this.implementationState = implementationState;
        allowedDependencies = contract.Dependencies.Select(dependency => dependency.AssemblyIdentity).ToHashSet(StringComparer.Ordinal);
        validatingAssembly = contract.AssemblyIdentity;
        ownsLibraries = false;
    }

    internal static bool External(MethodReference reference, ModuleDefinition module) =>
        reference.DeclaringType.Scope is AssemblyNameReference scope && scope.FullName != module.Assembly.Name.FullName;

    internal void Admit(MethodReference reference, Instruction instruction, FeatureProfile profile)
    {
        // Shapes no sidecar can import are rejected before any sidecar is read or suggested.
        if (instruction.OpCode.Code != Code.Call)
            throw new InvalidDataException("Contract imports support call only, not callvirt, newobj or ldftn.");
        string assembly = reference.DeclaringType.Scope is AssemblyNameReference scope ? scope.FullName : reference.DeclaringType.Scope.Name;
        if (allowedDependencies is not null && !allowedDependencies.Contains(assembly))
            throw new InvalidDataException("Undeclared contract dependency: " + assembly + " required by " + validatingAssembly);
        if (!libraries.Any(candidate => candidate.Interface.AssemblyIdentity == assembly) &&
            discovered.Remove(reference.DeclaringType.Scope.Name, out Source? pending))
        {
            Load(pending);
            ValidateGraph();
        }
        Library? library = libraries.SingleOrDefault(candidate => candidate.Interface.AssemblyIdentity == assembly);
        if (library is null)
            throw new InvalidDataException($"External managed dependency: {reference.FullName}\n  Next: supply --import {reference.DeclaringType.Scope.Name}.leancil.contracts and --import-sha256 {reference.DeclaringType.Scope.Name}=<hex> and --import-interface-sha256 {reference.DeclaringType.Scope.Name}=<hex>.");
        ContractMethodMetadata.Selection selection = ContractMethodMetadata.ResolveImported(reference, library.Module, profile.Architecture);
        string identity = selection.Identity;
        ContractExport export = library.Interface.Exports.SingleOrDefault(candidate => candidate.Identity == identity)
            ?? throw new InvalidDataException("Contract export not present: " + identity);
        MethodDefinition definition = selection.Definition;
        ContractLayout[] actualLayouts = [];
        if (library.Interface.FormatVersion == 2)
        {
            actualLayouts = ImportedLayoutMetadata.Signature(selection.Reference, library.Module, profile.Architecture);
            if (export.DefinitionSignature != definition.FullName ||
                !export.TypeArguments!.SequenceEqual(selection.ArgumentNames, StringComparer.Ordinal) ||
                !MetadataEqual(export.TypedSignature, selection.Signature) || !MetadataEqual(export.Layouts, actualLayouts))
                throw new InvalidDataException("Contract import typed signature or raw layout differs from selected implementation metadata.");
        }
        else if (selection.Arguments.Length != 0)
            throw new InvalidDataException("Legacy contract imports cannot admit generic instances.");
        string visibility = definition.IsPublic ? "public" : definition.IsFamily || definition.IsFamilyOrAssembly ? "protected" : "private";
        if (!definition.IsStatic || definition.IsVirtual || visibility == "private" || export.Visibility != visibility ||
            reference.HasThis || reference.ExplicitThis || (reference.CallingConvention & ~MethodCallingConvention.Generic) != MethodCallingConvention.Default || definition.IsPInvokeImpl)
            throw new InvalidDataException("Contract export must be static, non-virtual and public or protected with matching visibility.");
        if (library.Interface.FormatVersion == 1)
        {
            MetadataValidation.Type(reference.ReturnType, reference.Module, returns: true);
            foreach (ParameterDefinition parameter in reference.Parameters) MetadataValidation.Type(parameter.ParameterType, reference.Module);
        }
        if (export.Signature != selection.Closed.FullName || export.ParameterCount != selection.Closed.Parameters.Count || export.HasThis != reference.HasThis ||
            export.ReturnsValue != (selection.Closed.ReturnType.MetadataType != MetadataType.Void))
            throw new InvalidDataException("Contract import signature counts mismatch.");
        if (FeatureProfile.Select(profile.Name) != profile)
            throw new InvalidDataException("Contract import requires an exact named built-in profile.");
        if (!export.Profiles.Contains(profile.Name, StringComparer.Ordinal))
            throw new InvalidDataException("Contract import profile not listed: " + profile.Name);
        ContractCertification certification = library.Interface.Certifications.SingleOrDefault(record => record.Identity == identity && record.Profile == profile.Name)
            ?? throw new InvalidDataException("Contract import certification not present for profile: " + profile.Name);
        if (certification.ImplementationSha256 != library.Interface.ImplementationSha256 ||
            certification.InterfaceDigest != library.Interface.InterfaceDigest || certification.ClosureDigest != export.ClosureDigest)
            throw new InvalidDataException("Contract import certification binding mismatch.");
        StaticIdentity.ValidateFields(certification.StaticIdentities, library.Module);
        if (!library.Interface.IsReferenceAssembly)
            ValidateImplementation(library, export, certification, profile);
        MarkUsed(library);
        int slot = bindings.FindIndex(binding => binding.Identity == identity);
        if (slot < 0)
        {
            slot = bindings.Count;
            bindings.Add(new(slot, identity, Path.GetFullPath(library.Source.ImplementationPath), library.Interface.ImplementationSha256,
                "contract", Path.GetFullPath(library.Source.SidecarPath), library.SidecarSha256, library.Interface.InterfaceDigest,
                export.ContractConstant, export.ClosureDigest, export.Signature, export.ParameterCount, export.ReturnsValue, profile.Name, library.Source.ExpectedInterfaceDigest, export.Kind,
                certification.Theorem, certification.Statement, certification.StatementDigest, library.Interface.IsReferenceAssembly,
                certification.StaticIdentities, export.DefinitionSignature,
                export.TypeArguments ?? [], export.TypedSignature, export.Layouts ?? [], actualLayouts,
                ImportedLayoutMetadata.ComputedLean(actualLayouts, library.Module, profile.Architecture)));
        }
        sites[instruction] = slot;
    }

    void MarkUsed(Library library)
    {
        Stack<Library> pending = new();
        pending.Push(library);
        while (pending.TryPop(out Library? selected))
        {
            if (!used.Add(selected)) continue;
            foreach (ContractDependency dependency in selected.Interface.Dependencies)
                pending.Push(libraries.Single(candidate => candidate.Interface.AssemblyIdentity == dependency.AssemblyIdentity));
        }
    }

    void ValidateImplementation(Library library, ContractExport export, ContractCertification certification, FeatureProfile profile)
    {
        (string Identity, string Profile) key = (export.Identity, profile.Name);
        int state = implementationState.GetValueOrDefault(key);
        if (state == 2) return;
        if (state == 1) throw new InvalidDataException("Recursive contract implementation validation: " + export.Identity);
        implementationState[key] = 1;
        try
        {
            using ImportResolution imports = new(libraries, implementationState, library.Interface);
            MethodDefinition[] implementation = MetadataValidation.Validate(library.Module, library.Interface.AssemblyIdentity,
                export.DefinitionSignature ?? export.Signature, profile, imports: imports,
                typeArguments: export.TypeArguments, importedByref: type => imports.ValidateByref(type, profile));
            StaticIdentityRecord[] actualStatics = LeanEmitter.StaticIdentities(implementation, profile);
            StaticIdentityRecord[] certifiedStatics = certification.StaticIdentities.OrderBy(item => item.Identity, StringComparer.Ordinal).ToArray();
            if (!actualStatics.SequenceEqual(certifiedStatics))
                throw new InvalidDataException("Contract import static identities differ from the selected implementation.");
            imports.ValidateStatics(actualStatics);
            implementationState[key] = 2;
        }
        catch
        {
            implementationState.Remove(key);
            throw;
        }
    }

    internal void ValidateStatics(IEnumerable<StaticIdentityRecord> application) =>
        StaticIdentity.Validate(application.Concat(bindings.SelectMany(binding => binding.StaticIdentities)));

    static bool MetadataEqual<T>(T expected, T actual) => JsonElement.DeepEquals(
        JsonSerializer.SerializeToElement(expected, ContractInterface.Json), JsonSerializer.SerializeToElement(actual, ContractInterface.Json));

    internal string? Identity(Instruction instruction) => sites.TryGetValue(instruction, out int slot) ? bindings[slot].Identity : null;

    internal bool ValidateByref(TypeReference type, FeatureProfile profile)
    {
        if (type is not ByReferenceType reference || ContractMethodMetadata.Primitive(reference.ElementType) ||
            reference.ElementType.Scope is not AssemblyNameReference scope) return false;
        ContractMethodMetadata.RejectModifiers(reference);
        if (allowedDependencies is not null && !allowedDependencies.Contains(scope.FullName))
            throw new InvalidDataException("Undeclared imported layout dependency: " + scope.FullName);
        if (!libraries.Any(candidate => candidate.Interface.AssemblyIdentity == scope.FullName) &&
            discovered.Remove(scope.Name, out Source? pending))
        {
            Load(pending);
            ValidateGraph();
        }
        Library? library = libraries.SingleOrDefault(candidate => candidate.Interface.AssemblyIdentity == scope.FullName);
        if (library is null || library.Interface.FormatVersion != 2)
            throw new InvalidDataException("Imported byref layout requires a pinned typed interface: " + reference.FullName);
        ContractLayout[] actual = ImportedLayoutMetadata.ForType(reference.ElementType, library.Module, profile.Architecture);
        foreach (ContractLayout layout in actual)
        {
            ContractLayout[] published = library.Interface.Exports.SelectMany(export => export.Layouts ?? [])
                .Where(candidate => candidate.Identity == layout.Identity).ToArray();
            if (published.Length == 0 || published.Any(candidate => !MetadataEqual(candidate, layout)))
                throw new InvalidDataException("Imported raw layout differs from selected implementation metadata: " + layout.Identity);
        }
        return true;
    }

    internal static string LeanSlot(Binding binding) =>
        "{ identity := " + JsonSerializer.Serialize(binding.Identity) + ", closureDigest := " + JsonSerializer.Serialize(binding.ClosureDigest) +
        ", parameterCount := " + binding.ParameterCount + ", hasThis := false, returnsValue := " + (binding.ReturnsValue ? "true" : "false") +
        (binding.TypedSignature is null ? "" : ", signature := some (" + binding.TypedSignature.Lean + "), layouts := { published := " +
            ImportedLayoutMetadata.RawLean(binding.PublishedLayouts) + ", actual := " + ImportedLayoutMetadata.RawLean(binding.ActualLayouts) +
            ", computed := " + binding.ComputedLayouts + " }") + " }";

    internal bool TryTranslate(Instruction instruction, int methodCount, out string translated)
    {
        if (sites.TryGetValue(instruction, out int slot))
        {
            translated = $".call {methodCount + slot} {bindings[slot].ParameterCount}";
            return true;
        }
        translated = "";
        return false;
    }

    // Bound libraries and their declared dependencies contribute modules to the extraction.
    internal SortedDictionary<string, string> InterfaceModules() => Modules(libraries.Where(used.Contains));

    static SortedDictionary<string, string> Modules(IEnumerable<Library> selected)
    {
        SortedDictionary<string, string> modules = new(StringComparer.Ordinal);
        foreach (InterfaceModule module in selected.SelectMany(library => library.Interface.InterfaceModules))
        {
            if ((modules.TryGetValue(module.Name, out string? prior) && prior != module.Source) ||
                modules.Keys.Any(name => name != module.Name && string.Equals(name, module.Name, StringComparison.OrdinalIgnoreCase)))
                throw new InvalidDataException("Conflicting contract interface module: " + module.Name);
            modules[module.Name] = module.Source;
        }
        return modules;
    }

    internal string EmitImports(int methodCount)
    {
        StringBuilder lean = new("import Extracted\nimport CIL.Safety.Imports\nimport CIL.Safety.OutcomeContract\n");
        foreach (string module in InterfaceModules().Keys) lean.AppendLine("import " + module);
        lean.AppendLine("\nnamespace Extracted\ndef ImportsHold (linked : _root_.CIL.Program) : Prop :=");
        lean.AppendLine(bindings.Count == 0 ? "  True" : "  " + string.Join(" \u2227\n  ", bindings.Select(binding =>
            $"@_root_.CIL.Safety.{(binding.ContractKind == "method" ? "MethodContract" : "OutcomeContract")}.Holds _ _ _root_.{binding.ContractConstant} linked {methodCount + binding.Slot}")));
        lean.AppendLine("end Extracted");
        return lean.ToString();
    }

    public void Dispose()
    {
        if (!ownsLibraries) return;
        foreach (Library library in libraries) library.Module.Dispose();
        libraries.Clear();
        used.Clear();
    }
}
