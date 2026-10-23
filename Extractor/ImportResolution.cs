using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal sealed class ImportResolution : IDisposable
{
    // A discovered sidecar is read only when a call site needs its library, so unused sidecars need no pins.
    internal sealed record Source(string SidecarPath, string ImplementationPath, string ExpectedSha256, string ExpectedInterfaceDigest, bool Discovered = false);
    internal sealed record Binding(int Slot, string Identity, string ImplementationPath, string ImplementationSha256,
        string SidecarPath, string SidecarSha256, string InterfaceDigest, string ContractConstant,
        string ClosureDigest, string Signature, int ParameterCount, bool ReturnsValue, string Profile, string ContractKind,
        string CertificationTheorem, string CertificationStatement, string CertificationStatementDigest, bool IsReferenceAssembly);
    sealed record Library(Source Source, ContractInterface Interface, string SidecarSha256, ModuleDefinition Module);
    readonly List<Library> libraries = [];
    readonly HashSet<Library> used = [];
    readonly Dictionary<string, Source> discovered = new(StringComparer.Ordinal);
    readonly List<Binding> bindings = [];
    readonly Dictionary<Instruction, int> sites = [];
    internal IReadOnlyList<Binding> Bindings => bindings;

    internal ImportResolution(IEnumerable<Source> sources)
    {
        try
        {
            foreach (Source source in sources)
            {
                if (source.Discovered) discovered[Path.GetFileName(source.SidecarPath)[..^".leancil.contracts".Length]] = source;
                else Load(source);
            }
            Modules(libraries);
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
                    if (libraries.Any(library => library.Module.Assembly.Name.Name == module.Assembly.Name.Name))
                        throw new InvalidDataException("Duplicate import assembly: " + module.Assembly.Name.Name);
                    libraries.Add(new(source, contract, ContractInterface.Hash(sidecar), module));
                }
                catch { module.Dispose(); throw; }
    }

    internal static bool External(MethodReference reference, ModuleDefinition module) =>
        reference.DeclaringType.Scope is AssemblyNameReference scope && scope.FullName != module.Assembly.Name.FullName;

    internal void Admit(MethodReference reference, Instruction instruction, FeatureProfile profile)
    {
        // Shapes no sidecar can import are rejected before any sidecar is read or suggested.
        if (instruction.OpCode.Code != Code.Call)
            throw new InvalidDataException("Contract imports support call only, not callvirt, newobj or ldftn.");
        if (reference is GenericInstanceMethod || reference.HasGenericParameters || reference.DeclaringType is TypeSpecification || reference.DeclaringType.HasGenericParameters)
            throw new InvalidDataException("Generic contract imports are not supported in version 1.");
        if (reference.DeclaringType.Scope.Name is "System.Runtime" or "System.Runtime.Intrinsics" or "System.Memory" or "System.Private.CoreLib" or "mscorlib" or "netstandard")
            throw new InvalidDataException($"External managed dependency: {reference.FullName}\n  Contract imports from framework assemblies are not supported.");
        string assembly = reference.DeclaringType.Scope is AssemblyNameReference scope ? scope.FullName : reference.DeclaringType.Scope.Name;
        if (!libraries.Any(candidate => candidate.Interface.AssemblyIdentity == assembly) &&
            discovered.Remove(reference.DeclaringType.Scope.Name, out Source? pending))
        {
            Load(pending);
            Modules(libraries);
        }
        Library? library = libraries.SingleOrDefault(candidate => candidate.Interface.AssemblyIdentity == assembly);
        if (library is null)
            throw new InvalidDataException($"External managed dependency: {reference.FullName}\n  Next: supply --import {reference.DeclaringType.Scope.Name}.leancil.contracts and --import-sha256 {reference.DeclaringType.Scope.Name}=<hex> and --import-interface-sha256 {reference.DeclaringType.Scope.Name}=<hex>.");
        string identity = assembly + "::" + reference.FullName;
        ContractExport export = library.Interface.Exports.SingleOrDefault(candidate => candidate.Identity == identity)
            ?? throw new InvalidDataException("Contract export not present: " + identity);
        MethodDefinition[] definitions = library.Module.GetTypes().Where(type => type.FullName == reference.DeclaringType.FullName)
            .SelectMany(type => type.Methods).Where(method => method.FullName == reference.FullName).ToArray();
        if (definitions.Length != 1) throw new InvalidDataException("Contract export definition not present or ambiguous: " + identity);
        MethodDefinition definition = definitions[0];
        if (definition.HasGenericParameters || definition.DeclaringType.HasGenericParameters)
            throw new InvalidDataException("Generic contract imports are not supported in version 1.");
        string visibility = definition.IsPublic ? "public" : definition.IsFamily || definition.IsFamilyOrAssembly ? "protected" : "private";
        if (!definition.IsStatic || definition.IsVirtual || visibility == "private" || export.Visibility != visibility ||
            reference.HasThis || reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default || definition.IsPInvokeImpl)
            throw new InvalidDataException("Contract export must be static, non-virtual and public or protected with matching visibility.");
        MetadataValidation.Type(reference.ReturnType, reference.Module, returns: true);
        foreach (ParameterDefinition parameter in reference.Parameters) MetadataValidation.Type(parameter.ParameterType, reference.Module);
        if (TypeIdentity(definition.ReturnType) != TypeIdentity(reference.ReturnType) ||
            !definition.Parameters.Select(parameter => TypeIdentity(parameter.ParameterType)).SequenceEqual(
                reference.Parameters.Select(parameter => TypeIdentity(parameter.ParameterType)), StringComparer.Ordinal))
            throw new InvalidDataException("Contract import exact signature identity mismatch.");
        if (export.Signature != reference.FullName || export.ParameterCount != reference.Parameters.Count || export.HasThis != reference.HasThis ||
            export.ReturnsValue != (reference.ReturnType.MetadataType != MetadataType.Void) || definition.Parameters.Count != export.ParameterCount)
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
        used.Add(library);
        int slot = bindings.FindIndex(binding => binding.Identity == identity);
        if (slot < 0)
        {
            slot = bindings.Count;
            bindings.Add(new(slot, identity, Path.GetFullPath(library.Source.ImplementationPath), library.Interface.ImplementationSha256,
                Path.GetFullPath(library.Source.SidecarPath), library.SidecarSha256, library.Interface.InterfaceDigest,
                export.ContractConstant, export.ClosureDigest, export.Signature, export.ParameterCount, export.ReturnsValue, profile.Name, export.Kind,
                certification.Theorem, certification.Statement, certification.StatementDigest, library.Interface.IsReferenceAssembly));
        }
        sites[instruction] = slot;
    }

    static string TypeIdentity(TypeReference type) => type switch
    {
        ByReferenceType reference => "&" + TypeIdentity(reference.ElementType),
        GenericInstanceType generic => TypeIdentity(generic.ElementType) + "<" + string.Join(",", generic.GenericArguments.Select(TypeIdentity)) + ">",
        TypeSpecification specification => specification.GetType().Name + ":" + TypeIdentity(specification.ElementType),
        _ => (type.Scope is AssemblyNameReference assembly ? assembly.FullName :
            type.Scope is ModuleDefinition module ? module.Assembly.Name.FullName : type.Scope.Name) + "::" + type.FullName
    };

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

    // Only libraries with a bound call site contribute modules to the extraction.
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
        foreach (Library library in libraries) library.Module.Dispose();
        libraries.Clear();
        used.Clear();
    }
}
