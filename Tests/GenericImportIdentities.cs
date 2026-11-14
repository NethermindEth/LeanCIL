using System.Globalization;
using System.Reflection;
using System.Text;
using Mono.Cecil;
using Nethermind.LeanCIL;

partial class Program
{
    static void CheckGenericImportIdentities(string library, string output, Type metadata)
    {
        Run(["lake", "build", "CIL.Extraction.MetadataBinding"]);
        long previousNames = 0;
        foreach (int size in new[] { 64, 256, 1024 })
        {
            string path = Path.Combine(output, "ClosedNameScaling" + size + ".lean");
            File.WriteAllText(path, $$"""
                import CIL.Extraction.MetadataBinding
                open CIL CIL.Extraction
                set_option maxRecDepth 100000
                set_option maxHeartbeats 10000000
                /-- Closed arguments share the independently expected UInt32 spelling. -/
                def arguments : List ResolvedType := List.replicate {{size}} (.primitive 9)
                /-- Closed argument names are indexed once for the signature. -/
                def argumentNames : SearchTree (List Nat) := SearchTree.ofSorted
                  (((arguments.mapM (cecilName false resolveFuel)).getD []).zipIdx.map
                    fun (name, index) => (index, name))
                /-- Open parameters select every argument in declaration order. -/
                def parameters : List ResolvedType := (List.range {{size}}).map .mvar
                /-- Parameter rendering preserves each selected argument's name. -/
                theorem closed_names :
                    parameters.mapM (contractClosedName argumentNames resolveFuel) =
                        some (List.replicate {{size}} (bytesOf "System.UInt32")) := by decide +kernel
                #print axioms closed_names
                #eval show IO Nat from IO.getNumHeartbeats
                """);
            string result = Compile(path);
            long heartbeats = long.Parse(result.Split('\n', StringSplitOptions.TrimEntries |
                StringSplitOptions.RemoveEmptyEntries).Last(), CultureInfo.InvariantCulture);
            Console.WriteLine($"PASS closed names {size} arguments and parameters: {heartbeats} heartbeats");
            if (previousNames != 0 && heartbeats > previousNames * 6)
                throw new InvalidOperationException("Closed name indexing exceeded linear growth: " + result);
            previousNames = heartbeats;
        }
        using var pinned = new PinnedMetadata(metadata.Assembly, library);
        MethodInfo instantiate = metadata.GetMethod("Instantiate", BindingFlags.Static | BindingFlags.NonPublic)!;
        ModuleDefinition module = pinned.Module;
        string[] identities = module.GetType("TypedFixture.Library").Methods
            .Where(method => method.Name is "Identity" or "Ignore" or "Overload" or "First")
            .Append(module.GetType("TypedFixture.\u03A9wner").Methods.Single(method => method.HasGenericParameters))
            .Select(Check).ToArray();
        if (identities.Distinct(StringComparer.Ordinal).Count() != identities.Length)
            throw new InvalidOperationException(
                "Distinct open definitions produced the same closed contract identity.");
        Console.WriteLine("PASS exact generic identity, void, Unicode and distinct open overloads");

        MethodDefinition identity = module.GetType("TypedFixture.Library").Methods
            .Single(method => method.Name == "Identity");
        long previous = 0;
        foreach (int size in new[] { 128, 512, 2048 })
        {
            identity.Name = new string('N', size);
            string text = Source(identity, Selected(identity));
            string path = Path.Combine(output, "IdentityScaling" + size + ".lean");
            File.WriteAllText(path, text + "\n#eval show IO Nat from IO.getNumHeartbeats\n");
            string result = Compile(path);
            long heartbeats = long.Parse(result.Split('\n', StringSplitOptions.TrimEntries |
                StringSplitOptions.RemoveEmptyEntries).Last(), CultureInfo.InvariantCulture);
            if (previous != 0 && heartbeats > previous * 6)
                throw new InvalidOperationException("Generic identity construction exceeded linear growth: " + result);
            Console.WriteLine($"PASS generic identity {size} name bytes: {heartbeats} heartbeats");
            previous = heartbeats;
        }

        previous = 0;
        foreach (int size in new[] { 16, 64, 256 })
        {
            MethodDefinition counted = new("Counted", Mono.Cecil.MethodAttributes.Public |
                Mono.Cecil.MethodAttributes.Static,
                module.TypeSystem.Void) {
                    DeclaringType = identity.DeclaringType,
                    CallingConvention = MethodCallingConvention.Generic };
            for (int index = 0; index < size; index++)
                counted.GenericParameters.Add(new GenericParameter("T" + index, counted));
            counted.ReturnType = counted.GenericParameters[^1];
            for (int index = 0; index < size; index++)
                counted.Parameters.Add(new ParameterDefinition(counted.GenericParameters[^1]));
            string path = Path.Combine(output, "IdentityCountScaling" + size + ".lean");
            File.WriteAllText(path, Source(counted, Selected(counted)) +
                "\n#eval show IO Nat from IO.getNumHeartbeats\n");
            string result = Compile(path);
            long heartbeats = long.Parse(result.Split('\n', StringSplitOptions.TrimEntries |
                StringSplitOptions.RemoveEmptyEntries).Last(), CultureInfo.InvariantCulture);
            Console.WriteLine($"PASS generic identity {size} arguments and parameters: {heartbeats} heartbeats");
            if (previous != 0 && heartbeats > previous * 6)
                throw new InvalidOperationException("Generic argument indexing exceeded linear growth: " + result);
            previous = heartbeats;
        }

        string Selected(MethodDefinition method)
        {
            TypeReference[] arguments = method.GenericParameters.Select((_, index) =>
                index == 0 ? module.TypeSystem.UInt64 : module.TypeSystem.UInt32).ToArray();
            object selection = instantiate.Invoke(null, [method, arguments, "scalar", true])!;
            return (string)selection.GetType().GetProperty("Identity")!.GetValue(selection)!;
        }

        static string Compile(string path)
        {
            string result = Run(["lake", "env", "lean", "-DElab.async=false", path]);
            if (result.Contains("sorryAx", StringComparison.Ordinal))
                throw new InvalidOperationException("Generic identity proof contains an unproved claim: " + result);
            return result;
        }

        string Check(MethodDefinition method)
        {
            string identity = Selected(method);
            string path = Path.Combine(output, "IdentityKey" + method.MetadataToken.ToUInt32() + ".lean");
            string checks = Source(method, identity) + """

                /-- Changing any definition or instantiation component changes the contract key. -/
                theorem mutations_rejected :
                    ([{ site with name := bytesOf "Other" },
                      { site with genericArity := site.genericArity + 1 },
                      { site with convention := 0x30 },
                      { site with result := .primitive 9 },
                      { site with parameters := [.primitive 9] },
                      { site with methodArguments := some [.primitive 9] },
                      { site with methodArguments := some [] },
                      { site with methodArguments := some [.pointer (.primitive 11)] }].all fun changed =>
                        !changed.externalMatches frame identity) = true := by decide +kernel
                #print axioms mutations_rejected
                /-- An appended descriptor byte cannot be accepted as the same contract. -/
                theorem appended_byte_rejected :
                    site.externalMatches frame (identity ++ "x") = false := by decide +kernel
                #print axioms appended_byte_rejected
                /-- Unknown or incorrectly scoped argument kinds have no generic contract identity. -/
                theorem malformed_argument_rejected :
                    ([TypeKind.external none, .external (some true)].all fun kind =>
                      !({ site with methodArguments := some [.named {
                          scope := bytesOf "Other", name := bytesOf "System.UInt64",
                          parts := [], kind := kind, pinned := false }] }).externalMatches
                        frame identity) = true := by decide +kernel
                #print axioms malformed_argument_rejected
                /-- A differently scoped owner cannot use the same imported contract identity. -/
                theorem different_owner_rejected :
                    (match site.owner with
                    | .named owner => ({ site with owner := .named {
                        owner with scope := bytesOf "Other" } }).externalMatches frame identity
                    | _ => true) = false := by decide +kernel
                #print axioms different_owner_rejected
                /-- Closed imported signatures cannot retain a method or owner parameter. -/
                theorem open_parameters_refused :
                    ({ site with result := .var 0 }).contractName frame = none ∧
                    ({ site with parameters := [.byref (.var 0)] }).contractName frame = none ∧
                    ({ site with result := .mvar site.genericArity }).contractName frame = none :=
                  by decide +kernel
                #print axioms open_parameters_refused
                """;
            if (method.Name == "Overload")
            {
                string otherType = method.ReturnType is GenericParameter ? ".primitive 11" : ".mvar 0";
                checks += $$"""

                    /-- Equal closed signatures retain distinct open overload identities. -/
                    theorem distinct_open_overload :
                        ({ site with result := {{otherType}}, parameters := [{{otherType}}] }).externalMatches
                          frame identity = false := by decide +kernel
                    #print axioms distinct_open_overload
                    """;
            }
            if (method.Name == "First") checks += """

                /-- Generic arguments and open parameters retain their order. -/
                theorem ordered_components :
                    ({ site with methodArguments := some [.primitive 9, .primitive 11] }).externalMatches
                        frame identity = false ∧
                    ({ site with parameters := [.mvar 1, .mvar 0] }).externalMatches
                        frame identity = false := by decide +kernel
                #print axioms ordered_components
                """;
            File.WriteAllText(path, checks);
            Compile(path);
            return identity;
        }
    }

    static string Source(MethodDefinition method, string identity)
    {
        static string Bytes(string value) => "[" + string.Join(",", Encoding.UTF8.GetBytes(value)) + "]";
        static string Type(TypeReference type) => type is GenericParameter parameter
            ? ".mvar " + parameter.Position : ".primitive " + (int)type.MetadataType;
        string scope = method.Module.Assembly.Name.FullName;
        string arguments = string.Join(",", method.GenericParameters.Select((_, index) =>
            index == 0 ? ".primitive 11" : ".primitive 9"));
        string parameters = string.Join(",", method.Parameters.Select(parameter => Type(parameter.ParameterType)));
        ExternalIdentityEvidence evidence = new();
        string identityReference = evidence.Reference(identity, reachable: true);
        StringBuilder encoded = new();
        evidence.Emit(encoded);
        return $$"""
            import CIL.Extraction.MetadataBinding
            open CIL CIL.Extraction
            set_option maxRecDepth 100000
            set_option maxHeartbeats 10000000
            {{encoded}}
            /-- The primitive scope named by the compiled fixture. -/
            def frame : Frame := {
              corlib := some runtimeScopeBytes, anchor := runtimeScopeBytes,
              arity := 0, ownerArity := 0 }
            /-- The raw open signature and MethodSpec arguments of the compiled fixture. -/
            def site : MethodSite := {
              owner := .named {
                scope := {{Bytes(scope)}}, name := {{Bytes(method.DeclaringType.FullName)}},
                parts := [], kind := .external none, pinned := false },
              name := {{Bytes(method.Name)}}, convention := 0x10,
              genericArity := {{method.GenericParameters.Count}},
              result := {{Type(method.ReturnType)}},
              parameters := [{{parameters}}],
              definition := none,
              methodArguments := some [{{arguments}}] }
            /-- The identity emitted by the production C# selector. -/
            def identity : String := {{identityReference}}
            /-- The kernel reconstructs the producer's entire generic contract identity. -/
            theorem exact_identity : site.externalMatches frame identity = true := by decide +kernel
            #print axioms exact_identity
            """;
    }
}
