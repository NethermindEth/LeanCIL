#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/BatchVerification.cs
#:include ExceptionMembers.cs
#:include ContractVariants.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Throws");
Directory.CreateDirectory(root);
var rejected = new RejectedEvidence(root);
var queue = new GeneratedQueue(verification, assembly);
var controls = new GeneratedEvidence(Path.Combine(root, "EvidenceControls"));
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Throws")!;
using var exampleModule = ModuleDefinition.ReadModule(assembly);
var throwMethods = exampleModule.GetType("Examples.Throws").Methods;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution");

// Compare the exception type and throw site with the compiled method.
foreach (var (name, selector, inputs) in new (string, string, uint[][])[]
{
    ("Null", "Throws::Null(uint)", [[0], [1]]),
    ("Quotient", "Throws::Quotient(uint,uint)", [[7, 2], [7, 0], [0, 0], [uint.MaxValue, 1]]),
    ("Percent", "Throws::Percent(uint)", [[0], [100], [101], [uint.MaxValue]]),
    ("Inner", "Throws::Inner(uint)", [[0], [1]]),
    ("Message", "Throws::Message(uint)", [[0], [1]]),
    ("NamedArgument", "Throws::NamedArgument(uint)", [[0], [1]]),
    ("ArgumentInner", "Throws::ArgumentInner(uint)", [[0], [1]]),
    ("ActualValue", "Throws::ActualValue(uint)", [[0], [1]])
})
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", selector, folder));
    var extracted = Path.Combine(folder, "Extracted.lean");
    var source = File.ReadAllText(extracted);
    var entry = throwMethods.Single(candidate => candidate.Name == name);
    var boundConstructor = name is "Percent" or "ActualValue" or "ArgumentInner" or "Inner" or "Message" or
        "NamedArgument";
    var method = name is "Null" or "Quotient" ? 1 : 0;
    var owner = method == 0 ? entry : ((MethodReference)entry.Body.Instructions
        .Single(instruction => instruction.OpCode.Code == Code.Call).Operand).Resolve();
    var body = owner.Body.Instructions;
    var pc = body.IndexOf(body.Single(instruction => instruction.OpCode.Code == Code.Throw));
    if (boundConstructor)
    {
        if (!source.Contains("def program : Program := boundPackage.methods", StringComparison.Ordinal) ||
            source.Contains("cil_decoded_method method0", StringComparison.Ordinal))
            throw new InvalidOperationException("Expected the physical constructor program");
    }
    else if (!IsDecodedMethod(source, method)) throw new InvalidOperationException($"Expected decoded {owner.FullName}");
    if (name == "Null")
    {
        var obligation = $"method{method}_features_validated";
        source = NarrowEvidence(source, obligation);
        var control = Path.Combine(folder, "EvidenceControl.lean");
        File.WriteAllText(control, source);
        controls.Add(control, "PASS exact null-throw evidence control", obligation);
        foreach (var opcode in new[] { 20, 122 })
        {
            var before = $"opcode := {opcode}, operand := .none";
            if (!source.Contains(before, StringComparison.Ordinal))
                throw new InvalidOperationException("Missing null-throw operand: " + opcode);
            var forgedOperand = Path.Combine(folder, $"Operand-{opcode}.lean");
            var rawPc = opcode == 122 ? pc : pc - 1;
            File.WriteAllText(forgedOperand, ForgeClosedCode(source, method,
                $$"""modify {{rawPc}} (fun raw => { raw with operand := .integer 0 })"""));
            rejected.Add(forgedOperand, "PASS null-throw operand forgery rejected: " + opcode,
                "Extraction.FeatureFlowValid", FeatureObligation(method), "is false");
        }
    }

    if (name == "Quotient")
    {
        var ctorPc = body.IndexOf(body.Single(site => site.OpCode.Code == Code.Newobj));
        var obligation = FeatureObligation(method);
        var evidence = NarrowEvidence(source, $"method{method}_features_validated");
        var control = Path.Combine(folder, "ConstructorControl.lean");
        File.WriteAllText(control, evidence);
        controls.Add(control, "PASS compiled exception constructor signature", $"method{method}_features_validated");
        foreach (var (changed, field) in new[]
        {
            ("vararg", "declared.convention := 0x25"),
            ("explicit-this", "declared.convention := 0x60"),
            ("result", "declared.returnType := .atom Extraction.runtimeScope \"System.Int32\""),
            ("generic-arity", "method.genericArity := 1")
        })
        {
            var changedFile = Path.Combine(folder, $"Constructor-{changed}.lean");
            File.WriteAllText(changedFile, ForgeClosedCode(evidence, method, $$"""
                modify {{ctorPc}} (fun raw => { raw with operand := match raw.operand with
                  | .call site => .call { site with {{field}} }
                  | operand => operand })
                """));
            rejected.Add(changedFile, $"PASS altered {changed} exception constructor rejected",
                "Extraction.FeatureFlowValid", obligation, "is false");
        }
    }

    string? label = null;
    var claims = inputs.Select(input =>
    {
        string outcome;
        try { outcome = $".ok [.scalar (.i32 {(uint)runtime.GetMethod(name)!.Invoke(null, [.. input.Cast<object>()])!})]"; }
        catch (TargetInvocationException error)
        {
            label = ExceptionMember(error.InnerException!);
            outcome = $".error \u27e8{method}, {pc}, .thrown .{label}\u27e9";
        }
        var args = string.Join(", ", input.Select(v => $".scalar (.i32 {v})"));
        if (boundConstructor)
            return $"(Extracted.translation_valid.invoke .net11WinX64 66 [{args}]).map " +
                $"(fun loaded => loaded.map (·.map Prod.snd)) = some (.ok ({outcome}))";
        return $"(CIL.Safety.invoke Extracted.program 64 0 [{args}] CIL.Safety.Memory.empty).map Prod.snd = {outcome}";
    }).ToList();
    if (label is null) throw new InvalidOperationException($"No runtime input reached the throw in {name}");
    var nullLoads = body.Select((site, index) => (site, index)).Where(item => item.site.OpCode.Code == Code.Ldnull);
    var nullEquations = string.Join('\n', nullLoads.Select(item => boundConstructor
        ? $"example : Extracted.method{method}.code[{item.index}]? = some .ldnull := by cil_kernel_rfl"
        : $"example : Extracted.method{method}.code[{item.index}]? = some .ldnull := " +
        $"Extracted.method{method}_instruction{item.index}"));
    var raisedInstruction = name == "Null" ? ".throw" : $"(.throw (some .{label}))";
    var throwSite = boundConstructor
        ? $"example : (Extracted.program[{method}]? >>= fun m => m.code[{pc}]?) = some .throw := by cil_kernel_rfl"
        : $"example : Extracted.method{method}.code[{pc}]? = some {raisedInstruction} := Extracted.method{method}_instruction{pc}";
    var entryCheck = name switch
    {
        "Null" => "example : (Extracted.translation_valid.entry .portable).map (·.methods) = some Extracted.program := by cil_kernel_rfl",
        _ => ""
    };
    var proof = Path.Combine(folder, "BoundaryProof.lean");
    File.WriteAllText(proof, $$"""
        import Extracted
        import CIL.Safety.Execution
        namespace ExampleProof
        {{entryCheck}}
        {{nullEquations}}
        {{throwSite}}
        theorem correctness :
          {{string.Join(" \u2227\n  ", claims)}} := by
          repeat' first | apply And.intro | {{(boundConstructor ? "cil_kernel_rfl" : "rfl")}}
        #print axioms correctness
        end ExampleProof
        """);
    queue.Add(new(selector, proof, Path.Combine(root, name + "-Verified")), () =>
        Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons, {label} located at method {method} pc {pc}"));

    if (!boundConstructor)
    {
        // A forged type must fail the feature certificate, independently of the instruction lemma.
        var forgedLabel = label == "invalidOperation" ? "divideByZero" : "invalidOperation";
        var forged = ForgeDecodedInstruction(source, method, pc, $"fun _ => .throw (some .{forgedLabel})");
        var mutated = Path.Combine(root, name + "-forged.lean");
        File.WriteAllText(mutated, forged);
        rejected.Add(mutated, $"PASS {name}: forged raised type rejected by the feature certificate",
            "Extraction.FeatureFlowValid", FeatureObligation(method), "is false");
    }
    if (boundConstructor)
    {
        using var translated = ModuleDefinition.ReadModule(assembly);
        var translatedMethod = translated.GetType("Examples.Throws").Methods.Single(candidate => candidate.Name == name);
        foreach (var literal in translatedMethod.Body.Instructions.Where(site => site.OpCode.Code == Code.Ldstr))
            literal.Operand = (string)literal.Operand switch
            {
                "value" => "valeur",
                "must not exceed 100" => "La valeur dépasse la limite.",
                "invalid value" => "valeur non valide",
                var text => throw new InvalidOperationException("Untranslated exception literal: " + text)
            };
        var image = Path.Combine(folder, "Examples.dll");
        translated.Write(image);
        queue.Add(new(selector, proof, Path.Combine(root, name + "-Translated"), Assembly: image), () =>
            Console.WriteLine($"PASS {name}: the same boundary proof checks with translated exception literals"));

        if (name is "ActualValue" or "ArgumentInner" or "Inner" or "Message" or "NamedArgument")
        {
            foreach (var (suffix, path) in new[] { ("", assembly), ("-Translated", image) })
                queue.Add(new(selector, At("Tests/ExceptionConstructor/Proof.lean"),
                    Path.Combine(root, name + "-All" + suffix), Theorem: "ExceptionConstructorProof.correctness",
                    Assembly: path), () => Console.WriteLine($"PASS {name}: every input and getter completion{suffix}"));
            continue;
        }

        var rawProof = CompiledPercentProof(folder);
        foreach (var (suffix, assemblyPath) in new[] { ("", assembly), ("-Translated", image) })
        {
            queue.Add(new(selector, At("Examples/Proofs/Percent.lean"),
                Path.Combine(root, "Percent-Managed" + suffix), Theorem: "ExampleProof.correctness",
                Assembly: assemblyPath), () => Console.WriteLine("PASS Percent: managed entry from empty storage" + suffix));
            queue.Add(new(selector, At("Examples/Proofs/Percent.lean"),
                Path.Combine(root, "Percent-ZeroBudget" + suffix), Theorem: "ExampleProof.zeroBudget",
                Assembly: assemblyPath), () => Console.WriteLine("PASS Percent: zero quota fails at newobj" + suffix));
            verification.Verify(assemblyPath, "Examples", selector, rawProof, Path.Combine(root, "Percent-Raw" + suffix),
                theorem: "CompiledPercent.verified");
            Console.WriteLine("PASS Percent: decoded caller and CoreLib exception path at every heap quota" + suffix);
        }
        CheckPercentVariants(translated, translatedMethod, selector);
    }

    if (name == "Null")
    {
        var nullPc = body.IndexOf(body.First(site => site.OpCode.Code == Code.Ldnull));
        var erased = Path.Combine(root, name + "-erased-null.lean");
        File.WriteAllText(erased, ForgeDecodedInstruction(source, method, nullPc, "fun _ => .nop"));
        rejected.Add(erased, $"PASS {name}: erasing the null load rejected",
            "Extraction.FeatureFlowValid", FeatureObligation(method), "is false");
        var nonNull = Path.Combine(root, name + "-non-null.lean");
        const string nullLoad = "opcode := 20, operand := .none";
        if (!source.Contains(nullLoad, StringComparison.Ordinal))
            throw new InvalidOperationException("Missing null constructor argument");
        var changed = """
            map (fun raw => if raw.opcode == 20 then
              { raw with opcode := 114, operand := .text "not null" } else raw)
            """.ReplaceLineEndings(" ");
        File.WriteAllText(nonNull, ForgeClosedCode(source, method, changed));
        rejected.Add(nonNull, $"PASS {name}: non-null constructor operand rejected",
            "Extraction.FeatureFlowValid", FeatureObligation(method), "is false");
    }
}

queue.Flush();
controls.Check(replay: false);
rejected.Check();

// Exercise stack-based throws, constructor signatures and control flow in compiled images.
foreach (var (mutation, marker) in new[]
{
    ("handler", "Unsupported method metadata"),
    ("no-throw", "Contract imports support call only, not callvirt, newobj or ldftn."),
    ("separated-null", ""),
    ("null-branch", ""),
    ("empty-throw-branch", "Invalid evaluation stack"),
    ("scalar-throw", "Throw requires an object on the evaluation stack"),
    ("interior-branch", "Branch into a folded throw"),
    ("non-exception", "Unsupported exception constructor"),
    ("dead-non-exception", ""),
    ("missing-constructor", "Unsupported exception constructor"),
    ("wrong-parameter", "Unsupported exception constructor"),
    ("instruction-only", "Unsupported exception constructor"),
    ("explicit-this", "Unsupported exception constructor"),
    ("vararg", "Unsupported exception constructor")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var helper = module.GetType("Examples.Throws").Methods.Single(m => m.Name == "ThrowDivideByZero").Body;
        var code = helper.Instructions;
        var il = helper.GetILProcessor();
        if (code.Count != 2 || code[0].OpCode.Code != Code.Newobj || code[1].OpCode.Code != Code.Throw)
            throw new InvalidOperationException("Unexpected compiled throw helper");
        switch (mutation)
        {
            case "handler":
                var leave = il.Create(OpCodes.Ret);
                il.Append(il.Create(OpCodes.Pop));
                il.Append(il.Create(OpCodes.Leave, leave));
                il.Append(leave);
                helper.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
                {
                    TryStart = code[0], TryEnd = code[2], HandlerStart = code[2], HandlerEnd = leave,
                    CatchType = module.ImportReference(typeof(Exception))
                });
                break;
            case "no-throw":
                il.Replace(code[1], il.Create(OpCodes.Pop));
                il.Append(il.Create(OpCodes.Ret));
                break;
            case "separated-null":
                il.Replace(code[0], il.Create(OpCodes.Ldnull));
                il.InsertBefore(code[1], il.Create(OpCodes.Nop));
                break;
            case "null-branch":
                il.Replace(code[0], il.Create(OpCodes.Ldnull));
                var targetThrow = code[1];
                il.InsertBefore(targetThrow, il.Create(OpCodes.Br_S, targetThrow));
                il.InsertBefore(targetThrow, il.Create(OpCodes.Nop));
                break;
            case "empty-throw-branch":
                var deadLoad = il.Create(OpCodes.Ldnull);
                il.Replace(code[0], deadLoad);
                il.InsertBefore(deadLoad, il.Create(OpCodes.Br, code[1]));
                break;
            case "scalar-throw":
                il.Replace(code[0], il.Create(OpCodes.Ldc_I4_1));
                break;
            case "non-exception":
            case "dead-non-exception":
            case "missing-constructor":
            case "wrong-parameter":
            case "instruction-only":
            {
                var original = (MethodReference)code[0].Operand;
                var typeName = mutation switch
                {
                    "non-exception" or "dead-non-exception" => "Object",
                    "instruction-only" => "InvalidCastException",
                    _ => "DivideByZeroException"
                };
                var type = new TypeReference("System", typeName, module, original.DeclaringType.Scope);
                var constructor = new MethodReference(".ctor", module.TypeSystem.Void, type) { HasThis = true };
                code[0].Operand = constructor;
                if (mutation is "missing-constructor" or "wrong-parameter")
                {
                    var creation = code[0];
                    for (int n = 0; n < (mutation == "missing-constructor" ? 2 : 1); n++)
                    {
                        constructor.Parameters.Add(new ParameterDefinition(mutation == "missing-constructor" ? module.TypeSystem.String : module.TypeSystem.Int32));
                        il.InsertBefore(creation, il.Create(OpCodes.Ldstr, "message"));
                    }
                }
                if (mutation == "dead-non-exception")
                {
                    var returned = il.Create(OpCodes.Ret);
                    il.InsertBefore(code[0], il.Create(OpCodes.Br, returned));
                    il.Append(returned);
                }
                break;
            }
            case "explicit-this": ((MethodReference)code[0].Operand).ExplicitThis = true; break;
            case "vararg": ((MethodReference)code[0].Operand).CallingConvention = MethodCallingConvention.VarArg; break;
            case "interior-branch":
                il.InsertBefore(code[0], il.Create(OpCodes.Br, code[1]));
                il.InsertBefore(code[0], il.Create(OpCodes.Ldnull));
                break;
        }
        module.Write(dll);
    }
    if (mutation is "non-exception" or "missing-constructor" or "separated-null" or "null-branch")
    {
        var expected = mutation switch
        {
            "separated-null" or "null-branch" => "System.NullReferenceException",
            "non-exception" => "System.Runtime.CompilerServices.RuntimeWrappedException",
            _ => "System.MissingMethodException"
        };
        try
        {
            Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Throws")!.GetMethod("Quotient")!.Invoke(null, [1u, 0u]);
            throw new InvalidOperationException("The runtime fixture unexpectedly returned: " + mutation);
        }
        catch (TargetInvocationException error) when (error.InnerException?.GetType().FullName == expected) { }
        Console.WriteLine($"PASS runtime throws {expected} for {mutation}");
    }
    var result = Execute(Extract("extract", dll, "Examples", "Throws::Quotient(uint,uint)", output));
    if (mutation is "separated-null" or "null-branch")
    {
        if (result.Code != 0) throw new InvalidOperationException(result.Output);
        var proof = Path.Combine(output, "StackThrow.lean");
        int throwPc = mutation == "separated-null" ? 2 : 3;
        File.WriteAllText(proof, $$"""
            import Extracted
            import CIL.Safety.Execution
            namespace ExampleProof
            theorem correctness :
                (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i32 1), .scalar (.i32 0)]
                  CIL.Safety.Memory.empty).map Prod.snd = .error ⟨1, {{throwPc}}, .thrown .nullReference⟩ := by
              decide +kernel
            #print axioms correctness
            end ExampleProof
            """);
        queue.Add(new("Throws::Quotient(uint,uint)", proof, Path.Combine(root, mutation + "-Verified"),
            Assembly: dll), () => Console.WriteLine("PASS stack-based null throw: " + mutation));
        continue;
    }
    if (mutation == "dead-non-exception")
    {
        if (result.Code != 0) throw new InvalidOperationException("Unreachable unsupported throw blocked extraction: " + result.Output);
        Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")], cwd: verification.CheckoutPackage());
        Console.WriteLine("PASS unreachable unsupported throw stays excluded and its certificate checks");
        continue;
    }
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        File.Exists(Path.Combine(output, "verified.json")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect throw rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
queue.Flush();
Console.WriteLine("PASS folded throws, located faults, runtime comparisons, forged types and exact-pattern rejection");

static string CompiledPercentProof(string folder)
{
    // Single-file consumer proofs carry their fixture declarations alongside the generated Extracted module.
    string[] modules = ["Tests.PercentRuntime.Source",
        "Tests.PercentRuntime.Program", "Tests.PercentRuntime.Startup", "Tests.PercentRuntime", "Tests.CompiledPercent.Proof"];
    var imports = new SortedSet<string>(StringComparer.Ordinal);
    var declarations = new List<string>();
    foreach (var module in modules)
    {
        foreach (var line in File.ReadLines(At(module.Replace('.', '/') + ".lean")))
        {
            if (line.StartsWith("import ", StringComparison.Ordinal))
            {
                if (!modules.Contains(line[7..])) imports.Add(line);
            }
            else declarations.Add(line);
        }
        declarations.Add("");
    }
    var path = Path.Combine(folder, "CompiledPercent.lean");
    File.WriteAllLines(path, imports.Concat(declarations));
    return path;
}

void CheckPercentVariants(ModuleDefinition image, MethodDefinition method, string selector)
{
    const string bounded = """
        def bounded : OutcomeContract W32 W32 where
          args value := [.scalar (.i32 value)]
          results result := [.scalar (.i32 result)]
          pre _ _ := True
          footprint _ := []
          post value _ _ result := result = value
          raises value _ := if value ≤ 100 then none else some .argumentOutOfRange
        """;
    // Preserve both translated ldstr operands and the constructor signature. Change only the exception class.
    var site = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Newobj);
    var original = (MethodReference)site.Operand;
    var throwPc = method.Body.Instructions.IndexOf(
        method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Throw));
    string Retyped(Type raised)
    {
        var owner = new TypeReference("System", raised.Name, image, original.DeclaringType.Scope);
        var replacement = new MethodReference(original.Name, original.ReturnType, owner) { HasThis = original.HasThis };
        foreach (var parameter in original.Parameters)
            replacement.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
        site.Operand = replacement;
        var changed = Path.Combine(root, $"Percent-{raised.Name}.dll");
        image.Write(changed);
        var invoked = Assembly.Load(File.ReadAllBytes(changed)).GetType("Examples.Throws")!.GetMethod("Percent")!;
        try { invoked.Invoke(null, [101u]); throw new InvalidOperationException("Expected " + raised.Name); }
        catch (TargetInvocationException error) when (error.InnerException?.GetType() == raised) { }
        return changed;
    }

    // ArgumentException(string, string) runs its CoreLib body, so the raised object refutes the range contract.
    var argument = Retyped(typeof(ArgumentException));
    var refuted = Path.Combine(root, "RetypedPercent.lean");
    File.WriteAllText(refuted, $$"""
        import Extracted
        import CIL.Runtime.EntryContract
        import CIL.Safety.Imports
        namespace ExampleProof
        open CIL CIL.Safety
        {{bounded}}
        private def image := (Extracted.translation_valid.entry .net11WinX64).getD (.translated [] [])
        private def memory := image.initialMemory.toOption.getD Memory.empty

        theorem correctness :
            bounded.RefutedAtEntryCLR Extracted.program 0 Extracted.translation_valid .net11WinX64 := by
          refine ⟨image, memory, by cil_kernel_rfl, by cil_kernel_rfl, by decide, ?_⟩
          intro extra
          apply OutcomeContract.RefutedCLR.of_fault (input := (101 : W32)) (initial := memory)
            (observed := 66) (fault := ⟨0, {{throwPc}}, .thrown .argument⟩)
          · exact ⟨rfl, trivial⟩
          · decide
          · apply invoke_extend (base := image.methods) ⟨extra, rfl⟩ _ _ _ _ _
            · intro fault wrong
              cases wrong
              decide
            · cil_kernel_rfl
          · have above : ¬ ((101 : W32) ≤ 100) := by decide
            simp only [OutcomeContract.ViolatesCLR, OutcomeContract.atStartup, bounded, ite_eq_right above]
            decide
        #print axioms correctness
        end ExampleProof
        """);
    verification.Verify(argument, "Examples", selector, refuted, Path.Combine(root, "Percent-Type-Refuted"));
    Console.WriteLine("PASS Percent: the bound ArgumentException constructor refutes the range contract");

    // ArgumentNullException(string, string) has no runtime binding, so its entry supplies no counterexample.
    var unboundImage = Retyped(typeof(ArgumentNullException));
    var unbound = Path.Combine(root, "UnboundPercent.lean");
    File.WriteAllText(unbound, """
        import Extracted
        import CIL.Runtime.EntryContract
        namespace ExampleProof
        open CIL CIL.Safety
        theorem correctness (c : OutcomeContract W32 W32) :
            ¬ c.RefutedAtEntryCLR Extracted.program 0 Extracted.translation_valid .net11WinX64 :=
          OutcomeContract.not_refuted_of_unbound (by cil_kernel_rfl)
        #print axioms correctness
        end ExampleProof
        """);
    verification.Verify(unboundImage, "Examples", selector, unbound, Path.Combine(root, "Percent-Type-Unbound"));
    Console.WriteLine("PASS Percent: ArgumentNullException has no binding and supplies no counterexample");

    site.Operand = original;
    var threshold = method.Body.Instructions.Single(instruction =>
        instruction.OpCode.Code == Code.Ldc_I4_S && Equals(instruction.Operand, (sbyte)100));
    threshold.Operand = (sbyte)101;
    var offByOne = Path.Combine(root, "Percent-OffByOne.dll");
    image.Write(offByOne);
    verification.VerifyContractVariant(assembly, "Examples", selector, Path.Combine(root, "Percent-Contract-Original"),
        offByOne, selector, Path.Combine(root, "Percent-OffByOne"), bounded, """
        theorem correctness :
            bounded.HoldsAtEntryCLR Extracted.program 0 Extracted.translation_valid .net11WinX64 :=
          ExampleProof.correctness
        """, """
        private def image := (Extracted.translation_valid.entry .net11WinX64).getD (.translated [] [])
        private def memory := image.initialMemory.toOption.getD Memory.empty

        theorem correctness :
            bounded.RefutedAtEntryCLR Extracted.program 0 Extracted.translation_valid .net11WinX64 := by
          refine ⟨image, memory, by cil_kernel_rfl, by cil_kernel_rfl, by decide, ?_⟩
          intro extra
          apply OutcomeContract.RefutedCLR.of_return (input := (101 : W32)) (initial := memory)
            (fuel := 66) (final := memory) (values := [.scalar (.i32 101)])
          · exact ⟨rfl, trivial⟩
          · apply invoke_extend (base := image.methods) ⟨extra, rfl⟩ _ _ _ _ _
            · intro fault impossible
              cases impossible
            · cil_kernel_rfl
          · trivial
        """, example: At("Examples/Proofs/Percent.lean"), imports: "import CIL.Runtime.EntryContract\nimport CIL.Safety.Imports");
    Console.WriteLine("PASS Percent: returning 101 refutes the packaged CLR contract at its first out-of-range input");
}
