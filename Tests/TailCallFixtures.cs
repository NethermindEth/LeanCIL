using Mono.Cecil;
using Mono.Cecil.Cil;

partial class Program
{
    static void AddTailCallFixtures(string assembly, string root, GeneratedEvidence evidence,
        RejectedEvidence rejected)
    {
        var names = new[] { "Forward", "ForwardReference", "ForwardVoid", "ForwardThrow", "LocalReference" };
        var dll = Path.Combine(root, "TailCalls.dll");
        var callPcs = new Dictionary<string, int>(StringComparer.Ordinal);
        using (var module = ModuleDefinition.ReadModule(assembly))
        {
            foreach (var method in module.GetType("Examples.TailCalls").Methods.Where(method => names.Contains(method.Name)))
            {
                var call = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Call);
                if (call.Next?.OpCode.Code != Code.Ret) throw new InvalidOperationException("Missing tail-call fixture return");
                method.Body.GetILProcessor().InsertBefore(call, Instruction.Create(OpCodes.Tail));
                callPcs.Add(method.Name, method.Body.Instructions.IndexOf(call));
            }
            module.Write(dll);
        }
        foreach (var name in names)
        {
            var byref = name is "ForwardReference" or "ForwardVoid";
            var signature = "System.Int32" + (byref ? "&" : "");
            var output = Path.Combine(root, "Tail-" + name);
            Run(["dotnet", ExtractorPath, "extract", dll, $"TailCalls::{name}({signature})", output]);
            var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
            var pc = callPcs[name];
            var tailLinks = DirectLinks(source, 1).Where(call => call.Method == 0).ToArray();
            if (tailLinks.Length != 1 || tailLinks[0].Pc != pc || !IsDecodedMethod(source, 0))
                throw new InvalidOperationException("Missing emitted tail transfer: " + name);
            var argument = byref ? ".reference (.address ⟨0, 0⟩)" : ".scalar (.i32 42)";
            var result = name switch
            {
                "Forward" => ".ok [.scalar (.i32 43)]",
                "ForwardReference" => ".ok [.scalar (.i32 42)]",
                "ForwardVoid" => ".ok []",
                _ => null
            };
            var proof = Path.Combine(root, "Tail-" + name + ".lean");
            File.WriteAllText(proof, $$"""
                {{source}}

                example : Extracted.method0.code[{{pc - 1}}]? = some .nop :=
                  Extracted.method0_instruction{{pc - 1}}
                example : Extracted.method0.code[{{pc}}]? =
                    ((Extracted.method0Closed.code[{{pc}}]?).bind fun raw =>
                      match raw.operand with
                      | .call site => some (.call site.method { tail := true })
                      | _ => none) := by
                  rw [Extracted.method0_instruction{{pc}}] <;> rfl
                example : Extracted.method0.code[{{pc + 1}}]? = some .ret :=
                  Extracted.method0_instruction{{pc + 1}}

                private def tailMemory : CIL.Safety.Memory := {
                  allocations := fun identity => if identity == 0 then
                    some ⟨.callerStack, ⟨4, 1, []⟩, true, []⟩ else none
                  cells := fun _ offset => ⟨if offset == 0 then 42 else 0, true⟩
                  views := [⟨0, 0, 4, true, true⟩]
                  nextIdentity := 1 }
                """);
            if (result is not null)
                File.AppendAllText(proof, $$"""

                    theorem compiled_tail_result :
                        (CIL.Safety.invoke Extracted.program 32 0 [{{argument}}] tailMemory).map Prod.snd =
                          {{result}} := rfl
                    #print axioms compiled_tail_result
                    """);
            else
            {
                var fault = name == "ForwardThrow" ? ".thrown .invalidOperation" :
                    ".memory .expiredLifetime (.address ⟨1, 0⟩) 0";
                File.AppendAllText(proof, $$"""

                    theorem compiled_tail_fault :
                        (match CIL.Safety.invoke Extracted.program 32 0 [{{argument}}] tailMemory with
                          | .error fault => some fault.fault | .ok _ => none) = some ({{fault}}) := rfl
                    #print axioms compiled_tail_fault
                    """);
            }
            if (name == "ForwardVoid")
                File.AppendAllText(proof, """

                    theorem compiled_tail_store :
                        (CIL.Safety.invoke Extracted.program 32 0
                          [.reference (.address ⟨0, 0⟩)] tailMemory).map (fun result => result.1.cells 0 0) =
                            .ok ⟨7, true⟩ := rfl
                    #print axioms compiled_tail_store
                    """);
            evidence.Add(proof, "PASS compiled tail transfer and lifetime: " + name);
            if (name != "Forward") continue;
            const string withoutTail = "fun op => match op with | .call target _ => .call target {} | _ => op";
            foreach (var (mutation, changed, markers) in new[]
            {
                ("dropped", ForgeDecodedInstruction(source, 0, pc, withoutTail),
                    new[] { "Extraction.FeatureFlowValid", FeatureObligation(0) }),
                ("prefix", ForgeFeatureCode(source, 0,
                    $$"""modify {{pc - 1}} (fun raw => { raw with opcode := 0 })"""),
                    ["Extraction.FeatureFlowValid", FeatureObligation(0)]),
                ("target", ForgeLink(source, 0, pc, ".direct 0"), ["Extraction.ManagedCallsValid"])
            })
            {
                var forged = Path.Combine(root, "Forged-tail-" + mutation + ".lean");
                File.WriteAllText(forged, changed);
                rejected.Add(forged, "PASS tail certificate rejection: " + mutation, markers);
            }
        }
        var excludedDll = Path.Combine(root, "TailExcluded.dll");
        using (var module = ModuleDefinition.ReadModule(assembly))
        {
            var method = module.GetType("Examples.TailCalls").Methods.Single(method => method.Name == "Excluded");
            var call = method.Body.Instructions.Single(instruction =>
                instruction.Operand is MethodReference { Name: "Increment" });
            method.Body.GetILProcessor().InsertBefore(call, Instruction.Create(OpCodes.Tail));
            var signature = new CallSite(module.TypeSystem.Int32);
            signature.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
            call.OpCode = OpCodes.Calli;
            call.Operand = signature;
            module.Write(excludedDll);
        }
        var excludedOutput = Path.Combine(root, "Tail-Excluded");
        Run(["dotnet", ExtractorPath, "extract", excludedDll, "TailCalls::Excluded(System.Int32)", excludedOutput]);
        var excludedProof = Path.Combine(root, "Tail-Excluded.lean");
        File.WriteAllText(excludedProof, File.ReadAllText(Path.Combine(excludedOutput, "Extracted.lean")) + """

            theorem excluded_indirect_tail :
                (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i32 42)]
                  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                    views := [], nextIdentity := 0 }).map Prod.snd =
                  .ok [.scalar (.i32 42)] := by cil_kernel_rfl
            #print axioms excluded_indirect_tail
            """);
        evidence.Add(excludedProof, "PASS profile-excluded indirect tail");
        foreach (var mutation in new[] { "branch", "dead-branch", "return", "missing-pointer", "stack", "type" })
        {
            var changed = Path.Combine(root, "Tail-Rejected-" + mutation + ".dll");
            using (var module = ModuleDefinition.ReadModule(dll))
            {
                var method = module.GetType("Examples.TailCalls").Methods.Single(method => method.Name == "Forward");
                var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Tail);
                var call = prefix.Next;
                var processor = method.Body.GetILProcessor();
                if (mutation == "branch") processor.InsertBefore(prefix, Instruction.Create(OpCodes.Br, call));
                // An unreachable branch after the final return still may not enter the tail call.
                else if (mutation == "dead-branch") processor.Append(Instruction.Create(OpCodes.Br, call));
                else if (mutation == "return") processor.InsertAfter(call, Instruction.Create(OpCodes.Nop));
                else if (mutation == "stack")
                    processor.InsertBefore(method.Body.Instructions[0], Instruction.Create(OpCodes.Ldc_I4_0));
                else if (mutation == "type") ((MethodReference)call.Operand).ReturnType = module.TypeSystem.UInt32;
                else
                {
                    var signature = new CallSite(module.TypeSystem.Int32);
                    signature.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
                    call.OpCode = OpCodes.Calli;
                    call.Operand = signature;
                }
                module.Write(changed);
            }
            var result = Execute(["dotnet", ExtractorPath, "extract", changed,
                "TailCalls::Forward(System.Int32)", Path.Combine(root, "Tail-Rejected-" + mutation)]);
            var marker = mutation switch
            {
                "branch" or "dead-branch" => "Branch enters the instruction after a prefix",
                "missing-pointer" => "Invalid evaluation stack during reachability",
                "stack" => "Tail call requires exactly its arguments",
                _ => "Unsupported tail prefix"
            };
            if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
                throw new InvalidOperationException("Incorrect tail rejection: " + mutation + "\n" + result.Output);
            Console.WriteLine("PASS tail extraction rejection: " + mutation);
        }
    }
}
