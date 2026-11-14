using Mono.Cecil;
using Mono.Cecil.Cil;

partial class Program
{
    /// <summary>Checks outline recognition without elaborating author-supplied proof obligations.</summary>
    static void CheckReferenceAddOutlines(string root)
    {
        foreach (var variant in new[] { "Callee", "Direct", "Commuted", "Native", "Unsafe32", "Unsafe64" })
        {
            var directory = Path.Combine(root, "Outlines", variant);
            Directory.CreateDirectory(directory);
            var assembly = Path.Combine(directory, "Examples.dll");
            using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
            {
                AddReferenceOutlineLoop(module, variant);
                module.Write(assembly);
            }
            var extraction = Path.Combine(directory, "Extracted");
            var word = variant == "Unsafe64" ? "System.UInt64" : "System.UInt32";
            Run(["dotnet", ExtractorPath, "extract", assembly,
                $"Loops::ReferenceOutline({word}&,{word},System.Int32)", extraction]);
            var proof = Path.Combine(directory, "Proof.lean");
            File.Delete(proof);
            Run(["dotnet", ExtractorPath, "new-proof", extraction, proof]);
            var source = File.ReadAllText(proof);
            if (variant is "Commuted" or "Native")
                RequireOutlineText(source,
                    "a reference addition other than a reference argument followed by a 32-bit index " +
                    "before a call in the iteration", variant);
            else if (variant == "Direct")
                RequireOutlineText(source,
                    "a store through `Unsafe.Add` of a value the outline cannot name at the element's width", variant);
            else
            {
                RequireOutlineText(source, "import CIL.Safety.LoopObligations", variant);
                RequireOutlineText(source, "add_int_element", variant);
                var stride = variant == "Callee" ? 1 : variant == "Unsafe32" ? 4 : 8;
                RequireOutlineText(source, $"destination.element {stride} ", variant);
                if (source.Contains("-- not outlined:", StringComparison.Ordinal))
                    throw new InvalidOperationException($"{variant} outline stopped:\n{source}");
            }
            Console.WriteLine($"PASS reference-add outline recognition: {variant} (text only)");
        }
    }

    /// <summary>Builds a counter loop with reference addition followed by a word store.</summary>
    static void AddReferenceOutlineLoop(ModuleDefinition module, string variant)
    {
        var type = module.GetType("Examples.Loops");
        var word = variant == "Unsafe64" ? module.TypeSystem.UInt64 : module.TypeSystem.UInt32;
        var attributes = Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static;
        var store = new MethodDefinition("StoreWord", attributes, module.TypeSystem.Void);
        store.Parameters.Add(new ParameterDefinition("slot", ParameterAttributes.None, new ByReferenceType(word)));
        store.Parameters.Add(new ParameterDefinition("value", ParameterAttributes.None, word));
        type.Methods.Add(store);
        var storeBody = store.Body.GetILProcessor();
        storeBody.Emit(OpCodes.Ldarg_0);
        storeBody.Emit(OpCodes.Ldarg_1);
        storeBody.Emit(variant == "Unsafe64" ? OpCodes.Stind_I8 : OpCodes.Stind_I4);
        storeBody.Emit(OpCodes.Ret);
        var method = new MethodDefinition("ReferenceOutline", attributes, module.TypeSystem.Void);
        method.Parameters.Add(new ParameterDefinition("destination", ParameterAttributes.None,
            new ByReferenceType(word)));
        method.Parameters.Add(new ParameterDefinition("value", ParameterAttributes.None, word));
        method.Parameters.Add(new ParameterDefinition("count", ParameterAttributes.None, module.TypeSystem.Int32));
        type.Methods.Add(method);
        method.Body.InitLocals = true;
        method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
        var body = method.Body.GetILProcessor();
        var start = Instruction.Create(variant == "Commuted" ? OpCodes.Ldloc_0 : OpCodes.Ldarg_0);
        var condition = Instruction.Create(OpCodes.Ldloc_0);
        body.Emit(OpCodes.Ldc_I4_0);
        body.Emit(OpCodes.Stloc_0);
        body.Emit(OpCodes.Br, condition);
        body.Append(start);
        body.Emit(variant == "Commuted" ? OpCodes.Ldarg_0 : OpCodes.Ldloc_0);
        if (variant == "Native") body.Emit(OpCodes.Conv_I);
        if (variant.StartsWith("Unsafe", StringComparison.Ordinal))
        {
            var original = (GenericInstanceMethod)type.Methods.Single(method => method.Name == "FillWords")
                .Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call).Operand;
            var add = new GenericInstanceMethod(original.ElementMethod);
            add.GenericArguments.Add(word);
            body.Emit(OpCodes.Call, add);
        }
        else body.Emit(OpCodes.Add);
        body.Emit(OpCodes.Ldarg_1);
        if (variant == "Direct") body.Emit(OpCodes.Stind_I4);
        else body.Emit(OpCodes.Call, store);
        body.Emit(OpCodes.Ldloc_0);
        body.Emit(OpCodes.Ldc_I4_1);
        body.Emit(OpCodes.Add);
        body.Emit(OpCodes.Stloc_0);
        body.Append(condition);
        body.Emit(OpCodes.Ldarg_2);
        body.Emit(OpCodes.Blt, start);
        body.Emit(OpCodes.Ret);
    }

    /// <summary>Requires a specific outline term or unsupported-shape diagnosis.</summary>
    static void RequireOutlineText(string source, string expected, string variant)
    {
        var unwrapped = System.Text.RegularExpressions.Regex.Replace(source, @"\r?\n\s*--\s*", " ");
        if (!unwrapped.Contains(expected, StringComparison.Ordinal))
            throw new InvalidOperationException($"{variant} outline lacks '{expected}':\n{source}");
    }
}

