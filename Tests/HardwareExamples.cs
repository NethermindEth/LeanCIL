using Mono.Cecil;
using Mono.Cecil.Cil;

// These single-call bodies exercise the MemberRefs even when the host CPU cannot run the instruction.
internal static class HardwareExamples
{
    internal sealed record Example(string Selector, string Name, string Profile, string Model, bool NeedsFeature);

    internal static List<Example> Write(string assembly, string output, string x86, string arm)
    {
        using var module = ModuleDefinition.ReadModule(assembly);
        var intrinsics = module.AssemblyReferences.Single(row => row.Name == "System.Runtime.Intrinsics");
        // The fixture retains the target framework's assembly references and contains just the call wrappers.
        while (module.Types.Count > 1) module.Types.RemoveAt(module.Types.Count - 1);
        var wrapper = new TypeDefinition("Examples", "HardwareMembers",
            TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, module.TypeSystem.Object);
        module.Types.Add(wrapper);
        var examples = new List<Example>();
        var slots = new HashSet<(string Owner, string Name)>();
        var types = module.TypeSystem;
        var uint64 = types.UInt64;
        var int64 = types.Int64;
        var uint32 = types.UInt32;
        var int32 = types.Int32;
        var byteType = types.Byte;
        var boolean = types.Boolean;
        var single = types.Single;
        var doubleType = types.Double;

        TypeReference Owner(string name)
        {
            var nested = name.LastIndexOf('/');
            if (nested >= 0)
                return new TypeReference("", name[(nested + 1)..], module, intrinsics)
                    { DeclaringType = Owner(name[..nested]) };
            var full = $"System.Runtime.Intrinsics.{name}";
            var dot = full.LastIndexOf('.');
            return new TypeReference(full[..dot], full[(dot + 1)..], module, intrinsics);
        }

        static GenericInstanceType Apply(TypeReference head, params TypeReference[] arguments)
        {
            var applied = new GenericInstanceType(head);
            foreach (var argument in arguments) applied.GenericArguments.Add(argument);
            return applied;
        }

        var heads = new Dictionary<int, TypeReference>();
        foreach (var width in new[] { 128, 256, 512 })
        {
            var head = Owner($"Vector{width}`1");
            head.IsValueType = true;
            head.GenericParameters.Add(new GenericParameter("T", head));
            heads.Add(width, head);
        }
        TypeReference Vector(int width, TypeReference element) => Apply(heads[width], element);
        var tuple = new TypeReference("System", "ValueTuple`2", module, types.CoreLibrary, true);
        var pair = Apply(tuple, uint64, uint64);

        TypeReference Closed(TypeReference type) => type switch
        {
            GenericParameter => uint64,
            GenericInstanceType generic =>
                Apply(generic.ElementType, generic.GenericArguments.Select(Closed).ToArray()),
            _ => type
        };

        void Emit(MethodReference call, string model, string profile, bool feature)
        {
            if (!slots.Add((call.DeclaringType.GetElementType().FullName, call.Name)))
                throw new InvalidDataException($"Repeated hardware slot in {call.FullName}");
            var name = $"Member{examples.Count}";
            var method = new MethodDefinition(name, MethodAttributes.Static | MethodAttributes.Public,
                Closed(call.ReturnType));
            wrapper.Methods.Add(method);
            var il = method.Body.GetILProcessor();
            foreach (var parameter in call.Parameters)
            {
                var argument = new ParameterDefinition(Closed(parameter.ParameterType));
                method.Parameters.Add(argument);
                il.Emit(OpCodes.Ldarg, argument);
            }
            il.Emit(OpCodes.Call, call);
            il.Emit(OpCodes.Ret);
            examples.Add(new(method.FullName, name, profile, $".intrinsic ({model}) {call.Parameters.Count}", feature));
        }

        void Machine(string owner, string name, string model, TypeReference result, params TypeReference[] parameters)
        {
            var method = new MethodReference(name, result, Owner(owner));
            foreach (var parameter in parameters) method.Parameters.Add(new ParameterDefinition(parameter));
            Emit(method, model, owner.StartsWith("Arm.", StringComparison.Ordinal) ? arm : x86, true);
        }

        Machine("X86.Avx2", "And", ".avx2 .band", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "Or", ".avx2 .bor", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "Xor", ".avx2 .bxor", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "AndNot", ".avx2 .andNot", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "ShiftLeftLogical", ".avx2 .shl64Count", Vector(256, uint64),
            Vector(256, uint64), Vector(128, uint64));
        Machine("X86.Avx2", "ShiftRightLogical", ".avx2 .shr64Count", Vector(256, uint64),
            Vector(256, uint64), Vector(128, uint64));
        Machine("X86.Avx512F", "CompareLessThan", ".avx512 .ltu512", Vector(512, uint64),
            Vector(512, uint64), Vector(512, uint64));
        Machine("X86.Avx512F", "CompareGreaterThan", ".avx512 .gtu512", Vector(512, uint64),
            Vector(512, uint64), Vector(512, uint64));
        Machine("X86.Avx512DQ", "MoveMask", ".avx512DQ .moveMask512", int32,
            Vector(512, uint64));
        Machine("Arm.AdvSimd", "ReverseElement8", ".advSimd .reverseElement8", Vector(128, uint64),
            Vector(128, uint64));
        Machine("X86.Sse2", "Multiply", ".sse .multiplyEven32", Vector(128, uint64),
            Vector(128, uint32), Vector(128, uint32));
        Machine("X86.Ssse3", "Shuffle", ".sse .shuffleBytes", Vector(128, byteType),
            Vector(128, byteType), Vector(128, byteType));
        Machine("X86.Avx2", "Shuffle", ".avx2 .shuffleBytes", Vector(256, byteType),
            Vector(256, byteType), Vector(256, byteType));
        Machine("X86.Aes", "Encrypt", ".aes .encrypt", Vector(128, byteType),
            Vector(128, byteType), Vector(128, byteType));
        Machine("Arm.Aes", "Encrypt", ".armAes .encrypt", Vector(128, byteType),
            Vector(128, byteType), Vector(128, byteType));
        Machine("Arm.Aes", "MixColumns", ".armAes .mixColumns", Vector(128, byteType),
            Vector(128, byteType));
        Machine("X86.Avx512F/VL", "PermuteVar4x64x2", ".avx512 .permuteVar4x64x2", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64), Vector(256, uint64));
        Machine("Arm.AdvSimd", "ExtractVector128", ".advSimd .extract64", Vector(128, uint64),
            Vector(128, uint64), Vector(128, uint64), byteType);
        Machine("X86.Sse2", "ShiftLeftLogical128BitLane", ".sse .shiftLeftBytes", Vector(128, uint64),
            Vector(128, uint64), byteType);
        Machine("X86.Ssse3", "AlignRight", ".sse .alignBytes", Vector(128, byteType),
            Vector(128, byteType), Vector(128, byteType), byteType);
        Machine("X86.Avx2", "Permute4x64", ".avx2 .permute4x64", Vector(256, uint64),
            Vector(256, uint64), byteType);
        Machine("X86.Avx2", "Blend", ".avx2 .blend32", Vector(256, uint32),
            Vector(256, uint32), Vector(256, uint32), byteType);
        Machine("X86.Avx2", "Add", ".avx2 .add64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "CompareEqual", ".avx2 .eq64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx2", "CompareGreaterThan", ".avx2 .signedgt64", Vector(256, int64),
            Vector(256, int64), Vector(256, int64));
        Machine("X86.Avx2", "Multiply", ".avx2 .multiplyEven32", Vector(256, uint64),
            Vector(256, uint32), Vector(256, uint32));
        Machine("X86.Avx512F/VL", "AlignRight64", ".avx512 .alignRight64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64), byteType);
        Machine("X86.Avx512F/VL", "TernaryLogic", ".avx512 .ternaryLogic", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64), Vector(256, uint64), byteType);
        Machine("X86.Avx512F/VL", "CompareLessThan", ".avx512 .ltu64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx512F/VL", "CompareGreaterThan", ".avx512 .gtu64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx512F/VL", "CompareGreaterThanOrEqual", ".avx512 .geu64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx512DQ/VL", "MultiplyLow", ".avx512DQ .mul64", Vector(256, uint64),
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Avx", "MoveMask", ".avx .moveMask64", int32,
            Vector(256, doubleType));
        Machine("X86.Avx", "Blend", ".avx .blend32", Vector(256, single),
            Vector(256, single), Vector(256, single), byteType);
        Machine("X86.Avx", "TestZ", ".avx .testZ64", boolean,
            Vector(256, uint64), Vector(256, uint64));
        Machine("X86.Bmi1", "BitFieldExtract", ".bmi1 .bextr32", uint32,
            uint32, byteType, byteType);
        Machine("X86.Bmi2/X64", "MultiplyNoFlags", ".bmi2 .multiplyHigh64", uint64,
            uint64, uint64);
        Machine("Arm.ArmBase/Arm64", "MultiplyHigh", ".armBase64 .multiplyHigh64", uint64,
            uint64, uint64);
        Machine("X86.X86Base/X64", "DivRem", ".x86Base .divRem64", pair,
            uint64, uint64, uint64);

        foreach (var width in new[] { 128, 256, 512 })
        {
            void Portable(string name, string operation, bool ownerBinder, bool genericMethod,
                Func<TypeReference, TypeReference> result, params Func<TypeReference, TypeReference>[] parameters)
            {
                var owner = ownerBinder ? Vector(width, uint64) : Owner($"Vector{width}");
                var method = new MethodReference(name, types.Void, owner);
                TypeReference binder = uint64;
                if (ownerBinder) binder = heads[width].GenericParameters[0];
                if (genericMethod)
                {
                    binder = new GenericParameter("T", method);
                    method.GenericParameters.Add((GenericParameter)binder);
                    method.CallingConvention = MethodCallingConvention.Generic;
                }
                method.ReturnType = result(binder);
                foreach (var parameter in parameters) method.Parameters.Add(new ParameterDefinition(parameter(binder)));
                MethodReference call = method;
                if (genericMethod)
                {
                    var instance = new GenericInstanceMethod(method);
                    instance.GenericArguments.Add(uint64);
                    call = instance;
                }
                Emit(call, $".vector (.{operation} {width})", "scalar", false);
            }
            TypeReference V(TypeReference element) => Vector(width, element);
            foreach (var (name, operation) in new[]
            {
                ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor")
            })
                Portable(name, operation, true, false, V, V, V);
            Portable("op_OnesComplement", "bnot", true, false, V, V);
            Portable("get_Zero", "zero", true, false, V);
            Portable("get_AllBitsSet", "ones", true, false, V);
            Portable("EqualsAll", "equalsAll", false, true, _ => boolean, V, V);
            if (width == 512) continue;
            Portable("op_Addition", "add64", true, false, V, V, V);
            Portable("op_Subtraction", "sub64", true, false, V, V, V);
            Portable("Equals", "eq64", false, true, V, V, V);
            Portable("LessThan", "ltu64", false, true, V, V, V);
            Portable("Sum", "sum64", false, true, element => element, V);
            Portable("ExtractMostSignificantBits", "extractMSB64", false, true, _ => uint32, V);
            Portable("ShiftRightArithmetic", "ashr64", false, false, _ => V(int64), _ => V(int64), _ => int32);
            Portable("CreateScalar", "createScalar64", false, false, _ => V(uint64), _ => uint64);
            foreach (var target in new[] { byteType, doubleType, int32, int64, single, uint32, uint64 })
                Portable($"As{target.Name}", "reinterpret", false, true, _ => V(target), V);
        }
        if (examples.Count != 90) throw new InvalidDataException($"Expected 90 hardware slots, found {examples.Count}");
        module.Write(output);
        return examples;
    }
}
