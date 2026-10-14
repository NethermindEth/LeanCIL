#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil

using Mono.Cecil;
using Mono.Cecil.Cil;

if (args.Length != 3)
    throw new ArgumentException("input.dll output.dll mutation");

// Mutate an independent assembly without executing it.
using var module = ModuleDefinition.ReadModule(args[0]);
var owner = module.GetType("Examples.Arithmetic");
var add = owner.Methods.Single(m => m.Name == "Add");

// Each case creates one targeted invalid input or a static-data fixture.
switch (args[2])
{
    case "synchronized":
        add.ImplAttributes |= MethodImplAttributes.Synchronized;
        break;

    case "nested-byref":
        add.Parameters[0].ParameterType = new ByReferenceType(new ByReferenceType(module.TypeSystem.UInt64));
        break;

    case "framework":
        module.Assembly.CustomAttributes.Single(a => a.AttributeType.Name == "TargetFrameworkAttribute")
            .ConstructorArguments[0] = new CustomAttributeArgument(module.TypeSystem.String, ".NETCoreApp,Version=v9.0");
        break;

    case "return-overload":
        var overload = new MethodDefinition("Add", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.UInt32);
        overload.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt64));
        overload.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt64));
        overload.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_0));
        overload.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        owner.Methods.Add(overload);
        break;

    case "version":
        module.Assembly.Name.Version = new Version(2, 0, 0, 0);
        break;

    case "identity":
        module.Assembly.Name.Name = "Unexpected";
        break;

    case "field":
        module.GetType("Examples.Packet").Fields.Single(f => f.Name == "Tag").Offset = 12;
        break;

    case "local":
        add.Body.Variables.Add(new VariableDefinition(module.TypeSystem.String));
        break;

    case "cycle":
        add.Body.Instructions[0].OpCode = OpCodes.Br;
        add.Body.Instructions[0].Operand = add.Body.Instructions[0];
        break;

    case "initializer":
        var cctor = new MethodDefinition(".cctor", MethodAttributes.Static | MethodAttributes.Private |
            MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        cctor.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        owner.Methods.Add(cctor);
        break;

    case "runtime-scope":
        module.AssemblyReferences.Single(a => a.Name == "System.Runtime").PublicKeyToken = new byte[8];
        break;

    case "static-data":
        var layout = new TypeDefinition("", "Blob", TypeAttributes.Sealed | TypeAttributes.ExplicitLayout,
            new TypeReference("System", "ValueType", module, module.AssemblyReferences.Single(a => a.Name == "System.Runtime")))
            { ClassSize = 8, PackingSize = 1 };
        module.Types.Add(layout);
        var data = new FieldDefinition("Data", FieldAttributes.Static | FieldAttributes.InitOnly | FieldAttributes.HasFieldRVA, layout)
            { InitialValue = [42, 0, 0, 0, 0, 0, 0, 0] };
        owner.Fields.Add(data);
        add.Body.Instructions.Clear();
        add.Body.Instructions.Add(Instruction.Create(OpCodes.Ldsflda, data));
        add.Body.Instructions.Add(Instruction.Create(OpCodes.Ldind_I8));
        add.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        break;

    default:
        throw new ArgumentException("Unknown mutation");
}

module.Write(args[1]);
