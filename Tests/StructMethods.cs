#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/StructMethods");
Directory.CreateDirectory(root);
var queue = new GeneratedQueue(verification, assembly);
var cases = 0;

void Compare(string dll, string name, string suffix = "")
{
    var method = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.StructMethods")!.GetMethod(name)!;
    var output = Path.Combine(root, name + suffix);
    Directory.CreateDirectory(output);
    var narrow = name == "Narrow";
    var width = narrow ? 32 : 64;
    var claims = new List<string>();
    foreach (var bits in new ulong[] { 0, 1, 127, 128, 254, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue })
    {
        object value = narrow ? (object)unchecked((byte)bits) : bits;
        var expected = method.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i{width} {value})] CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i{width} {expected})]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    queue.Add(new($"StructMethods::{name}({(narrow ? "byte" : "ulong")})", proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {name}{suffix}: {claims.Count} runtime comparisons");
    });
}

// Mutating this, copying values, multiple argument indices and narrow parameter homes.
// `Initialized` calls an `init` accessor, whose `void modreq(IsExternalInit)` return pushes nothing.
foreach (var name in new[] { "Mutate", "ByValue", "Arguments", "Replace", "Narrow", "ConstructLocal", "Initialized" })
    Compare(assembly, name);

// The accessor itself is an entry: it stores its argument through `this` and returns no value.
const string initSelector = "InitCounter::set_Value(ulong)";
var initOutput = Path.Combine(root, "InitAccessor");
Directory.CreateDirectory(initOutput);
var initProof = Path.Combine(initOutput, "InitProof.lean");
File.WriteAllText(initProof, """
    import Extracted
    import CIL.Safety.Execution
    namespace ExampleProof
    private def counterMemory : CIL.Safety.Memory := {
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨8, 1, []⟩, true, []⟩ else none
      cells := fun _ _ => ⟨0, true⟩
      views := [⟨0, 0, 8, true, true⟩]
      nextIdentity := 1 }
    theorem init_stores :
        (CIL.Safety.invoke Extracted.program 32 0 [.reference (.address ⟨0, 0⟩), .scalar (.i64 0x0102)]
          counterMemory).map (fun result => (result.2, (result.1.cells 0 0).bits, (result.1.cells 0 1).bits)) =
          .ok ([], 2, 1) := rfl
    #print axioms init_stores
    end ExampleProof
    """);
queue.Add(new(initSelector, initProof, initOutput, "ExampleProof.init_stores"),
    () => Console.WriteLine("PASS init accessor entry"));

// Exercise explicit full/short argument operands, including Cecil's implicit this parameter.
foreach (var shortForm in new[] { false, true })
{
    var output = Path.Combine(root, "Encoding-" + shortForm);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Counter").Methods.Single(m => m.Name == "Mix");
        foreach (var instruction in method.Body.Instructions)
        {
            var index = instruction.OpCode.Code switch
            {
                Code.Ldarg_0 => 0, Code.Ldarg_1 => 1, Code.Ldarg_2 => 2, Code.Ldarg_3 => 3,
                Code.Ldarg or Code.Ldarg_S => ((ParameterDefinition)instruction.Operand).Index + 1,
                _ => -1
            };
            if (index < 0) continue;
            instruction.OpCode = shortForm ? OpCodes.Ldarg_S : OpCodes.Ldarg;
            instruction.Operand = index == 0 ? method.Body.ThisParameter : method.Parameters[index - 1];
        }
        module.Write(dll);
    }
    Compare(dll, "Arguments", "-" + shortForm);
}

// Libraries for older frameworks declare their own IsExternalInit; C# binds the marker by full name
// from any assembly, so an accessor marked by one runs exactly as with System.Runtime's.
foreach (var scope in new[] { "local-marker", "versioned-marker" })
{
    var output = Path.Combine(root, "Init-" + scope);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var setter = module.GetType("Examples.InitCounter").Methods.Single(method => method.Name == "set_Value");
        var marker = (RequiredModifierType)setter.ReturnType;
        var runtime = (AssemblyNameReference)marker.ModifierType.Scope;
        TypeReference replacement;
        if (scope == "local-marker")
        {
            var local = new TypeDefinition(marker.ModifierType.Namespace, marker.ModifierType.Name,
                Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
            module.Types.Add(local);
            replacement = local;
        }
        else
            replacement = new TypeReference(marker.ModifierType.Namespace, marker.ModifierType.Name, module,
                new AssemblyNameReference(runtime.Name, new Version(9, 0, 0, 0))
                    { PublicKeyToken = runtime.PublicKeyToken });
        setter.ReturnType = new RequiredModifierType(replacement, marker.ElementType);
        module.Write(dll);
    }
    Compare(dll, "Initialized", "-" + scope);
}

queue.Flush();

var contract = At("Examples/Proofs/InstanceWriteRead.lean");
verification.Verify(assembly, "Examples", "Counter::WriteRead(ulong)", contract, Path.Combine(root, "UniversalWriteRead"));
var wrongOutput = Path.Combine(root, "WrongWriteRead");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Counter::WrongWriteRead(ulong)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect instance mutation accepted");

// Invalid call metadata must not be mistaken for an instance or static invocation.
foreach (var mutation in new[] { "static-call", "explicit-this", "class", "constructor-return" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.Counter");
        var entry = module.GetType("Examples.StructMethods").Methods.Single(m => m.Name == "ConstructLocal");
        var constructor = type.Methods.Single(m => m.Name == ".ctor");
        switch (mutation)
        {
            case "static-call":
                var call = (MethodReference)entry.Body.Instructions.First(i => i.OpCode.Code == Code.Call).Operand;
                call.HasThis = false;
                break;
            case "explicit-this": constructor.ExplicitThis = true; break;
            case "class": type.BaseType = module.TypeSystem.Object; break;
            case "constructor-return": constructor.ReturnType = module.TypeSystem.Int32; break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "StructMethods::ConstructLocal(ulong)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Invalid instance metadata accepted: {mutation}\n{result.Output}");
}

// Only modreq(System.Runtime.CompilerServices.IsExternalInit) directly on System.Void is admitted;
// every other modifier, including a same-named marker in another namespace, is rejected by name,
// both as an entry and behind the call that reaches it.
const string returnRejection = "except modreq(System.Runtime.CompilerServices.IsExternalInit) directly on System.Void";
const string parameterRejection = "except System.Runtime's modreq(InAttribute) directly on a by-reference parameter";
static MethodDefinition Accessor(ModuleDefinition module, string name) =>
    module.GetType("Examples.InitCounter").Methods.Single(method => method.Name == name);
foreach (var mutation in new[] { "other-modreq", "modopt", "non-void", "parameter", "other-namespace" })
{
    var output = Path.Combine(root, "Reject-init-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector, modified;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var setter = Accessor(module, "set_Value");
        var marker = (RequiredModifierType)setter.ReturnType;
        var runtime = (AssemblyNameReference)marker.ModifierType.Scope;
        TypeReference Modifier(string name, IMetadataScope scope) =>
            new("System.Runtime.CompilerServices", name, module, scope);
        TypeReference ForeignMarker()
        {
            var local = new TypeDefinition("Examples", "IsExternalInit",
                Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
            module.Types.Add(local);
            return local;
        }
        var target = mutation == "non-void" ? Accessor(module, "get_Value") : setter;
        switch (mutation)
        {
            case "other-modreq":
                setter.ReturnType = new RequiredModifierType(Modifier("IsVolatile", runtime), marker.ElementType);
                break;
            case "modopt": setter.ReturnType = new OptionalModifierType(marker.ModifierType, marker.ElementType); break;
            case "non-void":
                target.ReturnType = new RequiredModifierType(marker.ModifierType, target.ReturnType);
                break;
            case "parameter":
                setter.ReturnType = marker.ElementType;
                setter.Parameters[0].ParameterType =
                    new RequiredModifierType(marker.ModifierType, setter.Parameters[0].ParameterType);
                break;
            default: setter.ReturnType = new RequiredModifierType(ForeignMarker(), marker.ElementType); break;
        }
        modified = mutation == "parameter" ? setter.Parameters[0].ParameterType.FullName : target.ReturnType.FullName;
        selector = target.FullName;
        module.Write(dll);
    }
    var entry = Execute(["dotnet", ExtractorPath, "extract", dll, selector, Path.Combine(output, "entry")]);
    if (entry.Code == 0 || !entry.Output.Contains(mutation == "parameter" ? parameterRejection : returnRejection,
            StringComparison.Ordinal) || !entry.Output.Contains(modified, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect init modifier rejection: {mutation}\n{entry.Output}");
    var caller = Execute(Extract("extract", dll, "Examples", "StructMethods::Initialized(ulong)",
        Path.Combine(output, "caller")));
    if (caller.Code == 0 || !caller.Output.Contains(modified, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect init modifier caller rejection: {mutation}\n{caller.Output}");
    Console.WriteLine("PASS init modifier rejection: " + mutation);
}

// The modifier stays in method identity: selectors, the recorded entry and the Lean signature all
// tell the accessor from a plain void setter, and a modifier-only twin of it is rejected.
var plainOutput = Path.Combine(root, "Init-plain");
Directory.CreateDirectory(plainOutput);
var plainDll = Path.Combine(plainOutput, "Examples.dll");
var twinDll = Path.Combine(plainOutput, "Twin.dll");
string initName, plainName;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var setter = Accessor(module, "set_Value");
    initName = setter.FullName;
    setter.ReturnType = ((RequiredModifierType)setter.ReturnType).ElementType;
    plainName = setter.FullName;
    module.Write(plainDll);
}
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var setter = Accessor(module, "set_Value");
    var copy = new MethodDefinition(setter.Name, setter.Attributes,
        ((RequiredModifierType)setter.ReturnType).ElementType) { HasThis = true };
    copy.Parameters.Add(new ParameterDefinition(setter.Parameters[0].ParameterType));
    if (setter.Body.Instructions.Any(instruction =>
        instruction.Operand is Instruction or Instruction[] or ParameterDefinition))
        throw new InvalidOperationException("Init twin requires a straight-line body with short argument loads");
    foreach (var instruction in setter.Body.Instructions)
    {
        var cloned = Instruction.Create(OpCodes.Nop);
        cloned.OpCode = instruction.OpCode;
        cloned.Operand = instruction.Operand;
        copy.Body.Instructions.Add(cloned);
    }
    setter.DeclaringType.Methods.Add(copy);
    module.Write(twinDll);
}
string Entry(string dll, string selector, string name)
{
    var output = Path.Combine(plainOutput, name);
    Run(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    var entry = System.Text.Json.JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json")))
        .RootElement.GetProperty("entry").GetString()!;
    var signature = "Signature : String := " + System.Text.Json.JsonSerializer.Serialize(entry);
    if (!File.ReadAllText(Path.Combine(output, "Extracted.lean")).Contains(signature, StringComparison.Ordinal))
        throw new InvalidOperationException("Extracted signature differs from the recorded entry: " + entry);
    return entry;
}
if (initName == plainName || Entry(assembly, initName, "init") != initName ||
    Entry(plainDll, plainName, "plain") != plainName)
    throw new InvalidOperationException("Init accessor identity lost its modifier");
foreach (var (dll, selector) in new[] { (assembly, "void " + initSelector), (plainDll, initName) })
{
    var mismatch = Execute(["dotnet", ExtractorPath, "extract", dll, selector, Path.Combine(plainOutput, "mismatch")]);
    if (mismatch.Code == 0 || !mismatch.Output.Contains("No method matches selector", StringComparison.Ordinal))
        throw new InvalidOperationException($"Selector ignored the init modifier: {selector}\n{mismatch.Output}");
}
foreach (var selector in new[] { initName, plainName })
{
    var twin = Execute(["dotnet", ExtractorPath, "extract", twinDll, selector, Path.Combine(plainOutput, "twin")]);
    if (twin.Code == 0 || !twin.Output.Contains("Ambiguous modifier-only twin", StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect init twin rejection: {selector}\n{twin.Output}");
}
Console.WriteLine("PASS init modifier identity, selector distinctness and twin rejection");

Console.WriteLine($"PASS {cases} instance-call runtime comparisons, universal mutation proof and metadata rejections");
