#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ContractVariants.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Strings as opaque object references: proofs that they are passed, returned, stored and loaded as literals, and the
// named rejection of every operation that would read through one, address its root or load an unencodable literal.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Strings");
Directory.CreateDirectory(root);

foreach (var (source, entry) in new[]
{
    ("Examples/Proofs/StringValues.lean", "Strings::Pick(System.Boolean,System.String,System.String)"),
    ("Examples/Proofs/StringLabel.lean", "Strings::Relabel(Examples.Labelled,System.String)"),
    ("Examples/Proofs/StringLiterals.lean", "Strings::SameText()"),
    ("Examples/Proofs/StringDefault.lean", "Strings::OrNone(System.String)")
})
{
    var proof = Path.GetFileNameWithoutExtension(source);
    verification.Verify(assembly, "Examples", entry, At(source), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

// The compiled #US entry contains controls and both ends of the supplementary scalar range.
const string scalarText = "A\0\b\f\uFFFF\U00010000\U0010FFFFZ";
var unicode = Path.Combine(root, "Unicode");
Directory.CreateDirectory(unicode);
var changedAssembly = Path.Combine(unicode, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var load = module.GetType("Examples.Strings").Methods.Single(method => method.Name == "OrNone")
        .Body.Instructions.Single(site => site.OpCode.Code == Code.Ldstr);
    load.Operand = scalarText;
    module.Write(changedAssembly);
}
var wrongDirectory = Path.Combine(unicode, "Modified");
Directory.CreateDirectory(wrongDirectory);
var wrongAssembly = Path.Combine(wrongDirectory, "Examples.dll");
var image = File.ReadAllBytes(changedAssembly);
var payload = System.Text.Encoding.Unicode.GetBytes(scalarText);
var offset = image.AsSpan().IndexOf(payload);
if (offset < 0 || image.AsSpan().LastIndexOf(payload) != offset)
    throw new InvalidDataException("Expected a unique physical Unicode fixture literal");
// Change only the low surrogate of U+10000, giving U+10001 in the same #US entry.
var lowSurrogate = offset + (scalarText.IndexOf("\U00010000", StringComparison.Ordinal) + 1) * sizeof(char);
image[lowSurrogate]++;
File.WriteAllBytes(wrongAssembly, image);

foreach (var (dll, expected) in new[] { (changedAssembly, scalarText),
    (wrongAssembly, scalarText.Replace("\U00010000", "\U00010001", StringComparison.Ordinal)) })
{
    var strings = System.Reflection.Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Strings")!;
    if (!Equals(strings.GetMethod("OrNone")!.Invoke(null, [null]), expected))
        throw new InvalidOperationException("The CLR did not load the expected UTF-16 literal");
}
const string loadSelector = "Strings::OrNone(System.String)";
verification.VerifyContractVariant(changedAssembly, "Examples", loadSelector, Path.Combine(unicode, "Original"),
    wrongAssembly, loadSelector, Path.Combine(unicode, "Changed"), """
    private def text (point : Nat) :=
      String.ofList ([65, 0, 8, 12, 65535, point, 1114111, 90].map Char.ofNat)

    /-- Passing null returns the original literal's interned object and preserves caller memory. -/
    def originalLiteral : MethodContract Reference Reference where
      args _ := [.object .null]
      results found := [.object (.address found)]
      pre expected memory := memory.literals.lookup (text 65536) = some expected ∧
        formObject memory (.address expected) = .ok (.object (.address expected))
      footprint _ := []
      post expected before after found := after = before ∧ found = expected
    """, """
    theorem correctness : originalLiteral.Holds Extracted.program 0 := by
      intro expected memory ready
      obtain ⟨bound, formed⟩ := ready
      apply MethodContract.Holds.intro (c := originalLiteral) (input := expected) memory expected ?_
        (Confined.refl _ _) ⟨rfl, rfl⟩
      change ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
        .ok (memory, [.object (.address expected)])
      cil_checked_steps [formed]
      have atSite : Extracted.method0.code[4]? = some (.ldstr (text 65536)) := by decide +kernel
      apply Eq.trans (run_next (body := Extracted.method0) rfl atSite (by
        rw [step_ldstr_eq, literalObject_of_lookup bound, formed]
        rfl))
      cil_checked_steps [formed]
    """, """
    private def strings : Memory := { Memory.empty with
      allocations := fun id => if id < 2 then some {
        kind := .object ⟨.object CIL.Extraction.coreLibraryScope "System.String", []⟩
        layout := ⟨16, 8, []⟩ } else none
      nextIdentity := 2
      literals := [(text 65536, ⟨0, 0⟩), (text 65537, ⟨1, 0⟩)] }

    theorem correctness : originalLiteral.Refuted Extracted.program 0 := by
      apply MethodContract.Refuted.of_return (c := originalLiteral) (input := ⟨0, 0⟩)
        (initial := strings) (fuel := 8) (values := [.object (.address ⟨1, 0⟩)])
        (And.intro rfl rfl) rfl
      rintro ⟨_, found, encoded, _, rfl⟩
      revert encoded
      decide +kernel
    """, imports: "import CIL.Safety.SymbolicExecution");
Console.WriteLine("PASS exact UTF-16 literal binding and verified one-byte surrogate-pair counterexample");

foreach (var mutation in new[] { "read", "highSurrogate", "lowSurrogate", "argumentAddress", "localAddress", "byref", "modified" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expected, selector = "Strings::Pick(System.Boolean,System.String,System.String)";
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Strings").Methods.Single(candidate => candidate.Name == "Pick");
        var il = method.Body.GetILProcessor();
        var start = method.Body.Instructions[0];
        var text = module.TypeSystem.String;
        switch (mutation)
        {
            case "read":
                var empty = new MethodReference("IsNullOrEmpty", module.TypeSystem.Boolean, text);
                empty.Parameters.Add(new ParameterDefinition(text));
                il.InsertBefore(start, il.Create(OpCodes.Ldarg_1));
                il.InsertBefore(start, il.Create(OpCodes.Call, empty));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Rejected external call: System.Boolean System.String::IsNullOrEmpty(System.String)";
                break;
            case "highSurrogate" or "lowSurrogate":
                il.InsertBefore(start, il.Create(OpCodes.Ldstr, mutation == "highSurrogate" ? "\uD800" : "\uDC00"));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported string literal: an unpaired UTF-16 surrogate";
                break;
            case "argumentAddress":
                il.InsertBefore(start, il.Create(OpCodes.Ldarga_S, method.Parameters[1]));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported address of a class instance argument: " + method.FullName;
                break;
            case "localAddress":
                il.InsertBefore(start, il.Create(OpCodes.Ldloca_S, method.Body.Variables[0]));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported address of a class instance local: " + method.FullName;
                break;
            case "byref":
                method.Parameters[1].ParameterType = new ByReferenceType(text);
                selector = "Strings::Pick(System.Boolean,System.String&,System.String)";
                expected = "Unsupported by-reference class instance: System.String&";
                break;
            case "modified":
                method.Parameters[1].ParameterType = new OptionalModifierType(module.TypeSystem.Object, text);
                selector = "Strings::Pick(System.Boolean,System.String modopt(System.Object),System.String)";
                expected = "Custom modifiers are unsupported in method signatures";
                break;
            default: throw new InvalidOperationException("Unknown string rejection fixture: " + mutation);
        }
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect string rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS string rejection: {mutation}");
}
Console.WriteLine("PASS strings: passed, returned, stored and loaded as literals; reads and addresses rejected by name");
