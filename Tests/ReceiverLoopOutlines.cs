#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
foreach (var methodName in new[] { "Drain", "Clear" })
{
    var root = At("artifacts/ReceiverLoopOutlines/" + methodName);
    Directory.CreateDirectory(root);
    string[] Cli(params string[] arguments) => ["dotnet", ExtractorPath, .. arguments];
    var selector = $"OutlineCountdown::{methodName}()";
    var extraction = Path.Combine(root, "Drain");
    Run(Extract("extract", assembly, "Examples", selector, extraction));
    var outline = Path.Combine(root, "Outline.lean");
    File.Delete(outline);
    Run(Cli("new-proof", extraction, outline));
    var source = File.ReadAllText(outline).ReplaceLineEndings("\n");
    if (source.Contains("-- not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException("Receiver loop left an execution hole:\n" + source);
    source = Regex.Replace(source, @"^import Extracted\.[^\n]+", "import Extracted");
    source = Regex.Replace(source, @"(def Precondition[\s\S]*?: Prop :=) sorry", "$1 True");
    source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry", """
        $1
          ∀ remaining count : W64,
            Contents initial outlineCountdown 8 [remaining] →
            Contents initial (outlineCountdown.element 1 8) 8 [count] →
            result = count + remaining ∧ Contents final outlineCountdown 8 [0] ∧
              Contents final (outlineCountdown.element 1 8) 8 [result]
        """);
    source = Regex.Replace(source, @"(def invariant[\s\S]*?: Prop :=) sorry", """
        $1
          ∀ remaining count : W64,
            Contents initial outlineCountdown 8 [remaining] →
            Contents initial (outlineCountdown.element 1 8) 8 [count] →
            state.count + state.remaining = count + remaining
        """);
    source = Regex.Replace(source, @"(def measure[\s\S]*?: Nat :=) sorry", "$1 state.remaining.toNat");
    var invariant = new Regex("case invariant => sorry[^\\n]*");
    source = invariant.Replace(source, """
        case invariant =>
              intro remaining count first second
              have left := (remainingRead.load_word (index := 0) rfl).symm.trans
                (first.load_word (index := 0) rfl)
              have right := (countRead.load_word (index := 0) rfl).symm.trans
                (second.load_word (index := 0) rfl)
              simp only [Except.ok.injEq, CIL.Value.i64.injEq] at left right
              change state.count + state.remaining = count + remaining
              rw [left, right]
        """, 1);
    source = invariant.Replace(source, """
        case invariant =>
                intro remaining count first second
                have previous := invariantHeld remaining count first second
                change (state.count + 1) + (state.remaining - 1) = count + remaining
                bv_omega
        """, 1);
    source = source.Replace("case measure => sorry -- The continuing iteration decreases", """
        case measure =>
                change (state.remaining - 1).toNat < state.remaining.toNat
                have positive : 0 < state.remaining.toNat := by
                  have nonzero : state.remaining.toNat ≠ 0 := by
                    intro zero
                    exact branch2 (BitVec.eq_of_toNat_eq zero)
                  omega
                rw [BitVec.toNat_sub_of_le]
                · simp; omega
                · change 1 ≤ state.remaining.toNat
                  omega
        """, StringComparison.Ordinal);
    source = source.Replace("all_goals sorry -- Required postcondition at this return", """
        all_goals
              simp only [leaveFrame, List.foldl_nil]
              intro remaining count first second
              have total := invariantHeld remaining count first second
              exact ⟨by simpa [branch2] using total,
                by simpa [branch2] using state.remainingRead, state.countRead⟩
        """, StringComparison.Ordinal);
    if (methodName == "Clear")
        source = source.Replace("result = count + remaining", "True", StringComparison.Ordinal)
            .Replace("8 [result]", "8 [count + remaining]", StringComparison.Ordinal)
            .Replace("⟨by simpa [branch2] using total,", "⟨True.intro,", StringComparison.Ordinal)
            .Replace("state.countRead⟩", "by simpa [show state.count = count + remaining by " +
                "simpa [branch2] using total] using state.countRead⟩", StringComparison.Ordinal);
    if (source.Contains("=> sorry", StringComparison.Ordinal) || source.Contains(":= sorry", StringComparison.Ordinal))
        throw new InvalidOperationException("Unfilled receiver-loop obligations");
    var proof = Path.Combine(root, "Filled.lean");
    File.WriteAllText(proof, source);
    Run(Cli("verify", extraction, "--proof", proof));
    foreach (var mutation in new[] { "wrong-count", "nondecreasing" })
    {
        var output = Path.Combine(root, mutation);
        Directory.CreateDirectory(output);
        var dll = Path.Combine(output, "Examples.dll");
        using (var module = ModuleDefinition.ReadModule(assembly))
        {
            var method = module.GetType("Examples.OutlineCountdown").Methods
                .Single(method => method.Name == methodName);
            var operation = method.Body.Instructions.Single(instruction => instruction.OpCode.Code ==
                (mutation == "wrong-count" ? Code.Add : Code.Sub));
            operation.OpCode = mutation == "wrong-count" ? OpCodes.Sub : OpCodes.Add;
            module.Write(dll);
        }
        Run(Extract("extract", dll, "Examples", selector, output));
        var rejected = Execute(Cli("verify", output, "--proof", proof));
        if (rejected.Code == 0 || !rejected.Output.Contains("Lean could not prove", StringComparison.Ordinal) ||
            File.Exists(Path.Combine(output, "verified.json")))
            throw new InvalidOperationException("Receiver-loop mutation was not rejected during proof checking:\n" +
                rejected.Output);
    }
    Console.WriteLine("PASS receiver loop termination, accumulated count, field contents, frame " +
        "and mutation rejection");
}

var doWhileRoot = At("artifacts/ReceiverLoopOutlines/DoWhile");
Run(Extract("extract", assembly, "Examples", "OutlineCountdown::DrainAtLeastOnce()", doWhileRoot));
var doWhileProof = Path.Combine(doWhileRoot, "Outline.lean");
File.Delete(doWhileProof);
Run(["dotnet", ExtractorPath, "new-proof", doWhileRoot, doWhileProof]);
if (File.ReadAllText(doWhileProof).Contains("-- not outlined:", StringComparison.Ordinal))
    throw new InvalidOperationException("The do/while receiver loop left an execution hole");
var unfinished = Execute(["dotnet", ExtractorPath, "verify", doWhileRoot, "--proof", doWhileProof]);
if (unfinished.Code == 0 || !unfinished.Output.Contains("Unapproved proof axioms: sorryAx", StringComparison.Ordinal))
    throw new InvalidOperationException("The do/while outline failed before its open obligations:\n" +
        unfinished.Output);
Console.WriteLine("PASS do/while receiver outline elaborates and rejects unfilled proof obligations");
