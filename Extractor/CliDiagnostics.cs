namespace Nethermind.LeanCIL;

internal sealed class CliFailure(string stage, Exception cause, bool reported = false) : Exception(cause.Message, cause)
{
    internal string Stage { get; } = stage;

    /// <summary>Whether the command already reported this failure itself, so no text diagnostic follows.</summary>
    internal bool Reported { get; } = reported;
}

internal enum Rejection { Selector, Call }

// Classifies a validation failure so the CLI can suggest a fix that matches its cause.
internal static class Rejections
{
    const string Key = "Nethermind.LeanCIL.Rejection";

    internal static T Tag<T>(Rejection kind, T error) where T : Exception
    {
        error.Data[Key] = kind;
        return error;
    }

    internal static Rejection? Of(Exception error) => error.Data[Key] as Rejection?;
}

internal static class CliDiagnostics
{
    /// <summary>Exception data key holding the failed proof's located Lean messages.</summary>
    internal const string ProofMessagesKey = "LeanCIL.ProofMessages";

    /// <summary>Exception data key holding a report line printed after `Next:`, such as an option to add.</summary>
    internal const string HintKey = "LeanCIL.Hint";

    const string NextKey = "LeanCIL.Next";

    /// <summary>Gives `error` its own `Next:` line: the fix for the cause its message states.</summary>
    internal static T WithNext<T>(T error, string next) where T : Exception
    {
        error.Data[NextKey] = next;
        return error;
    }

    /// <summary>
    /// Proof-authored text with control and bidirectional override characters shown as escapes, so it
    /// cannot rewrite or reorder the report lines printed around it.
    /// </summary>
    internal static string Printable(string text) => string.Concat(text.Select(character =>
        character != '\n' && character != '\t' && (char.IsControl(character) || IsBidiControl(character))
            ? $"\\u{(int)character:X4}" : character.ToString()));

    static bool IsBidiControl(char character) =>
        character is >= '‪' and <= '‮' or >= '⁦' and <= '⁩' or '‎' or '‏' or '؜';

    internal static void Write(Exception error, string stage, bool invalid)
    {
        if (error is CliFailure failure)
            stage = failure.Stage;

        var next = stage switch
        {
            "arguments" => "Run leancil --help for command syntax.",
            "assembly loading" => "Check the DLL path and build the assembly before extracting it.",
            "metadata and CIL validation" => Rejections.Of(error is CliFailure { InnerException: { } cause } ? cause : error) switch
            {
                Rejection.Selector => "Use leancil list to find the exact method selector.",
                Rejection.Call => "Reachable calls must target methods in the extracted assembly or runtime calls modelled by LeanCIL. " +
                    "Remove the call from the extracted path, or see Supported subset and limits in the README for the modelled calls.",
                _ => "Use the supported CIL and metadata subset described in the README."
            },
            "extraction integrity" => "Rerun leancil extract with the intended assembly, method and profile, then rerun this command.",
            "proof selection" => "Supply --proof path/to/Proof.lean, or correct the proof path and theorem in verification.json.",
            "Lean library build" => "Ensure Lean and Lake are installed with the bundled lean-toolchain version, then address the build diagnostic below.",
            "proof checking" => "Read the Lean diagnostic below and check the implementation against the stated contract, including its preconditions.",
            "compile check" => "Fix the elaboration errors below, then rerun the compile check.",
            "theorem audit" => "Select a proved theorem with --theorem and remove unproved or unsupported axioms from its dependencies.",
            "open goals" => "Prove each goal listed below in place of its `sorry` or failing tactic, then rerun.",
            "proof outline" => "Write this proof by hand from a similar example, or report the shape as an issue.",
            "library audit" => "Address the kernel replay or axiom diagnostic for the listed theorems, or correct the namespace prefixes.",
            "build" => "Read the build output, then fix the project or its build properties in the manifest.",
            "extraction" => "Run leancil extract on the built assembly, method and profile to see why.",
            "program comparison" => "Fix the fixture case, or the variant's program if the change is intended.",
            "refutation template" or "proof template" =>
                "Give every template placeholder a value and every value a placeholder.",
            "statement identity" => "State the variant's theorem as production's statement, or its refutation as " +
                "that statement's negation; name only declarations both proofs import.",
            _ => "Check the diagnostic and the input paths, then retry."
        };

        var raised = error is CliFailure { InnerException: { } inner } ? inner : error;
        if (raised.Data[NextKey] is string fix) next = fix;

        var missingTool = error.Message.Contains("Required command not found:", StringComparison.Ordinal);
        if (missingTool)
            next = "Install the missing tool and ensure it is on PATH. Verification requires .NET, Lean and Lake.";

        // A panic leaves a tactic running on a default value, so the report leads with it at any stage.
        var internalError = !missingTool && LeanOutput.InternalErrors(error.Message,
            raised.Data[LeanDiagnostics.HiddenModulesKey] as string[]).Count > 0;
        if (internalError)
            next = "Report the internal error below as a LeanCIL issue with the proof or module that produced it. " +
                "No result of this run is accepted.";

        var summary = internalError ? "Lean or a LeanCIL tactic reported an internal error."
            : error is CliFailure && !missingTool ? stage switch
        {
            "proof checking" => "Lean could not prove the selected theorem.",
            "compile check" => "Lean could not compile the selected proof.",
            "Lean library build" => "The Lean library or proof dependencies could not be built.",
            "theorem audit" => "The selected theorem did not pass the proof-integrity audit.",
            _ => error.Message
        } : error.Message;

        Console.Error.WriteLine($"{(invalid ? "Invalid" : "Error")}: {Printable(summary)}");
        Console.Error.WriteLine($"  Stage: {stage}");
        Console.Error.WriteLine($"  Next: {next}");
        if (error.Data[HintKey] is string hint) Console.Error.WriteLine($"  {hint}");
        if (summary != error.Message)
        {
            // Each Lean error is printed once, located in the file the developer edits rather than a session copy.
            var cause = error is CliFailure ? error.InnerException ?? error : error;
            var hidden = cause.Data[LeanDiagnostics.HiddenModulesKey] as string[];
            var copies = cause.Data[SourceCopies.Key] as SourceCopies;
            var lean = LeanDiagnostics.Summarize(error.Message, hidden,
                location => copies?.Locate(location, CliPaths.Display) ?? location,
                module => copies?.ModuleOf(module) ?? module);
            // The session's copies are deleted when it ends, so details cite the originals instead.
            string Shown(string text) => copies?.Displayed(text, CliPaths.Display) ?? text;
            if (lean is null)
                Console.Error.WriteLine("Details:\n" + Printable(Shown(error.Message.ReplaceLineEndings("\n"))));
            else
            {
                Console.Error.Write(Printable(lean.Text));
                if (lean.Shortened.Length > 0)
                    Console.Error.Write("Details:\n" + Printable(Shown(lean.Shortened)));
            }
        }
        if (error.Data[ProofMessagesKey] is string messages)
            Console.Error.Write(messages);
    }
}
