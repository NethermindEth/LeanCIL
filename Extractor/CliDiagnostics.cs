namespace Nethermind.LeanCIL;

internal sealed class CliFailure(string stage, Exception cause) : Exception(cause.Message, cause)
{
    internal string Stage { get; } = stage;
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
            "theorem audit" => "Select a proved theorem with --theorem and remove unproved or unsupported axioms from its dependencies.",
            _ => "Check the diagnostic and the input paths, then retry."
        };

        var missingTool = error.Message.Contains("Required command not found:", StringComparison.Ordinal);
        if (missingTool)
            next = "Install the missing tool and ensure it is on PATH. Verification requires .NET, Lean and Lake.";

        var summary = error is CliFailure && !missingTool ? stage switch
        {
            "proof checking" => "Lean could not prove the selected theorem.",
            "Lean library build" => "The Lean library or proof dependencies could not be built.",
            "theorem audit" => "The selected theorem did not pass the proof-integrity audit.",
            _ => error.Message
        } : error.Message;

        Console.Error.WriteLine($"{(invalid ? "Invalid" : "Error")}: {summary}");
        Console.Error.WriteLine($"  Stage: {stage}");
        Console.Error.WriteLine($"  Next: {next}");
        if (summary != error.Message)
            Console.Error.WriteLine("Details:\n" + error.Message);
    }
}
