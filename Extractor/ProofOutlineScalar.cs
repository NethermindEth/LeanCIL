using System.Globalization;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

// Straight-line bodies over word arguments that branch on tests of their words or fault on checked arithmetic.
internal static partial class ProofOutline
{
    /// <summary>The most return paths a scalar outline splits a body into.</summary>
    const int MaxScalarPaths = 8;

    /// <summary>What a scalar body does from one pc to a return along every path.</summary>
    abstract record ScalarStep;

    /// <summary>A return, stepped with the facts of the path that reaches it.</summary>
    sealed record ScalarReturn : ScalarStep;

    /// <summary>An overflow-checked operation: the body continues where `Fits` holds and throws where it fails,
    /// a side the precondition must rule out; `Lemma` steps it given `Fits`.</summary>
    sealed record ScalarCheck(string Fits, string Lemma, string Operation, int Pc, ScalarStep Next) : ScalarStep;

    /// <summary>A conditional branch on `Condition` of named words, with the pc and steps of each side.</summary>
    sealed record ScalarSplit(string Condition, int Pc, int HoldsPc, ScalarStep Holds, int FailsPc,
        ScalarStep Fails) : ScalarStep;

    /// <summary>A word on the walked stack: its term, or null when the outline does not name it.</summary>
    sealed record ScalarWord(string? Term, int Bits, long? Numeral = null);

    /// <summary>The paths of a body over word arguments that tests named words or checks arithmetic, with no
    /// backward jump; null when it does neither, has another operation or splits into too many paths.</summary>
    static ScalarStep? ScalarPaths(Specification spec, Operation[] ops)
    {
        if (spec.Parameters.Any(parameter => parameter.Shape != ParameterShape.Scalar)) return null;
        var paths = 0;
        var decided = false;
        ScalarStep? Walk(int pc, ImmutableStack stack)
        {
            for (; pc < ops.Length; pc++)
            {
                var op = ops[pc];
                if (op is Arg { Narrow: null } argument)
                {
                    var parameter = spec.Parameters[argument.Index];
                    stack = stack.Push(new(parameter.Name, 8 * parameter.Width));
                }
                else if (op is Constant constant)
                    stack = stack.Push(new(constant.Numeral ? $"{constant.Value}" : $"({constant.Value})",
                        constant.Width == 32 ? 32 : 64, constant.Numeral ? constant.Value : null));
                else if (op is StackOperation { IsArithmetic: true } arithmetic)
                {
                    if (stack.Count < 2) return null;
                    stack = stack.Pop(out var right).Pop(out var left);
                    var symbol = arithmetic.Symbol;
                    stack = stack.Push(new(left.Term is null || right.Term is null ? null
                        : $"{Operand(left.Term)} {symbol} {Operand(right.Term)}", right.Bits));
                }
                else if (op is CheckedArithmetic checkedOperation)
                {
                    if (stack.Count < 2) return null;
                    stack = stack.Pop(out var right).Pop(out var left);
                    if (left.Term is null || right.Term is null || left.Bits != right.Bits) return null;
                    var operation = checkedOperation.Operator.ToString().ToLowerInvariant();
                    var signed = checkedOperation.Signed;
                    var symbol = operation switch { "add" => "+", "sub" => "-", _ => "*" };
                    var fits = Fits(operation, signed, Operand(left.Term), Operand(right.Term), symbol, left.Bits);
                    stack = stack.Push(new($"{Operand(left.Term)} {symbol} {Operand(right.Term)}", left.Bits));
                    decided = true;
                    if (Walk(pc + 1, stack) is not { } next) return null;
                    var reading = signed ? "signed" : "unsigned";
                    return new ScalarCheck(fits, $"CIL.checkedValues_{operation}_{reading}_i{left.Bits}",
                        operation, pc, next);
                }
                else if (op is Jump jump)
                {
                    var target = jump.Target;
                    if (target <= pc) return null;
                    if (!jump.Conditional) { pc = target - 1; continue; }
                    var operands = new ScalarWord[jump.Operands];
                    if (stack.Count < operands.Length) return null;
                    for (var position = operands.Length - 1; position >= 0; position--)
                        stack = stack.Pop(out operands[position]);
                    if (operands.Any(operand => operand.Term is null || operand.Bits != operands[0].Bits))
                        return null;
                    var (condition, takenWhenTrue) = Body.Test(jump, [.. operands.Select(operand =>
                        new Body.Operand(Operand(operand.Term!), operand.Numeral))], operands[0].Bits);
                    var (holds, fails) = takenWhenTrue ? (target, pc + 1) : (pc + 1, target);
                    decided = true;
                    if (Walk(holds, stack) is not { } holdsStep || Walk(fails, stack) is not { } failsStep)
                        return null;
                    return new ScalarSplit(condition, pc, holds, holdsStep, fails, failsStep);
                }
                else if (op is Return { Narrow: null }) return ++paths > MaxScalarPaths ? null : new ScalarReturn();
                else if (op.IsNop) { }
                else if (Body.Pure(op))
                {
                    // Conversions and bit counts compute a word the outline does not name; it may be returned.
                    if (stack.Count == 0) return null;
                    stack = stack.Pop(out var word).Push(new(null,
                        op is StackOperation { Kind: StackOpcode.ConvU8 or StackOpcode.ConvI8 } ? 64
                        : op is StackOperation { Kind: StackOpcode.ConvU4 or StackOpcode.ConvI4 }
                            or ScalarIntrinsic { Result: 32 } ? 32
                        : word.Bits));
                }
                else return null;
            }
            return null;
        }
        var walked = Walk(0, ImmutableStack.Empty);
        return decided ? walked : null;
    }

    static string Operand(string term) => Regex.IsMatch(term, @"\A[\w.]+\z") ? term : $"({term})";

    /// <summary>The fact under which a checked operation of `bits`-bit words does not overflow.</summary>
    static string Fits(string operation, bool signed, string left, string right, string symbol, int bits)
    {
        if (signed)
        {
            var value = $"{left}.toInt {symbol} {right}.toInt";
            return $"-2 ^ {bits - 1} ≤ {value} ∧ {value} < 2 ^ {bits - 1}";
        }
        var (a, b) = ($"{left}.toNat", $"{right}.toNat");
        return operation == "sub" ? $"{b} ≤ {a}" : $"{a} {symbol} {b} < 2 ^ {bits}";
    }

    /// <summary>The proof of a scalar body's paths: a `by_cases` at each test and each checked operation, and at
    /// every return the run stepped with the path's facts and its own postcondition.</summary>
    static void ScalarRun(Writer lean, Specification spec, ScalarStep root)
    {
        var returns = 0;
        var checks = 0;
        var splits = 0;
        var many = Returns(root) > 1;
        void Emit(ScalarStep step, string indent, IReadOnlyList<string> facts, string where)
        {
            switch (step)
            {
                case ScalarReturn:
                    var suffix = many ? (++returns).ToString(CultureInfo.InvariantCulture) : "";
                    lean.Line($"{indent}refine ⟨CIL.executionBound Extracted.program 0, ?final{suffix}, " +
                        $"?results{suffix}, ?run, ?postcondition⟩");
                    lean.Line($"{indent}case run => cil_checked_steps [{string.Join(", ", facts)}]");
                    spec.Postcondition(lean, indent, "Postcondition of the returned value" + where);
                    break;
                case ScalarCheck check:
                    var index = ++checks;
                    var location = Location(spec.Method, check.Pc);
                    lean.Line($"{indent}by_cases fits{index} : {check.Fits}");
                    lean.Line($"{indent}· -- the checked {check.Operation} at {location} fits");
                    // A fact at the stepped instruction's level; the step reduces with it where the bounds recurse.
                    lean.Line($"{indent}  have checked{index} := {check.Lemma} fits{index}");
                    Emit(check.Next, indent + "  ", [.. facts, $"checked{index}"], where);
                    lean.Line($"{indent}· -- it overflows and throws at {location}, which Precondition must rule out");
                    lean.Line($"{indent}  exfalso");
                    lean.Line($"{indent}  cil_loop_obligation [Precondition]");
                    break;
                case ScalarSplit split:
                    var branch = $"branch{++splits}";
                    lean.Line($"{indent}by_cases {branch} : {split.Condition}");
                    lean.Line($"{indent}· -- `{branch}` holds: continues at {Location(spec.Method, split.HoldsPc)}");
                    Emit(split.Holds, indent + "  ", [.. facts, branch], Joined(where, $"`{branch}` holds"));
                    lean.Line($"{indent}· -- `{branch}` fails: continues at {Location(spec.Method, split.FailsPc)}");
                    Emit(split.Fails, indent + "  ", [.. facts, branch], Joined(where, $"`{branch}` fails"));
                    break;
            }
        }
        Emit(root, "  ", [], "");
    }

    static string Joined(string where, string side) => where.Length == 0 ? " where " + side : $"{where} and {side}";

    static int Returns(ScalarStep step) => step switch
    {
        ScalarCheck check => Returns(check.Next),
        ScalarSplit split => Returns(split.Holds) + Returns(split.Fails),
        _ => 1
    };

    /// <summary>A persistent stack, so each side of a split walks on from the same values.</summary>
    sealed class ImmutableStack
    {
        internal static readonly ImmutableStack Empty = new(null, null!, 0);
        readonly ImmutableStack? below;
        readonly ScalarWord top;

        ImmutableStack(ImmutableStack? below, ScalarWord top, int count) =>
            (this.below, this.top, Count) = (below, top, count);

        internal int Count { get; }

        internal ImmutableStack Push(ScalarWord word) => new(this, word, Count + 1);

        internal ImmutableStack Pop(out ScalarWord word)
        {
            word = top;
            return below!;
        }
    }
}
