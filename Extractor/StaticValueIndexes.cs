using System.Runtime.ExceptionServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static partial class StaticValues
{
    // One validation reads an unchanged compiled module; specialization creates detached clones.
    internal sealed class Context(ModuleDefinition module)
    {
        readonly Dictionary<MethodDefinition, ConstructorIndex> constructors = new();
        readonly Dictionary<MethodDefinition, FieldUses> addresses = new();
        readonly Dictionary<MethodDefinition, MethodDefinition?> initializerStatics = new();
        readonly Dictionary<string, MethodSpecialization> specializations = new(StringComparer.Ordinal);
        FieldUses? stores;

        internal MethodDefinition Specialize(MethodReference reference, string architecture)
        {
            if (reference.DeclaringType is not GenericInstanceType) return reference.Resolve();
            if (!specializations.TryGetValue(architecture, out var instances))
                specializations.Add(architecture, instances = new MethodSpecialization(module, architecture));
            return instances.Instantiate(reference);
        }

        internal Value Resolve(FieldReference reference, string architecture = "scalar")
        {
            var field = Field(reference, module, architecture);
            var values = cache.GetValue(field, _ => new());
            return values.GetOrAdd(architecture, selected => Compute(field, module, selected, this));
        }

        internal ConstructorIndex Constructor(MethodDefinition method)
        {
            if (!constructors.TryGetValue(method, out var index))
                constructors.Add(method, index = new ConstructorIndex(method));
            return index;
        }

        internal MethodDefinition? OutsideStore(FieldDefinition field, MethodDefinition constructor)
        {
            stores ??= FieldUses.Scan(module.GetTypes().SelectMany(type => type.Methods)
                .Where(method => method.HasBody), Code.Stsfld);
            return stores.First(field, constructor);
        }

        internal MethodDefinition? InitializerStaticAccess(MethodDefinition initializer)
        {
            if (initializerStatics.TryGetValue(initializer, out var first)) return first;
            first = Closure(initializer, module).FirstOrDefault(method => method.Body.Instructions.Any(instruction =>
                instruction.OpCode.Code is Code.Ldsfld or Code.Ldsflda or Code.Stsfld));
            initializerStatics.Add(initializer, first);
            return first;
        }
        internal MethodDefinition? AddressTaken(FieldDefinition field, MethodDefinition constructor)
        {
            if (!addresses.TryGetValue(constructor, out var uses))
                addresses.Add(constructor, uses = FieldUses.Scan(Closure(constructor, module), Code.Ldsflda));
            return uses.First(field);
        }
    }

    sealed record Occurrence(MethodDefinition? Method, int Order, ExceptionDispatchInfo? Error = null);

    // Two distinct methods suffice because a query can exclude only its own static constructor.
    sealed class FirstMethods
    {
        internal Occurrence? First;
        internal Occurrence? Second;
        internal void Add(Occurrence occurrence)
        {
            if (First is null) First = occurrence;
            else if (Second is null && First.Method != occurrence.Method) Second = occurrence;
        }
        internal Occurrence? Except(MethodDefinition? excluded) =>
            excluded is not null && First?.Method == excluded ? Second : First;
    }

    sealed class FieldUses
    {
        readonly Dictionary<FieldDefinition, FirstMethods> fields = new();
        readonly FirstMethods errors = new();

        internal static FieldUses Scan(IEnumerable<MethodDefinition> methods, Code opcode)
        {
            var uses = new FieldUses();
            var order = 0;
            try
            {
                foreach (var method in methods)
                    foreach (var instruction in method.Body.Instructions)
                    {
                        order++;
                        try
                        {
                            if (Stored(instruction, opcode) is not { } field) continue;
                            if (!uses.fields.TryGetValue(field, out var occurrences))
                                uses.fields.Add(field, occurrences = new FirstMethods());
                            occurrences.Add(new(method, order));
                        }
                        catch (Exception error)
                        {
                            uses.errors.Add(new(method, order, ExceptionDispatchInfo.Capture(error)));
                        }
                    }
            }
            catch (Exception error)
            {
                uses.errors.Add(new(null, ++order, ExceptionDispatchInfo.Capture(error)));
            }
            return uses;
        }

        internal MethodDefinition? First(FieldDefinition field, MethodDefinition? excluded = null)
        {
            var found = fields.GetValueOrDefault(field)?.Except(excluded);
            var error = errors.Except(excluded);
            if (error is not null && (found is null || error.Order < found.Order)) error.Error!.Throw();
            return found?.Method;
        }
    }

    internal sealed class ConstructorIndex
    {
        readonly Dictionary<FieldDefinition, List<int>> stores = new();
        readonly ExceptionDispatchInfo? storeError;
        readonly Instruction?[] reentries;
        internal int FirstControlTransfer { get; }

        internal ConstructorIndex(MethodDefinition method)
        {
            var code = method.Body.Instructions;
            var positions = new InstructionIndex(method);
            FirstControlTransfer = code.Count;
            reentries = new Instruction?[code.Count];
            for (var index = 0; index < code.Count; index++)
            {
                var instruction = code[index];
                try
                {
                    if (Stored(instruction, Code.Stsfld) is { } field)
                    {
                        if (!stores.TryGetValue(field, out var indices)) stores.Add(field, indices = []);
                        indices.Add(index);
                    }
                }
                catch (Exception error) { storeError ??= ExceptionDispatchInfo.Capture(error); }
                if (FirstControlTransfer == code.Count &&
                    (instruction.OpCode.FlowControl is not (FlowControl.Next or FlowControl.Call or FlowControl.Meta) ||
                        instruction.OpCode.Code == Code.Jmp)) FirstControlTransfer = index;
                var earliest = instruction.Operand switch
                {
                    Instruction target => positions.Position(target),
                    Instruction[] targets when targets.Length != 0 => targets.Min(positions.Position),
                    _ => code.Count
                };
                if (earliest < code.Count)
                {
                    earliest = Math.Max(0, earliest);
                    reentries[earliest] ??= instruction;
                }
            }
            Instruction? first = null;
            for (var index = 0; index < reentries.Length; index++)
            {
                if (reentries[index] is { } candidate &&
                    (first is null || positions.Position(candidate) < positions.Position(first))) first = candidate;
                reentries[index] = first;
            }
        }

        internal IReadOnlyList<int> Stores(FieldDefinition field)
        {
            storeError?.Throw();
            return stores.GetValueOrDefault(field) ?? (IReadOnlyList<int>)Array.Empty<int>();
        }
        internal Instruction? Reentry(int store) => reentries[store];
    }
}
