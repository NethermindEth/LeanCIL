using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class CallReturnType
{
    internal static TypeReference Resolve(MethodReference method) => Substitute(method.ReturnType, method);

    internal static IEnumerable<TypeReference> Parameters(MethodReference method) =>
        method.Parameters.Select(parameter => Substitute(parameter.ParameterType, method));

    static TypeReference Substitute(TypeReference type, MethodReference method)
    {
        if (type is GenericParameter parameter)
        {
            IList<TypeReference>? arguments = parameter.Type == GenericParameterType.Method
                ? (method as GenericInstanceMethod)?.GenericArguments
                : (method.DeclaringType as GenericInstanceType)?.GenericArguments;
            if (arguments is null) return type;
            if ((uint)parameter.Position >= (uint)arguments.Count)
                throw new InvalidDataException("Invalid call signature type parameter");
            return arguments[parameter.Position];
        }
        if (type is ByReferenceType byRef) return new ByReferenceType(Substitute(byRef.ElementType, method));
        if (type is RequiredModifierType required)
            return new RequiredModifierType(required.ModifierType, Substitute(required.ElementType, method));
        if (type is PointerType pointer) return new PointerType(Substitute(pointer.ElementType, method));
        if (type is ArrayType { IsVector: true } array)
            return new ArrayType(Substitute(array.ElementType, method));
        if (type is GenericInstanceType generic)
        {
            GenericInstanceType result = new(generic.ElementType);
            foreach (TypeReference argument in generic.GenericArguments)
                result.GenericArguments.Add(Substitute(argument, method));
            return result;
        }
        return type;
    }
}
