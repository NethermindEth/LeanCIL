using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class CallReturnType
{
    internal static TypeReference Resolve(MethodReference method)
    {
        if (method is not GenericInstanceMethod generic) return method.ReturnType;
        return Substitute(method.ReturnType, generic);
    }

    static TypeReference Substitute(TypeReference type, GenericInstanceMethod method)
    {
        if (type is GenericParameter { Type: GenericParameterType.Method } parameter)
        {
            if ((uint)parameter.Position >= (uint)method.GenericArguments.Count)
                throw new InvalidDataException("Invalid call return type parameter");
            return method.GenericArguments[parameter.Position];
        }
        if (type is ByReferenceType byRef) return new ByReferenceType(Substitute(byRef.ElementType, method));
        if (type is PointerType pointer) return new PointerType(Substitute(pointer.ElementType, method));
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
