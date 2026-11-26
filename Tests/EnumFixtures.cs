partial class Program
{
    // The enum rows in the unsigned Examples assembly, including the empty namespace of nested rows.
    static string ExampleEnumIdentity(string name, string? declaring = null)
    {
        const string assembly = """{ name := name!"Examples", version := { major := 1, minor := 0, build := 0, revision := 0 }, culture := name!"", publicKeyToken := none }""";
        var row = declaring is null ? """typeNamespace := name!"Examples", """ :
            $$"""typeNamespace := name!"", enclosing := [{ typeNamespace := name!"Examples", name := name!"{{declaring}}" }], """;
        return $$"""{ assembly := {{assembly}}, {{row}}name := name!"{{name}}" }""";
    }
}
