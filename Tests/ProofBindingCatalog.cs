#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/ProofBindingCatalog.cs

using LeanCIL;

string root = Path.Combine(Path.GetTempPath(), "leancil-bindings-" + Guid.NewGuid().ToString("N"));
ProofGate scalar = new("Add", "scalar", "proofs/Add.lean", "Consumer.add");
ProofGate vector = new("Equal", "x64-v3", "proofs/Equal.lean", "Consumer.equal");
ProofGate[] catalog = [scalar, vector];
ProofBinding[] recipes = [new(scalar, "-- scalar\n"), new(vector, "-- vector\n")];
try
{
    var sources = ProofBindingCatalog.Sources(catalog, recipes);
    Require(sources.SequenceEqual(ProofBindingCatalog.Sources(catalog.Reverse(), recipes.Reverse())),
        "Catalog and recipe order must not change generated sources");
    Reject(() => ProofBindingCatalog.Materialize(root, catalog, recipes, check: true));
    Require(!Directory.Exists(root), "Check mode must not create output directories");
    ProofBindingCatalog.Materialize(root, catalog, recipes);
    ProofBindingCatalog.Materialize(root, catalog, recipes, check: true);
    string path = Path.Combine(root, scalar.Proof);
    File.WriteAllText(path, "-- changed\n");
    Reject(() => ProofBindingCatalog.Materialize(root, catalog, recipes, check: true));
    Require(File.ReadAllText(path) == "-- changed\n", "Check mode must not repair changed sources");
    ProofBindingCatalog.Materialize(root, catalog, recipes);
    Require(File.ReadAllText(path) == recipes[0].Source, "Materialization must restore reviewed source");

    foreach (ProofGate[] invalid in new ProofGate[][]
    {
        [vector], [scalar, scalar, vector], [scalar with { Profile = "x64-v4" }, vector],
        [scalar with { Theorem = "Consumer.wrong" }, vector],
        [scalar with { Proof = "proofs/Wrong.lean" }, vector],
        [scalar, vector, scalar with { Profile = "x64-v4" }]
    }) Reject(() => ProofBindingCatalog.Sources(invalid, recipes));
    Reject(() => ProofBindingCatalog.Sources(catalog, [.. recipes, recipes[0]]));
    foreach (string invalid in new[] { "../outside.lean", "/outside.lean", "proofs/../outside.lean",
        "proofs\\outside.lean", "proofs/A.lean:stream", "proofs//A.lean", "proofs/A.cs" })
    {
        ProofGate gate = scalar with { Proof = invalid };
        Reject(() => ProofBindingCatalog.Materialize(root, [gate], [new(gate, "-- rejected\n")]));
    }
    ProofGate shared = vector with { Proof = scalar.Proof };
    Reject(() => ProofBindingCatalog.Sources([scalar, shared],
        [recipes[0], new(shared, "-- conflicting\n")]));
    Require(ProofBindingCatalog.Sources([scalar, shared],
        [recipes[0], new(shared, recipes[0].Source)]).Count == 1, "Identical shared sources are emitted once");
    ProofGate caseCollision = vector with { Proof = "proofs/add.lean" };
    Reject(() => ProofBindingCatalog.Sources([scalar, caseCollision],
        [recipes[0], new(caseCollision, recipes[0].Source)]));
    Console.WriteLine("PASS exact binding catalogs, deterministic materialization and mutation rejection");
}
finally
{
    if (Directory.Exists(root)) Directory.Delete(root, recursive: true);
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static void Reject(Action action)
{
    try { action(); }
    catch (InvalidOperationException) { return; }
    throw new InvalidOperationException("Invalid binding input was accepted");
}
