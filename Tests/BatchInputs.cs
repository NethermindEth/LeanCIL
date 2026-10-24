#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

var directory = At("artifacts/BatchInputs/" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
var proof = Path.Combine(directory, "Proof.lean");
var otherProof = Path.Combine(directory, "Other.lean");
var settings = Path.Combine(directory, "settings.json");
var commonSource = At("Tests/BatchInputsMutation" + Guid.NewGuid().ToString("N") + ".lean");
try
{
    File.WriteAllText(proof, "-- first proof\n");
    File.WriteAllText(otherProof, "-- second proof\n");
    File.WriteAllText(settings, "{}\n");
    var common = CommonInputs();
    var first = Inputs(common, proof, settings);
    var second = Inputs(common, otherProof);
    Require(Same(first, Inputs(proof, settings)), "settings snapshot differs from direct verification");
    Require(Same(second, Inputs(otherProof)), "proof snapshot differs from direct verification");
    Require(first.Comparer.Equals(StringComparer.Ordinal), "snapshot comparer changed");
    Require(first["proof:" + proof] == Sha(proof), "proof identity missing");
    Require(first["settings:" + settings] == Sha(settings), "settings identity missing");
    Require(!second.ContainsKey("proof:" + proof) && !second.ContainsKey("settings:" + settings),
        "per-proof inputs leaked into another snapshot");
    first["probe"] = "changed";
    Require(!common.ContainsKey("probe") && !second.ContainsKey("probe"), "snapshots share mutable dictionaries");
    first.Remove("probe");
    Console.WriteLine("PASS direct and batched input identities, settings and dictionary isolation");

    File.AppendAllText(proof, "-- changed after another fixture was checked\n");
    var after = CommonInputs();
    Require(!Same(first, Inputs(after, proof, settings)), "earlier proof mutation was accepted");
    Require(Same(second, Inputs(after, otherProof)), "unmodified proof changed");
    File.WriteAllText(proof, "-- first proof\n");
    File.AppendAllText(settings, " \n");
    Require(!Same(first, Inputs(proof, settings)), "direct verification missed changed inputs");
    Console.WriteLine("PASS earlier proof and settings mutations rejected by fresh snapshots");

    File.WriteAllText(commonSource, "-- added repository input\n");
    after = CommonInputs();
    Require(!Same(second, Inputs(after, otherProof)), "new common source was accepted");
    var added = Inputs(after, otherProof);
    File.AppendAllText(commonSource, "-- changed repository input\n");
    Require(!Same(added, Inputs(CommonInputs(), otherProof)), "changed common source was accepted");
    File.Delete(commonSource);
    Require(!Same(added, Inputs(CommonInputs(), otherProof)), "deleted common source was accepted");
    Require(Same(second, Inputs(CommonInputs(), otherProof)), "restored common inputs differ");
    Console.WriteLine("PASS added, changed and deleted common inputs rejected by fresh snapshots");
}
finally
{
    File.Delete(commonSource);
    Directory.Delete(directory, recursive: true);
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
