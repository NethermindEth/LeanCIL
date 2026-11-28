#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/VerifyReports.cs

using System.Diagnostics;
using System.Text.Json;

var root = At("artifacts/DeepDiagnostics-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
var image = Path.Combine(root, "image.bin");
File.WriteAllBytes(image, [1, 2, 3]);
var manifest = Path.Combine(root, "images.sha256");
File.WriteAllText(manifest, Sha(image) + "  image.bin\n");
var inputs = DeepCheckInputs.Read(manifest);
var identity = new ExtractionIdentity(root, new string('a', 64), JsonSerializer.SerializeToElement(new
{
    assemblyIdentity = "First", assemblySha256 = Sha(image),
    references = new[] { new { assemblyIdentity = "Second", sha256 = Sha(image) } }
}), new(StringComparer.Ordinal));
var holder = new DeepCheckRun(inputs);
Require(holder.Attempt is null, "An unbegun request has no binding attempt");
Expect(() => DeepCheckRun.Claim(null, holder), "requires inputs");
Expect(() => DeepCheckRun.Claim(DeepCheckInputs.Read(manifest), holder), "inputs do not match");
DeepCheckRun.Claim(inputs, holder);
holder.Begin(identity);
Expect(() => DeepCheckRun.Claim(inputs, holder), "already used");
Expect(() => holder.Begin(identity), "one claimed request");
var attempt = holder.Attempt!;
Expect(() => attempt.RequireIdentity(identity with { Sha256 = new string('b', 64) }), "identity changed");
Expect(() => attempt.RejectImage(Sha256Digest.Parse(new string('b', 64), "a test digest"), "unknown"),
    "Unknown deep-check image");
Expect(() => attempt.RejectFact((BindingFact)100, "unknown"), "Unknown binding fact");
Expect(() => attempt.RejectFact(BindingFact.BodyBytes, " "), "reason");
var incomplete = attempt.Failure("kernel replay", "resource limit");
Require(incomplete.images.Length == 2 && incomplete.images.All(result =>
    result.status == FailureReports.BindingFailureStatus.NotCovered), "Duplicate digest identities are retained");
Require(incomplete.facts.Select(fact => fact.id).SequenceEqual(Enum.GetValues<BindingFact>().Select(fact =>
    JsonSerializer.SerializeToElement(fact).GetString())), "Every fact uses its existing wire name in order");
attempt.RejectImage(Sha256Digest.Parse(Sha(image), "the test image"), "digest theorem rejected");
var rejected = attempt.Failure("theorem audit", "rejected");
Require(rejected.images.All(result => result.status == FailureReports.BindingFailureStatus.Failed) &&
    rejected.facts.All(result => result.status == FailureReports.BindingFailureStatus.NotCovered),
    "A rejected digest affects its identities without a transitive fact rejection");

foreach (var status in Enum.GetValues<FailureReports.BindingFailureStatus>())
{
    var encoded = JsonSerializer.Serialize(status);
    Require(encoded == (status == FailureReports.BindingFailureStatus.Failed ? "\"failed\"" : "\"not covered\"") &&
        JsonSerializer.Deserialize<FailureReports.BindingFailureStatus>(encoded) == status, "Exact status spelling");
}
foreach (var invalid in new[] { "0", "1", "\"reconfirmed\"", "\"trusted\"", "null", "\"Failed\"" })
    Expect(() => JsonSerializer.Deserialize<FailureReports.BindingFailureStatus>(invalid), "Expected");
Expect(() => JsonSerializer.Serialize((FailureReports.BindingFailureStatus)100), "Invalid binding failure status");
Expect(() => JsonSerializer.Deserialize<BindingSection>(JsonSerializer.Serialize(rejected)), "required properties");
var failure = FailureReports.Classify("theorem audit", "rejected", null, "Proof.correct", "Proof.lean", root, null);
Require(!JsonSerializer.SerializeToElement(failure).TryGetProperty("binding", out _), "Absent binding is omitted");
failure = failure with { binding = rejected };
var result = VerifyReports.Result("failed", failure, "Proof.correct", "Proof.lean", root, null,
    "theorem audit", null, null, []);
Require(result["binding"]!.ToJsonString() == JsonSerializer.Serialize(rejected) &&
    result["unknown"]?["binding"] is null, "JSON reports retain failed binding");
Expect(() => VerifyReports.Result("failed", failure, "Proof.correct", "Proof.lean", root, null,
    "theorem audit", null, null, [], binding: BindingSection.Default), "successful and failed binding");
VerifyReports.Result("verified", failure with { binding = null }, "Proof.correct", "Proof.lean", root, null,
    null, [], "True", [], binding: BindingSection.Default);
Console.WriteLine("PASS failed binding serialization, request ownership and duplicate-digest identities");

BindingRequest[] requests =
[
    new("BindingAudit.Bodies", new("BindingAudit.bodies"), new BindingSubject.Fact(BindingFact.BodyBytes)),
    new("BindingAudit.Images", new("BindingAudit.images_eq"))
];
var source = Path.Combine(root, "sources");
Directory.CreateDirectory(source);
DeepSessionContribution contribution = new([], new(requests), new(StringComparer.Ordinal),
    new(StringComparer.Ordinal), new(StringComparer.Ordinal), source);
AuditRequest[] expected = [new("Proof.correct"), .. requests.Select(request => request.Audit)];
AuditedTheorem body = new("BindingAudit.bodies", "Theorem statement mismatch", [], null, null);
AuditedTheorem equality = new("BindingAudit.images_eq", null, [], null, null);
AuditedTheorem proof = new("Proof.correct", null, [], null, null);
foreach (var malformed in new AuditedTheorem[][]
{
    [body, equality], [proof, body, equality, new("Extra", null, [], null, null)],
    [proof, body, equality, body], [proof with { axioms = null }, body, equality]
})
{
    var untouched = new DeepCheckAttempt(inputs, identity.Sha256, inputs.MatchPins(identity.Root));
    Expect(() => contribution.RequireTheorems(new(new(), malformed, []), expected, untouched),
        malformed.Select(result => result.name).Distinct().Count() != malformed.Length
            ? "same key" : "Incomplete deep-check");
    Require(untouched.Failure("audit", "incomplete").facts.All(fact =>
        fact.status == FailureReports.BindingFailureStatus.NotCovered), "Malformed joined results mark no subject");
}
var bodyAttempt = new DeepCheckAttempt(inputs, identity.Sha256, inputs.MatchPins(identity.Root));
Expect(() => contribution.RequireTheorems(new(new(), [proof, body, equality], []), expected, bodyAttempt),
    "Theorem statement mismatch");
Require(bodyAttempt.Failure("audit", "rejected").facts.Single(fact => fact.id == "body-bytes").status ==
    FailureReports.BindingFailureStatus.Failed, "Named body rejection marks only BodyBytes");
var equalityAttempt = new DeepCheckAttempt(inputs, identity.Sha256, inputs.MatchPins(identity.Root));
Expect(() => contribution.RequireTheorems(new(new(), [proof, body with { error = null },
    equality with { error = "Theorem statement mismatch" }], []), expected, equalityAttempt),
    "Theorem statement mismatch");
Require(equalityAttempt.Failure("audit", "rejected").facts.All(fact =>
    fact.status == FailureReports.BindingFailureStatus.NotCovered), "Images equality has no fact subject");
Console.WriteLine("PASS joined request-set validation precedes named failure attribution");

var scales = new[] { 64, 256, 1024 }.Select(count =>
{
    DeepCheckInputs.Pin[] pins = [.. Enumerable.Range(0, count).Select(index =>
        new DeepCheckInputs.Pin("Identity" + index,
            new("", Sha256Digest.Parse(index.ToString("x64"), "a test pin"), [])))];
    var scaled = new DeepCheckAttempt(inputs, identity.Sha256, pins);
    foreach (var pin in pins) scaled.RejectImage(pin.Image.Digest, "rejected");
    return (Count: count, Attempt: scaled);
}).ToArray();
foreach (var scale in scales)
    for (var warm = 0; warm < 64; warm++) scale.Attempt.Failure("audit", "rejected");
int repetitions = 1;
while (Measure(scales[0].Attempt, repetitions) < 25) repetitions *= 2;
var timings = scales.Select(_ => new List<double>()).ToArray();
Require(Growth(20, 80) && Growth(20, 100) && !Growth(20, 320),
    "Scaling bound must accept linear/n log n growth and reject quadratic growth");
double previousBytes = 0;
for (var round = 0; round < 7; round++)
    foreach (var index in round % 2 == 0 ? new[] { 0, 1, 2 } : new[] { 2, 1, 0 })
        timings[index].Add(Measure(scales[index].Attempt, repetitions));
double previousTime = 0;
for (var index = 0; index < scales.Length; index++)
{
    var started = GC.GetAllocatedBytesForCurrentThread();
    scales[index].Attempt.Failure("audit", "rejected");
    var allocated = GC.GetAllocatedBytesForCurrentThread() - started;
    var minimum = timings[index].Min();
    if (previousTime > 0)
        Require(Growth(previousTime, minimum) && allocated <= previousBytes * 6 + 1024,
            "Failure mapping grows faster than linear work");
    Console.WriteLine($"PASS {scales[index].Count} failed image subjects: {allocated} bytes, " +
        $"{minimum:F3} ms minimum for {repetitions} mappings");
    previousTime = minimum;
    previousBytes = allocated;
}

static double Measure(DeepCheckAttempt attempt, int repetitions)
{
    var timer = Stopwatch.StartNew();
    for (var repeat = 0; repeat < repetitions; repeat++)
        GC.KeepAlive(attempt.Failure("audit", "rejected"));
    return timer.Elapsed.TotalMilliseconds;
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static bool Growth(double previous, double current) => current <= previous * 6 + 1;

static void Expect(Action action, string diagnostic)
{
    try { action(); }
    catch (Exception error) when (error.Message.Contains(diagnostic, StringComparison.Ordinal)) { return; }
    throw new InvalidOperationException("Expected diagnostic rejection: " + diagnostic);
}
