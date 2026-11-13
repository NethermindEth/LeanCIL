partial class Program
{
    static void CheckConsumerPackagePaths(string[] args)
    {
        var work = Path.Combine(Path.GetTempPath(), "leancil-package-paths-" + Guid.NewGuid().ToString("N"));
        var real = Path.Combine(work, "real");
        var package = Path.Combine(real, "package");
        var outside = Path.Combine(work, "outside");
        var built = Path.Combine(package, ".lake", "packages", "generated", "lib");
        Directory.CreateDirectory(built);
        Directory.CreateDirectory(outside);
        File.WriteAllText(Path.Combine(outside, "Secret.lean"), "-- outside the package\n");
        void Require(bool condition, string message)
        {
            if (!condition) throw new Exception(message);
        }
        void Reject(string root, string path, string route)
        {
            try { Within(root, path); }
            catch (InvalidDataException) { return; }
            throw new Exception($"A path that leaves its package through {route} was accepted: {path}");
        }
        try
        {
            Reject(package, "../outside/Secret.lean", "..");
            Reject(package, ".lake/../../../outside", "..");
            Reject(package, "..", "..");
            Reject(package, Path.Combine(outside, "Secret.lean"), "an absolute path");
            Reject(package, outside, "an absolute path");
            Require(Within(package, "Missing/Module.lean") == Path.Combine(package, "Missing", "Module.lean") &&
                Within(package, ".") == package, "A path inside its package was not returned as spelled under it.");
            Console.WriteLine("PASS a package path that leaves through .. or an absolute path is rejected");

            // Lake reports its directories with links followed, as macOS reaches /var through /private/var.
            var link = Path.Combine(work, "link");
            if (!TryLinkDirectory(link, real))
            {
                Console.WriteLine("SKIP package paths through links: no directory link or junction could be made");
                return;
            }
            var linkedPackage = Path.Combine(link, "package");
            var linkedBuilt = Path.Combine(linkedPackage, ".lake", "packages", "generated", "lib");
            Require(Within(linkedPackage, Path.GetRelativePath(linkedPackage, built)) == linkedBuilt &&
                Within(linkedPackage, built) == linkedBuilt && Within(package, linkedBuilt) == built,
                "A package reached through a directory link rejected or respelled its own directory.");
            Require(ResolvedRelativePath(linkedPackage, built) == Path.Combine(".lake", "packages", "generated", "lib"),
                "A directory reached through a link was not found inside its package.");
            Reject(linkedPackage, Path.GetRelativePath(linkedPackage, outside), "..");
            Reject(linkedPackage, Path.Combine(link, "..", "outside"), "an absolute path");
            Console.WriteLine("PASS a package reached through a directory link holds its own directories");

            // Lean reports an audited module with links followed; the check still names one file.
            var olean = Path.Combine(built, "Proof.olean");
            var shadow = Path.Combine(outside, "Proof.olean");
            File.WriteAllText(olean, "");
            File.WriteAllText(shadow, "");
            AuditedOleans Audited(string path) => new(new() { ["Proof"] = path }, [], []);
            RequireAuditedModule(Audited(olean), "Proof", Path.Combine(linkedBuilt, "Proof.olean"));
            RequireAuditedModule(Audited(Path.Combine(linkedBuilt, "Proof.olean")), "Proof", olean);
            try
            {
                RequireAuditedModule(Audited(shadow), "Proof", Path.Combine(linkedBuilt, "Proof.olean"));
                throw new Exception("An audited module elsewhere was taken for the checked one.");
            }
            catch (InvalidDataException) { }
            Console.WriteLine("PASS an audited module reached through a link is the checked file, and a shadow is not");

            var escape = Path.Combine(package, "escape");
            Require(TryLinkDirectory(escape, outside), "Could not link a package directory outside the package.");
            Reject(package, "escape/Secret.lean", "a link");
            Reject(package, "escape", "a link");
            Reject(package, "escape/New/Module.lean", "a link");
            Reject(linkedPackage, "escape/Secret.lean", "a link");
            Require(ResolvedRelativePath(outside, Path.Combine(package, "escape", "Secret.lean")) == "Secret.lean",
                "A location inside a directory reached through a link was not found inside it.");
            // A dangling link still names where a write through it would land.
            var gone = Path.Combine(work, "gone");
            Directory.CreateDirectory(gone);
            var dangling = Path.Combine(package, "dangling");
            Require(TryLinkDirectory(dangling, gone), "Could not link a package directory outside the package.");
            Directory.Delete(gone);
            Reject(package, "dangling", "a dangling link");
            Reject(package, "dangling/New.lean", "a dangling link");
            var alias = Path.Combine(package, "alias");
            Require(TryLinkDirectory(alias, Path.Combine(package, ".lake")), "Could not link inside the package.");
            Require(Within(package, "alias/packages") == Path.Combine(package, ".lake", "packages"),
                "A link that stays inside its package was rejected or not followed.");
            Console.WriteLine("PASS a link inside a package that leaves it is rejected, also when dangling");

            var first = Path.Combine(package, "first");
            var second = Path.Combine(package, "second");
            Require(TryLinkDirectory(first, second) && TryLinkDirectory(second, first),
                "Could not make a cycle of directory links.");
            Reject(package, "first/Module.lean", "a cycle of links");
            Console.WriteLine("PASS a cycle of links is rejected");
        }
        // A recursive delete removes a link without entering the directory it names.
        finally { Directory.Delete(work, true); }
    }
}
