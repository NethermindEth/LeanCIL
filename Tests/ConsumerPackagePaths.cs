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

            // A case variant is one location only where the file system says so; no sibling exists to confuse it.
            var variant = Path.Combine(real, "PACKAGE");
            var sameUnderCase = Directory.Exists(variant);
            Require(SameLocation(package, variant) == sameUnderCase &&
                Inside(package, Path.Combine(variant, ".lake")) == sameUnderCase &&
                new[] { package, variant }.Select(ResolvedPath).Distinct(LocationComparer).Count() ==
                    (sameUnderCase ? 1 : 2),
                $"A case variant of a directory was judged {(sameUnderCase ? "another" : "the same")} location.");
            Console.WriteLine("PASS a case variant of a directory is " +
                (sameUnderCase ? "the same location" : "another location"));
            Require(NameCaseIn(real) == (sameUnderCase ? NameCase.Insensitive : NameCase.Sensitive) &&
                NameCaseIn(Path.Combine(real, "missing", "deeper")) == NameCaseIn(real),
                "The probe read another case rule than the temporary volume follows.");
            // macOS reports the case rule of every volume; Windows and Linux report only a flag that decides it.
            var queried = QueriedNameCase(real);
            Require(queried == NameCaseIn(real) || queried is null && !OperatingSystem.IsMacOS(),
                $"The operating system reported {queried} for the temporary volume.");
            Console.WriteLine("PASS the probe reads the case rule of the temporary volume");

            CheckNameCaseRule(work, Require);
            CheckCaseSensitiveVolume(Path.Combine(work, "sensitive"), Require, Reject);

            // Lake reports its directories with links followed, as macOS reaches /var through /private/var.
            var link = Path.Combine(work, "link");
            if (!TryLinkDirectory(link, real))
            {
                // Every Unix user can make a symbolic link, so only Windows may lack both kinds of link.
                if (!OperatingSystem.IsWindows()) throw new Exception("Could not make a directory symbolic link.");
                Console.WriteLine("SKIP package paths through links: no directory link or junction could be made");
                return;
            }
            var linkedPackage = Path.Combine(link, "package");
            var linkedBuilt = Path.Combine(linkedPackage, ".lake", "packages", "generated", "lib");
            Require(Within(linkedPackage, Path.GetRelativePath(linkedPackage, built)) == linkedBuilt &&
                Within(linkedPackage, built) == linkedBuilt && Within(package, linkedBuilt) == built,
                "A package reached through a directory link rejected or respelled its own directory.");
            var builtRelative = Path.Combine(".lake", "packages", "generated", "lib");
            Require(ResolvedRelativePath(linkedPackage, built) == builtRelative,
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
            Console.WriteLine("PASS an audited module reached through a link is the checked file; a shadow is not");

            // Guards that keep an output out of an input decide on the location, not the spelling.
            Require(Inside(linkedPackage, olean) && Inside(package, Path.Combine(linkedBuilt, "Proof.olean")) &&
                !Inside(linkedPackage, shadow) && SameLocation(linkedPackage, package) &&
                !SameLocation(linkedBuilt, outside), "A location reached through a link was judged by its spelling.");
            Require(CompiledName([ResolvedPath(linkedBuilt)], ResolvedPath(olean)) == "Proof.olean" &&
                CompiledName([ResolvedPath(linkedBuilt)], ResolvedPath(shadow)) is null &&
                CompiledName([ResolvedPath(linkedBuilt)], ResolvedPath(linkedBuilt)) is null,
                "A compiled module reached through a link was not named, or a file elsewhere was.");
            Console.WriteLine("PASS containment and identity of locations reached through a link");

            var escape = Path.Combine(package, "escape");
            Require(TryLinkDirectory(escape, outside), "Could not link a package directory outside the package.");
            Reject(package, "escape/Secret.lean", "a link");
            Reject(package, "escape", "a link");
            Reject(package, "escape/New/Module.lean", "a link");
            Reject(linkedPackage, "escape/Secret.lean", "a link");
            Require(ResolvedRelativePath(outside, Path.Combine(package, "escape", "Secret.lean")) == "Secret.lean",
                "A location inside a directory reached through a link was not found inside it.");
            var source = Path.Combine(linkedPackage, "escape", "Secret.lean");
            var blocked = ConsumerSourceLocations(new(StringComparer.Ordinal)
            {
                ["consumer:" + source] = "", ["revision:leancil"] = ""
            });
            Require(blocked.Contains(ResolvedPath(source)) && blocked.Contains(ResolvedPath(outside)) &&
                blocked.Contains(ResolvedPath(work)) && !blocked.Contains(ResolvedPath(linkedPackage)) &&
                !blocked.Contains(ResolvedPath(Path.Combine(outside, "Other.lean"))),
                "Batch output overlap changed for a source reached through two directory links.");
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
            // POSIX reads `..` where a link leads and Windows where it is spelled; a path both place inside stays.
            Reject(package, "escape/../outside/Secret.lean", "a link followed by ..");
            Require(Within(package, "alias/../.lake") == Path.Combine(package, ".lake"),
                "A path whose .. after a link stays inside its package under both readings was rejected.");
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

    /// <summary>
    /// Paths compared under a case rule given per directory: a name is matched by the rule of the directory that
    /// holds it, so a case-sensitive volume mounted inside one that ignores case is judged at each level.
    /// </summary>
    static void CheckNameCaseRule(string work, Action<bool, string> require)
    {
        var volume = Path.Combine(work, "volume");
        var package = Path.Combine(volume, "package");
        var sibling = Path.Combine(volume, "Package", "Module.lean");
        var asked = new HashSet<string>(StringComparer.Ordinal);
        Func<string, NameCase> Every(NameCase rule) => directory => { asked.Add(directory); return rule; };
        require(RelativeBelow(package, sibling, Every(NameCase.Sensitive)) is null &&
            RelativeBelow(package, sibling, Every(NameCase.Insensitive)) == "Module.lean" &&
            asked.SetEquals([volume]) && RelativeBelow(package, package, Every(NameCase.Sensitive)) == ".",
            "A name differing only in case was not decided by the rule of the directory holding it.");
        // `work` ignores case and `volume` tells it apart, as a disk image mounted in a temporary directory.
        Func<string, NameCase> mounted = directory => directory == work ? NameCase.Insensitive : NameCase.Sensitive;
        var respelled = Path.Combine(work, "VOLUME", "package", "Module.lean");
        require(RelativeBelow(package, respelled, mounted) == "Module.lean" &&
            RelativeBelow(package, sibling, mounted) is null,
            "A path crossing volumes with different case rules was judged by one rule.");
        LocationEquality sensitive = new(Every(NameCase.Sensitive), unknownMatches: true);
        LocationEquality insensitive = new(Every(NameCase.Insensitive), unknownMatches: false);
        var upper = Path.Combine(volume, "PACKAGE");
        require(!sensitive.Equals(package, upper) && insensitive.Equals(package, upper) &&
            insensitive.GetHashCode(package) == insensitive.GetHashCode(upper) &&
            new HashSet<string>([package, upper], insensitive).Count == 1 &&
            new HashSet<string>([package, upper], sensitive).Count == 2,
            "Locations differing only in case were compared against the given rule.");
        // An unknown rule never admits a path into a package, and keeps two outputs apart as if they collided.
        LocationEquality known = new(Every(NameCase.Unknown), unknownMatches: false);
        LocationEquality colliding = new(Every(NameCase.Unknown), unknownMatches: true);
        require(RelativeBelow(package, sibling, Every(NameCase.Unknown)) is null &&
            RelativeBelow(package, sibling, Every(NameCase.Unknown), unknownMatches: true) == "Module.lean" &&
            !known.Equals(package, upper) && colliding.Equals(package, upper) &&
            new HashSet<string>([package, upper], colliding).Count == 1,
            "A name in another case under an unknown rule was admitted, or two outputs were not kept apart.");
        Console.WriteLine("PASS paths are compared under the case rule of each directory that holds a name");
    }

    /// <summary>
    /// Containment and identity on a volume that tells case apart, where a sibling whose name differs only in case
    /// is another directory. The volume is made without privileges: a disk image on macOS, a directory with the
    /// case-sensitive flag on Windows, and the temporary directory itself on Linux.
    /// </summary>
    static void CheckCaseSensitiveVolume(string directory, Action<bool, string> require,
        Action<string, string, string> reject)
    {
        // Asked before it exists, the directory takes the rule of the volume it would be made on.
        var before = NameCaseIn(directory);
        require(before == NameCaseIn(Path.GetDirectoryName(directory)!),
            "A missing directory did not take the rule of its nearest existing ancestor.");
        if (CaseSensitiveDirectory(directory) is not { } removeVolume) return;
        try
        {
            var package = Path.Combine(directory, "package");
            var sibling = Path.Combine(directory, "Package");
            Directory.CreateDirectory(Path.Combine(package, ".lake"));
            Directory.CreateDirectory(sibling);
            File.WriteAllText(Path.Combine(sibling, "Secret.lean"), "-- beside the package\n");
            require(!Directory.Exists(Path.Combine(directory, "PACKAGE")),
                "The case-sensitive volume found a directory under a name no entry has.");
            reject(package, Path.Combine(sibling, "Secret.lean"), "a sibling named in another case");
            reject(package, "../Package/Secret.lean", "a sibling named in another case");
            reject(package, Path.Combine(directory, "PACKAGE", "New.lean"),
                "a missing directory named in another case");
            File.WriteAllText(Path.Combine(sibling, "Fixture.cs"), "");
            var checkout = Root;
            Root = package;
            try
            {
                FixtureInputs("../Package/Fixture.cs");
                throw new Exception("A fixture input in a sibling named in another case was taken as checked out.");
            }
            catch (InvalidOperationException) { }
            finally { Root = checkout; }
            require(!SameLocation(package, sibling) && !Inside(package, Path.Combine(sibling, "Secret.lean")) &&
                Inside(package, Path.Combine(package, ".lake")) &&
                new[] { package, sibling }.Select(ResolvedPath).Distinct(LocationComparer).Count() == 2,
                "A sibling whose name differs only in case was judged the package's location.");
            // The answer given before the volume existed is not reused for it.
            require(NameCaseIn(directory) == NameCase.Sensitive &&
                NameCaseIn(Path.Combine(directory, "missing", "deeper")) == NameCase.Sensitive,
                "A case-sensitive volume was read as ignoring case, or given an answer from before it existed.");
            require(OperatingSystem.IsLinux() ? QueriedNameCase(directory) is null
                    : QueriedNameCase(directory) == NameCase.Sensitive,
                $"The operating system reported {QueriedNameCase(directory)} for a case-sensitive volume.");
            // Both spellings of one name are listed, so neither shows the rule; the other entry does.
            require(EntryNameCase(directory) == NameCase.Sensitive,
                "The entries of a directory holding both spellings of a name were read as ignoring case.");
            var pair = Path.Combine(directory, "pair");
            Directory.CreateDirectory(Path.Combine(pair, "name"));
            Directory.CreateDirectory(Path.Combine(pair, "NAME"));
            var empty = Path.Combine(directory, "empty");
            Directory.CreateDirectory(empty);
            require(EntryNameCase(pair) == NameCase.Unknown && EntryNameCase(empty) == NameCase.Unknown,
                "Entries that cannot show the case rule were read as showing one.");
            // An unknown rule is never kept: the directory is asked again once an entry can show it.
            var firstAnswer = NameCaseIn(empty);
            require(firstAnswer == (QueriedNameCase(empty) ?? NameCase.Unknown),
                $"A directory whose entries show no rule was given {firstAnswer}.");
            Directory.CreateDirectory(Path.Combine(empty, "probe"));
            require(NameCaseIn(empty) == NameCase.Sensitive,
                "An unknown case rule was kept after the directory gained an entry that shows it.");
            reject(Path.Combine(pair, "name"), Path.Combine(pair, "NAME", "Module.lean"),
                "a sibling named in another case where the entries show no rule");
            Console.WriteLine(
                "PASS on a case-sensitive volume a sibling named in another case lies outside the package");
        }
        finally { removeVolume(); }
    }

    /// <summary>
    /// Makes `directory` on a volume that tells case apart and returns how to remove it, or null after printing SKIP
    /// where Windows refuses the flag or the Linux temporary directory ignores case. macOS always can, so a failure
    /// there throws.
    /// </summary>
    static Action? CaseSensitiveDirectory(string directory)
    {
        var parent = Path.GetDirectoryName(directory)!;
        if (OperatingSystem.IsMacOS())
        {
            var image = directory + ".dmg";
            Run(["hdiutil", "create", "-size", "16m", "-fs", "Case-sensitive APFS", "-volname", "leancil-case",
                "-type", "UDIF", image], parent);
            Directory.CreateDirectory(directory);
            Run(["hdiutil", "attach", "-nobrowse", "-noautoopen", "-mountpoint", directory, image], parent);
            return () => Run(["hdiutil", "detach", "-force", directory], parent);
        }
        Directory.CreateDirectory(directory);
        if (OperatingSystem.IsWindows())
        {
            var flag = Execute(["fsutil.exe", "file", "setCaseSensitiveInfo", directory, "enable"], parent);
            if (flag.Code == 0) return () => { };
            Console.WriteLine("SKIP case-sensitive volume: fsutil could not mark a directory: " + flag.Output.Trim());
            return null;
        }
        Directory.CreateDirectory(Path.Combine(directory, "probe"));
        if (!Directory.Exists(Path.Combine(directory, "PROBE"))) return () => { };
        Console.WriteLine("SKIP case-sensitive volume: the temporary directory ignores case");
        return null;
    }
}
