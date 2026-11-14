partial class Program
{
    static void CheckConsumerImportDirectories(string[] args)
    {
        var root = Path.Combine(Path.GetTempPath(), "leancil-import-directories-" + Guid.NewGuid().ToString("N"));
        var physical = Path.Combine(root, "physical");
        var alias = Path.Combine(root, "alias");
        var session = Path.Combine(alias, "session");
        var physicalSession = Path.Combine(physical, "session");
        var trusted = Path.Combine(alias, "toolchain");
        var certified = Path.Combine(alias, "certified");
        Directory.CreateDirectory(physicalSession);
        Directory.CreateDirectory(Path.Combine(physical, "toolchain"));
        Directory.CreateDirectory(Path.Combine(physical, "certified"));
        Directory.CreateDirectory(Path.Combine(physical, "session-sibling"));
        var links = new List<string>();
        void Link(string path, string target)
        {
            Directory.CreateSymbolicLink(path, target);
            links.Add(path);
        }
        try
        {
            Link(alias, "physical");
            string[] Validate(params string[] paths) =>
                ValidatedConsumerImportDirectories(
                    session, trusted, certified, string.Join(Path.PathSeparator, paths));
            void Require(string[] actual, params string[] expected)
            {
                if (!actual.SequenceEqual(expected))
                    throw new InvalidOperationException("Unexpected import directories: " + string.Join(", ", actual));
            }
            void Reject(string path)
            {
                try { Validate(path); }
                catch (InvalidDataException) { return; }
                throw new InvalidOperationException("Accepted outside or unresolved import directory: " + path);
            }
            var build = Path.Combine(".lake", "build", "lib", "lean");
            Require(Validate(build), Path.Combine(session, build));
            Require(Validate(Path.Combine(physicalSession, build), Path.Combine(session, build)),
                Path.Combine(session, build));
            Require(Validate(trusted, Path.Combine(physical, "toolchain"), certified,
                Path.Combine(physical, "certified")), certified);
            var nested = Path.Combine(physicalSession, "nested");
            Directory.CreateDirectory(nested);
            Link(Path.Combine(physicalSession, "inside"), nested);
            Require(Validate(Path.Combine(session, "inside", "..", build)), Path.Combine(session, build));
            Reject(Path.Combine(physical, "session-sibling"));
            Reject(Path.Combine("..", "session-sibling"));
            Reject(Path.Combine(trusted, "outside"));
            Reject(Path.Combine(certified, "outside"));
            Link(Path.Combine(physicalSession, "escape"), Path.Combine(physical, "session-sibling"));
            Reject(Path.Combine(session, "escape"));
            // Parent traversal follows the symbolic link before resolving its parent directory.
            Reject(Path.Combine(session, "escape", "..", "certified", "outside"));
            Link(Path.Combine(physicalSession, "cycle"), Path.Combine(physicalSession, "cycle"));
            Reject(Path.Combine(session, "cycle"));
            Link(Path.Combine(physicalSession, "dangling"), Path.Combine(physical, "missing"));
            Reject(Path.Combine(session, "dangling"));
            var module = Path.Combine(physicalSession, "Proof.olean");
            File.WriteAllText(module, "artifact");
            AuditedOleans audited = new(new() { ["Proof"] = module }, [], []);
            RequireAuditedModule(audited, "Proof", Path.Combine(session, "Proof.olean"));
            RequireAuditedModule(audited, "Proof", Path.Combine(session, "inside", "..", "Proof.olean"));
            void RejectArtifact(string expected)
            {
                try { RequireAuditedModule(audited, "Proof", expected); }
                catch (InvalidDataException) { return; }
                throw new InvalidOperationException("Accepted different audited artifact: " + expected);
            }
            var siblingModule = Path.Combine(physical, "session-sibling", "Proof.olean");
            File.WriteAllText(siblingModule, "artifact");
            RejectArtifact(siblingModule);
            var renamedModule = Path.Combine(physicalSession, "Other.olean");
            File.WriteAllText(renamedModule, "artifact");
            RejectArtifact(renamedModule);
            try
            {
                RequireAuditedModule(audited, "Missing", module);
                throw new InvalidOperationException("Accepted missing audited module.");
            }
            catch (KeyNotFoundException) { }
            Console.WriteLine("PASS consumer import directory aliases and containment");
        }
        finally
        {
            foreach (var link in links.AsEnumerable().Reverse())
            {
                if (OperatingSystem.IsWindows()) Directory.Delete(link);
                else File.Delete(link);
            }
            Directory.Delete(root, true);
        }
    }
}
