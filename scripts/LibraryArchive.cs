#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CertifiedLibraryArchive.cs
#:include CertifiedLibraryDonor.cs

switch (args)
{
    case ["pack", var source, var archive, var manifest]:
        var digest = CertifiedLibraryArchive.Pack(source, archive, manifest);
        Console.WriteLine(CertifiedLibraryDonor.ArchiveDigestLine + digest);
        if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } output)
            File.AppendAllText(output, "archive-sha256=" + digest + "\n");
        break;
    case ["restore", var download, var destination, var manifest, var archiveDigest]:
        CertifiedLibraryArchive.Restore(download, destination, manifest, archiveDigest);
        break;
    default:
        throw new ArgumentException("Usage: LibraryArchive.cs pack <source> <archive> <manifest-sha256> | " +
            "restore <download> <destination> <manifest-sha256> <archive-sha256-or-empty>");
}
