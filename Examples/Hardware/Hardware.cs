#:property OutputType=Library
#:property AssemblyName=Examples.Hardware
#:property Version=1.0.0
#:property PublishAot=false

using System.Runtime.Intrinsics.X86;

namespace Examples;

static class Hardware
{
    public static bool Available() => Avx2.IsSupported;
}
