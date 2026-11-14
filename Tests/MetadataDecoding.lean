import CIL.Extraction.Signatures

/-!
# Metadata table and heap decoding tests

The vectors are rows, header bytes and heap entries copied from `Examples.dll` (two-byte
columns) and from `System.Private.CoreLib.dll` (four-byte string, blob and coded columns), with
the major version of each assembly row set to the platform version 11, together with the values
`System.Reflection.Metadata` reads from the same positions and the assembly names Mono.Cecil
spells. Each rejection changes one fact of a slice that
decodes and asserts the exact error.
-/

namespace Tests.MetadataDecoding

open CIL.Extraction

/-! ## Vectors read from the images -/

def examplesHeader : List Nat := [0, 0, 0, 0, 2, 0, 0, 1, 87, 223, 163, 43, 9, 30, 0, 0, 0, 250,
  1, 51, 0, 22, 0, 0, 1, 0, 0, 0, 106, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 248, 4, 0, 0, 191, 6,
  0, 0, 43, 0, 0, 0, 37, 2, 0, 0, 26, 0, 0, 0, 50, 1, 0, 0, 1, 0, 0, 0, 31, 0, 0, 0, 13, 0, 0, 0,
  111, 0, 0, 0, 20, 0, 0, 0, 31, 0, 0, 0, 34, 0, 0, 0, 28, 0, 0, 0, 85, 0, 0, 0, 3, 0, 0, 0, 1, 0,
  0, 0, 4, 0, 0, 0, 27, 0, 0, 0, 76, 0, 0, 0, 60, 1, 0, 0, 88, 0, 0, 0]
def examplesRowSizes : List (Nat × Nat) := [(1, 6), (2, 14), (4, 6), (6, 14), (10, 6), (17, 2),
  (27, 2), (32, 22), (35, 20), (41, 4), (42, 8), (43, 4)]
def examplesAssemblyRow : List Nat := [4, 128, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
  52, 0, 0]
def examplesRows : List (Nat × List Nat) := [(16777217, [6, 0, 57, 28, 12, 51]), (16777218, [6, 0,
  235, 28, 12, 51]), (16777219, [6, 0, 177, 26, 92, 50]), (33554433, [0, 0, 0, 0, 228, 11, 0, 0,
  0, 0, 1, 0, 1, 0]), (33554434, [128, 1, 16, 0, 3, 44, 14, 46, 77, 0, 1, 0, 1, 0]), (33554435,
  [128, 1, 16, 0, 3, 44, 232, 23, 77, 0, 1, 0, 2, 0]), (33554436, [128, 1, 16, 0, 37, 57, 9, 52,
  77, 0, 1, 0, 5, 0]), (67108865, [6, 0, 220, 55, 68, 18]), (67108866, [6, 0, 37, 52, 74, 18]),
  (100663297, [80, 32, 0, 0, 0, 0, 150, 0, 111, 14, 52, 10, 1, 0]), (100663298, [85, 32, 0, 0, 0,
  0, 150, 0, 111, 14, 52, 10, 3, 0]), (100663299, [90, 32, 0, 0, 0, 0, 150, 0, 111, 14, 26, 10, 5,
  0]), (167772161, [9, 0, 6, 49, 1, 0]), (167772162, [17, 0, 6, 49, 6, 0]), (167772163, [25, 0, 6,
  49, 10, 0]), (285212673, [60, 1]), (452984833, [50, 0]), (587202561, [11, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 77, 17, 217, 23, 0, 0, 0, 0]), (587202562, [11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86,
  17, 47, 50, 0, 0, 0, 0]), (687865857, [201, 0, 4, 0]), (704643073, [0, 0, 0, 0, 36, 0, 105,
  12]), (721420289, [83, 0, 255, 0])]
def examplesStrings : List (Nat × List Nat) := [(0, [0]), (3044, [60, 77, 111, 100, 117, 108, 101,
  62, 0]), (3177, [84, 0]), (3695, [65, 100, 100, 0]), (6105, [83, 121, 115, 116, 101, 109, 46,
  82, 117, 110, 116, 105, 109, 101, 0]), (6120, [83, 101, 108, 101, 99, 116, 111, 114, 69, 120,
  97, 109, 112, 108, 101, 115, 46, 79, 110, 101, 0]), (6833, [68, 101, 98, 117, 103, 103, 97, 98,
  108, 101, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]), (7225, [67, 111, 109, 112, 105, 108,
  97, 116, 105, 111, 110, 82, 101, 108, 97, 120, 97, 116, 105, 111, 110, 115, 65, 116, 116, 114,
  105, 98, 117, 116, 101, 0]), (7403, [82, 117, 110, 116, 105, 109, 101, 67, 111, 109, 112, 97,
  116, 105, 98, 105, 108, 105, 116, 121, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]), (11267,
  [67, 111, 108, 108, 105, 115, 105, 111, 110, 0]), (11790, [83, 101, 108, 101, 99, 116, 111, 114,
  69, 120, 97, 109, 112, 108, 101, 115, 46, 84, 119, 111, 0]), (12550, [46, 99, 116, 111, 114,
  0]), (12847, [83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 46, 73, 110,
  116, 114, 105, 110, 115, 105, 99, 115, 0]), (12892, [83, 121, 115, 116, 101, 109, 46, 68, 105,
  97, 103, 110, 111, 115, 116, 105, 99, 115, 0]), (13068, [83, 121, 115, 116, 101, 109, 46, 82,
  117, 110, 116, 105, 109, 101, 46, 67, 111, 109, 112, 105, 108, 101, 114, 83, 101, 114, 118, 105,
  99, 101, 115, 0]), (13321, [69, 120, 97, 109, 112, 108, 101, 115, 0]), (13349, [76, 97, 110,
  101, 115, 0]), (14300, [80, 97, 105, 114, 115, 0]), (14629, [65, 103, 103, 114, 101, 103, 97,
  116, 101, 65, 114, 114, 97, 121, 115, 0])]
def examplesStringText : List (Nat × String) := [(0, ""), (3044, "\u003CModule\u003E"), (3177,
  "T"), (3695, "Add"), (6105, "System.Runtime"), (6120, "SelectorExamples.One"), (6833,
  "DebuggableAttribute"), (7225, "CompilationRelaxationsAttribute"), (7403,
  "RuntimeCompatibilityAttribute"), (11267, "Collision"), (11790, "SelectorExamples.Two"), (12550,
  ".ctor"), (12847, "System.Runtime.Intrinsics"), (12892, "System.Diagnostics"), (13068,
  "System.Runtime.CompilerServices"), (13321, "Examples"), (13349, "Lanes"), (14300, "Pairs"),
  (14629, "AggregateArrays")]
def examplesBlobs : List (Nat × List Nat) := [(0, [0]), (1, [4, 32, 1, 1, 8]), (6, [3, 32, 0, 1]),
  (10, [5, 32, 1, 1, 17, 17]), (50, [5, 21, 18, 72, 1, 8]), (255, [5, 10, 1, 17, 131, 36]), (316,
  [9, 7, 1, 21, 17, 89, 1, 17, 131, 36]), (2586, [5, 0, 2, 9, 9, 9]), (2612, [5, 0, 2, 11, 11,
  11]), (4429, [8, 176, 63, 95, 127, 17, 213, 10, 58]), (4438, [8, 204, 123, 19, 255, 205, 45,
  221, 81]), (4676, [5, 6, 29, 17, 131, 36]), (4682, [7, 6, 29, 21, 17, 97, 1, 11])]
def examplesBlobPayloads : List (Nat × List Nat) := [(0, []), (1, [32, 1, 1, 8]), (6, [32, 0, 1]),
  (10, [32, 1, 1, 17, 17]), (50, [21, 18, 72, 1, 8]), (255, [10, 1, 17, 131, 36]), (316, [7, 1,
  21, 17, 89, 1, 17, 131, 36]), (2586, [0, 2, 9, 9, 9]), (2612, [0, 2, 11, 11, 11]), (4429, [176,
  63, 95, 127, 17, 213, 10, 58]), (4438, [204, 123, 19, 255, 205, 45, 221, 81]), (4676, [6, 29,
  17, 131, 36]), (4682, [6, 29, 21, 17, 97, 1, 11])]
def examplesExpected : List (Nat × List Nat) := [(16777217, [587202561, 7225, 13068]), (16777218,
  [587202561, 7403, 13068]), (16777219, [587202561, 6833, 12892]), (67108865, [6, 14300, 4676]),
  (67108866, [6, 13349, 4682]), (100663297, [8272, 0, 150, 3695, 2612]), (100663298, [8277, 0,
  150, 3695, 2612]), (100663299, [8282, 0, 150, 3695, 2586]), (167772161, [16777217, 12550, 1]),
  (167772162, [16777218, 12550, 6]), (167772163, [16777219, 12550, 10]), (285212673, [316]),
  (452984833, [50]), (587202561, [11, 0, 0, 0, 0, 4429, 6105, 0]), (587202562, [11, 0, 0, 0, 0,
  4438, 12847, 0]), (687865857, [33554633, 33554436]), (704643073, [0, 0, 33554450, 3177]),
  (721420289, [167772201, 255])]
def examplesUserStrings : List (Nat × List Nat) := [(1, [11, 118, 0, 97, 0, 108, 0, 117, 0, 101,
  0, 0]), (13, [11, 99, 0, 111, 0, 117, 0, 110, 0, 116, 0, 0]), (25, [11, 105, 0, 110, 0, 100, 0,
  101, 0, 120, 0, 0]), (37, [11, 108, 0, 97, 0, 98, 0, 101, 0, 108, 0, 0]), (49, [17, 99, 0, 97,
  0, 112, 0, 97, 0, 99, 0, 105, 0, 116, 0, 121, 0, 0]), (67, [45, 84, 0, 104, 0, 101, 0, 32, 0,
  112, 0, 111, 0, 111, 0, 108, 0, 32, 0, 105, 0, 115, 0, 32, 0, 101, 0, 120, 0, 104, 0, 97, 0,
  117, 0, 115, 0, 116, 0, 101, 0, 100, 0, 46, 0, 0])]
def examplesUserUnits : List (Nat × List Nat) := [(1, [118, 97, 108, 117, 101]), (13, [99, 111,
  117, 110, 116]), (25, [105, 110, 100, 101, 120]), (37, [108, 97, 98, 101, 108]), (49, [99, 97,
  112, 97, 99, 105, 116, 121]), (67, [84, 104, 101, 32, 112, 111, 111, 108, 32, 105, 115, 32, 101,
  120, 104, 97, 117, 115, 116, 101, 100, 46])]
def examplesIdentity : String := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
def examplesRefIdentities : List String := [
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a",
  "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51",
  "System.Memory, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51",
  "System.Security.Cryptography, Version=11.0.0.0, Culture=neutral, " ++
    "PublicKeyToken=b03f5f7f11d50a3a"]

def corelibHeader : List Nat := [0, 0, 0, 0, 2, 0, 5, 10, 85, 191, 183, 63, 1, 31, 0, 0, 0, 250,
  1, 51, 0, 22, 196, 0, 1, 0, 0, 0, 83, 11, 0, 0, 253, 37, 0, 0, 136, 165, 0, 0, 156, 11, 1, 0,
  132, 8, 0, 0, 147, 32, 0, 0, 166, 14, 0, 0, 75, 108, 0, 0, 1, 1, 0, 0, 164, 0, 0, 0, 143, 0, 0,
  0, 214, 14, 0, 0, 12, 0, 0, 0, 32, 0, 0, 0, 53, 4, 0, 0, 205, 21, 0, 0, 246, 23, 0, 0, 69, 16,
  0, 0, 15, 0, 0, 0, 237, 8, 0, 0, 140, 2, 0, 0, 193, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 249, 3, 0,
  0, 76, 16, 0, 0, 143, 19, 0, 0, 192, 7, 0, 0]
def corelibRowSizes : List (Nat × Nat) := [(1, 10), (2, 18), (4, 10), (6, 20), (10, 12), (17, 4),
  (27, 4), (32, 28), (35, 28), (41, 4), (42, 12), (43, 8)]
def corelibAssemblyRow : List Nat := [4, 128, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
  0, 130, 95, 1, 0, 0, 0, 0, 0]
def corelibRows : List (Nat × List Nat) := [(33554932, [0, 1, 0, 0, 102, 86, 7, 0, 128, 9, 5, 0,
  44, 2, 37, 7, 66, 38]), (33556432, [0, 1, 16, 0, 139, 153, 8, 0, 153, 155, 5, 0, 148, 2, 53, 23,
  137, 132]), (33556932, [8, 1, 16, 0, 79, 247, 2, 0, 204, 13, 4, 0, 60, 3, 231, 33, 37, 156]),
  (67108869, [86, 128, 124, 193, 6, 0, 34, 24, 0, 0]), (67117864, [17, 0, 48, 78, 2, 0, 57, 228,
  5, 0]), (100663326, [0, 0, 0, 0, 128, 0, 147, 32, 184, 2, 4, 0, 3, 10, 0, 0, 81, 0, 0, 0]),
  (100684296, [52, 93, 147, 0, 0, 1, 150, 0, 245, 180, 8, 0, 35, 55, 3, 0, 226, 125, 0, 0]),
  (100705672, [168, 135, 157, 0, 0, 0, 147, 0, 125, 6, 4, 0, 246, 126, 4, 0, 156, 11, 1, 0]),
  (167775160, [68, 27, 0, 0, 158, 136, 0, 0, 163, 0, 0, 0]), (167780499, [156, 70, 0, 0, 132, 210,
  6, 0, 100, 136, 1, 0]), (285214672, [223, 145, 2, 0]), (452984932, [171, 105, 0, 0]),
  (452987117, [127, 33, 6, 0]), (687865906, [53, 0, 51, 0]), (704643172, [9, 0, 34, 0, 202, 1, 0,
  0, 189, 1, 0, 0]), (704647244, [1, 0, 0, 0, 17, 75, 1, 0, 140, 10, 8, 0]), (721420338, [98, 25,
  0, 0, 88, 48, 0, 0]), (721425295, [104, 247, 0, 0, 190, 84, 0, 0])]
def corelibStrings : List (Nat × List Nat) := [(0, [0]), (445, [84, 49, 48, 0]), (34974, [73, 116,
  101, 109, 49, 0]), (89986, [83, 121, 115, 116, 101, 109, 46, 80, 114, 105, 118, 97, 116, 101,
  46, 67, 111, 114, 101, 76, 105, 98, 0]), (151088, [115, 95, 105, 110, 115, 116, 97, 110, 99,
  101, 0]), (194383, [77, 97, 110, 105, 102, 101, 115, 116, 69, 110, 118, 101, 108, 111, 112, 101,
  0]), (262840, [73, 110, 100, 101, 120, 79, 102, 0]), (263805, [73, 110, 108, 105, 110, 101, 65,
  114, 114, 97, 121, 70, 105, 114, 115, 116, 69, 108, 101, 109, 101, 110, 116, 82, 101, 102, 0]),
  (265676, [83, 121, 115, 116, 101, 109, 46, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115,
  46, 84, 114, 97, 99, 105, 110, 103, 0]), (330112, [83, 121, 115, 116, 101, 109, 0]), (367513,
  [83, 121, 115, 116, 101, 109, 46, 82, 101, 102, 108, 101, 99, 116, 105, 111, 110, 0]), (442748,
  [85, 110, 107, 110, 111, 119, 110, 69, 114, 114, 111, 114, 0]), (447108, [46, 99, 116, 111, 114,
  0]), (480870, [84, 105, 109, 101, 90, 111, 110, 101, 73, 110, 102, 111, 79, 112, 116, 105, 111,
  110, 115, 0]), (526988, [84, 69, 108, 101, 109, 101, 110, 116, 0]), (563595, [76, 111, 97, 100,
  101, 114, 65, 108, 108, 111, 99, 97, 116, 111, 114, 83, 99, 111, 117, 116, 0]), (570613, [78,
  97, 114, 114, 111, 119, 0])]
def corelibStringText : List (Nat × String) := [(0, ""), (445, "T10"), (34974, "Item1"), (89986,
  "System.Private.CoreLib"), (151088, "s_instance"), (194383, "ManifestEnvelope"), (262840,
  "IndexOf"), (263805, "InlineArrayFirstElementRef"), (265676, "System.Diagnostics.Tracing"),
  (330112, "System"), (367513, "System.Reflection"), (442748, "UnknownError"), (447108, ".ctor"),
  (480870, "TimeZoneInfoOptions"), (526988, "TElement"), (563595, "LoaderAllocatorScout"),
  (570613, "Narrow")]
def corelibBlobs : List (Nat × List Nat) := [(1, [128, 160, 0, 36, 0, 0, 4, 128, 0, 0, 148, 0, 0,
  0, 6, 2, 0, 0, 0, 36, 0, 0, 82, 83, 65, 49, 0, 4, 0, 0, 1, 0, 1, 0, 141, 86, 199, 111, 158, 134,
  73, 56, 48, 73, 243, 131, 196, 75, 224, 236, 32, 65, 129, 130, 42, 108, 49, 207, 94, 183, 239,
  72, 105, 68, 208, 50, 24, 142, 161, 211, 146, 7, 99, 113, 44, 203, 18, 215, 95, 183, 126, 152,
  17, 20, 158, 97, 72, 229, 211, 47, 186, 171, 55, 97, 28, 24, 120, 221, 193, 158, 32, 239, 19,
  93, 12, 178, 207, 242, 191, 236, 61, 17, 88, 16, 195, 217, 6, 150, 56, 254, 75, 226, 21, 219,
  247, 149, 134, 25, 32, 229, 171, 111, 125, 178, 226, 206, 239, 19, 106, 194, 61, 93, 210, 191,
  3, 23, 0, 174, 194, 50, 246, 198, 177, 199, 133, 180, 48, 92, 18, 59, 55, 171]), (163, [3, 6,
  19, 0]), (2563, [15, 0, 7, 8, 24, 15, 3, 8, 15, 3, 8, 17, 138, 148, 15, 8]), (6178, [3, 6, 17,
  24]), (12376, [3, 10, 1, 8]), (21694, [4, 10, 1, 30, 1]), (27051, [6, 21, 17, 135, 0, 1, 11]),
  (100452, [10, 32, 1, 1, 21, 18, 171, 44, 1, 19, 0]), (168415, [5, 7, 1, 17, 145, 92]), (210723,
  [20, 0, 2, 21, 17, 150, 32, 1, 4, 21, 17, 150, 32, 1, 6, 21, 17, 150, 32, 1, 6]), (294646, [9,
  16, 2, 1, 16, 30, 1, 16, 30, 0]), (386105, [4, 6, 18, 168, 56]), (401791, [8, 21, 18, 150, 4, 2,
  30, 0, 11])]
def corelibBlobPayloads : List (Nat × List Nat) := [(1, [0, 36, 0, 0, 4, 128, 0, 0, 148, 0, 0, 0,
  6, 2, 0, 0, 0, 36, 0, 0, 82, 83, 65, 49, 0, 4, 0, 0, 1, 0, 1, 0, 141, 86, 199, 111, 158, 134,
  73, 56, 48, 73, 243, 131, 196, 75, 224, 236, 32, 65, 129, 130, 42, 108, 49, 207, 94, 183, 239,
  72, 105, 68, 208, 50, 24, 142, 161, 211, 146, 7, 99, 113, 44, 203, 18, 215, 95, 183, 126, 152,
  17, 20, 158, 97, 72, 229, 211, 47, 186, 171, 55, 97, 28, 24, 120, 221, 193, 158, 32, 239, 19,
  93, 12, 178, 207, 242, 191, 236, 61, 17, 88, 16, 195, 217, 6, 150, 56, 254, 75, 226, 21, 219,
  247, 149, 134, 25, 32, 229, 171, 111, 125, 178, 226, 206, 239, 19, 106, 194, 61, 93, 210, 191,
  3, 23, 0, 174, 194, 50, 246, 198, 177, 199, 133, 180, 48, 92, 18, 59, 55, 171]), (163, [6, 19,
  0]), (2563, [0, 7, 8, 24, 15, 3, 8, 15, 3, 8, 17, 138, 148, 15, 8]), (6178, [6, 17, 24]),
  (12376, [10, 1, 8]), (21694, [10, 1, 30, 1]), (27051, [21, 17, 135, 0, 1, 11]), (100452, [32, 1,
  1, 21, 18, 171, 44, 1, 19, 0]), (168415, [7, 1, 17, 145, 92]), (210723, [0, 2, 21, 17, 150, 32,
  1, 4, 21, 17, 150, 32, 1, 6, 21, 17, 150, 32, 1, 6]), (294646, [16, 2, 1, 16, 30, 1, 16, 30,
  0]), (386105, [6, 18, 168, 56]), (401791, [21, 18, 150, 4, 2, 30, 0, 11])]
def corelibExpected : List (Nat × List Nat) := [(33556432, [1048832, 563595, 367513, 33554597,
  5941, 33929]), (67108869, [32854, 442748, 6178]), (67117864, [17, 151088, 386105]), (100663326,
  [0, 128, 8339, 262840, 2563]), (100684296, [9657652, 256, 150, 570613, 210723]), (100705672,
  [10323880, 0, 147, 263805, 294646]), (167775160, [452985704, 34974, 163]), (167780499,
  [452987091, 447108, 100452]), (285214672, [168415]), (452984932, [27051]), (452987117,
  [401791]), (687865906, [33554485, 33554483]), (704643172, [9, 34, 33554661, 445]), (704647244,
  [1, 0, 100705672, 526988]), (721420338, [100666545, 12376]), (721425295, [100694964, 21694])]
def corelibUserStrings : List (Nat × List Nat) := [(1, [59, 123, 0, 123, 0, 32, 0, 84, 0, 104, 0,
  105, 0, 115, 0, 32, 0, 61, 0, 32, 0, 123, 0, 48, 0, 125, 0, 44, 0, 32, 0, 102, 0, 108, 0, 97, 0,
  103, 0, 115, 0, 32, 0, 61, 0, 32, 0, 123, 0, 49, 0, 125, 0, 32, 0, 125, 0, 125, 0, 0]), (61,
  [35, 85, 0, 110, 0, 107, 0, 110, 0, 111, 0, 119, 0, 110, 0, 32, 0, 101, 0, 114, 0, 114, 0, 111,
  0, 114, 0, 32, 0, 40, 0, 48, 0, 120, 0, 0]), (97, [3, 120, 0, 0]), (101, [3, 41, 0, 0]), (105,
  [23, 116, 0, 97, 0, 114, 0, 103, 0, 101, 0, 116, 0, 67, 0, 108, 0, 97, 0, 115, 0, 115, 0, 0]),
  (129, [15, 99, 0, 117, 0, 108, 0, 116, 0, 117, 0, 114, 0, 101, 0, 0])]
def corelibUserUnits : List (Nat × List Nat) := [(1, [123, 123, 32, 84, 104, 105, 115, 32, 61, 32,
  123, 48, 125, 44, 32, 102, 108, 97, 103, 115, 32, 61, 32, 123, 49, 125, 32, 125, 125]), (61,
  [85, 110, 107, 110, 111, 119, 110, 32, 101, 114, 114, 111, 114, 32, 40, 48, 120]), (97, [120]),
  (101, [41]), (105, [116, 97, 114, 103, 101, 116, 67, 108, 97, 115, 115]), (129, [99, 117, 108,
  116, 117, 114, 101])]
def corelibIdentity : String :=
  "System.Private.CoreLib, Version=11.0.0.0, Culture=neutral, PublicKeyToken=7cec85d7bea7798e"
def corelibRefIdentities : List String := []

/-! ## Decoding -/

/-- Whether a decoding gives the value. -/
private def gives {α : Type} [BEq α] (result : Except MetadataError α) (value : α) : Bool :=
  match result with
  | .ok found => found == value
  | .error _ => false

/-- Whether a decoding fails with exactly this error. -/
private def failsWith {α : Type} (result : Except MetadataError α)
    (error : MetadataError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

/-- A slice cut from one of the images. -/
private def sliceOf (identity : String) (header assemblyRow : List Nat)
    (rows strings blobs userStrings : List ByteEntry) (keyToken : List Nat := []) :
    MetadataSlice :=
  { assembly := { identity := identity, keyToken := keyToken, tableHeader := header,
                  assemblyRow := assemblyRow, strings := strings, blobs := blobs },
    rows := rows, strings := strings, blobs := blobs, userStrings := userStrings }

private def examplesSlice : MetadataSlice :=
  sliceOf examplesIdentity examplesHeader examplesAssemblyRow examplesRows examplesStrings
    examplesBlobs examplesUserStrings

private def corelibSlice : MetadataSlice :=
  sliceOf corelibIdentity corelibHeader corelibAssemblyRow corelibRows corelibStrings
    corelibBlobs [] (bytesOf "7cec85d7bea7798e")

/-- The columns of a row as the typed accessors read them, with coded indices as tokens. -/
private def typedColumns (index : MetadataIndex) (token : Nat) :
    Except MetadataError (List Nat) :=
  match metadataTableOf token with
  | 0x01 => do
    let row ← index.typeRef token
    .ok [row.scope, row.name, row.namespace_]
  | 0x02 => do
    let row ← index.typeDef token
    .ok [row.flags, row.name, row.namespace_, row.extends_, row.fieldList, row.methodList]
  | 0x04 => do
    let row ← index.field token
    .ok [row.flags, row.name, row.signature]
  | 0x06 => do
    let row ← index.methodDef token
    .ok [row.rva, row.implFlags, row.flags, row.name, row.signature]
  | 0x0A => do
    let row ← index.memberRef token
    .ok [row.parent, row.name, row.signature]
  | 0x11 => (fun signature => [signature]) <$> index.signatureOf Table.standAloneSig token
  | 0x1B => (fun signature => [signature]) <$> index.signatureOf Table.typeSpec token
  | 0x23 => do
    let row ← index.assemblyRef token
    .ok [row.major, row.minor, row.build, row.revision, row.flags, row.publicKeyOrToken, row.name,
      row.culture]
  | 0x29 => do
    let row ← index.nestedClass token
    .ok [row.nested, row.enclosing]
  | 0x2A => do
    let row ← index.genericParam token
    .ok [row.number, row.flags, row.owner, row.name]
  | 0x2B => do
    let row ← index.methodSpec token
    .ok [row.method, row.instantiation]
  | _ => .error (.unsupportedTable token)

/-- Every expected row decodes to the columns the reference reader gave, for the slice. -/
private def rowsDecode (slice : MetadataSlice) (expected : List (Nat × List Nat)) : Bool :=
  match slice.index with
  | .ok index => expected.all fun (token, columns) => gives (typedColumns index token) columns
  | .error _ => false

/-- The slice's `#Strings` entries read as the reference reader's strings. -/
private def stringsDecode (slice : MetadataSlice) (expected : List (Nat × String)) : Bool :=
  match slice.index with
  | .ok index => expected.all fun (offset, text) => gives (index.string offset) (bytesOf text)
  | .error _ => false

/-- The slice's `#Blob` entries read as the reference reader's blob payloads. -/
private def blobsDecode (slice : MetadataSlice) (expected : List (Nat × List Nat)) : Bool :=
  match slice.index with
  | .ok index => expected.all fun (offset, payload) => gives (index.blob offset) payload
  | .error _ => false

/-- The slice's `#US` entries read as the reference reader's UTF-16 units. -/
private def userStringsDecode (slice : MetadataSlice) (expected : List (Nat × List Nat)) : Bool :=
  match slice.index with
  | .ok index => expected.all fun (offset, units) => gives (index.userString offset) units
  | .error _ => false

/-- The `rowSize` of every table agrees with `GetTableRowSize` for the image's header. -/
private def rowSizesAgree (header : List Nat) (sizes : List (Nat × Nat)) : Bool :=
  match decodeTableHeader header with
  | .ok decoded => sizes.all fun (table, size) => rowSize decoded.widths table == some size
  | .error _ => false

theorem examples_row_sizes_agree : rowSizesAgree examplesHeader examplesRowSizes = true := by
  decide +kernel
#print axioms examples_row_sizes_agree

theorem corelib_row_sizes_agree : rowSizesAgree corelibHeader corelibRowSizes = true := by
  decide +kernel
#print axioms corelib_row_sizes_agree

theorem examples_rows_decode : rowsDecode examplesSlice examplesExpected = true := by
  decide +kernel
#print axioms examples_rows_decode

theorem corelib_rows_decode : rowsDecode corelibSlice corelibExpected = true := by
  decide +kernel
#print axioms corelib_rows_decode

theorem examples_strings_decode : stringsDecode examplesSlice examplesStringText = true := by
  decide +kernel
#print axioms examples_strings_decode

theorem corelib_strings_decode : stringsDecode corelibSlice corelibStringText = true := by
  decide +kernel
#print axioms corelib_strings_decode

theorem examples_blobs_decode : blobsDecode examplesSlice examplesBlobPayloads = true := by
  decide +kernel
#print axioms examples_blobs_decode

theorem corelib_blobs_decode : blobsDecode corelibSlice corelibBlobPayloads = true := by
  decide +kernel
#print axioms corelib_blobs_decode

theorem examples_user_strings_decode :
    userStringsDecode examplesSlice examplesUserUnits = true := by decide +kernel
#print axioms examples_user_strings_decode

/-- The identities of the `Assembly` row and the carried `AssemblyRef` rows are Cecil's names. -/
theorem identities_match_cecil :
    (match examplesSlice.index with
      | .ok index => (List.range 2).all fun position =>
          gives (index.assemblyRefIdentity (tokenOf Table.assemblyRef (position + 1)))
            (bytesOf (examplesRefIdentities.getD position ""))
      | .error _ => false) = true ∧
    gives (examplesSlice.index.map (·.identity)) (bytesOf examplesIdentity) ∧
    gives (corelibSlice.index.map (·.identity)) (bytesOf corelibIdentity) := by
  decide +kernel
#print axioms identities_match_cecil

/-! ## Compressed integers and coded indices -/

theorem compressed_integers_decode :
    decodeCompressed [0x03, 9] = some (3, [9]) ∧
    decodeCompressed [0x7F] = some (0x7F, []) ∧
    decodeCompressed [0x80, 0x80] = some (0x80, []) ∧
    decodeCompressed [0xAE, 0x57] = some (0x2E57, []) ∧
    decodeCompressed [0xBF, 0xFF] = some (0x3FFF, []) ∧
    decodeCompressed [0xC0, 0x00, 0x40, 0x00] = some (0x4000, []) ∧
    decodeCompressed [0xDF, 0xFF, 0xFF, 0xFF] = some (0x1FFFFFFF, []) ∧
    decodeCompressed [0xE0, 0, 0, 0] = none ∧ decodeCompressed [0x80] = none ∧
    decodeCompressed [0xC0, 0, 0] = none ∧ decodeCompressed [] = none := by decide +kernel
#print axioms compressed_integers_decode

theorem coded_indices_decode :
    gives (decodeCoded typeDefOrRefTags 2 (5 * 4 + 1)) (tokenOf Table.typeRef 5) ∧
    gives (decodeCoded typeDefOrRefTags 2 (7 * 4 + 2)) (tokenOf Table.typeSpec 7) ∧
    gives (decodeCoded resolutionScopeTags 2 (3 * 4 + 2)) (tokenOf Table.assemblyRef 3) ∧
    gives (decodeCoded resolutionScopeTags 2 (3 * 4 + 3)) (tokenOf Table.typeRef 3) ∧
    gives (decodeCoded memberRefParentTags 3 (9 * 8 + 3)) (tokenOf Table.methodDef 9) ∧
    gives (decodeCoded memberRefParentTags 3 (9 * 8 + 4)) (tokenOf Table.typeSpec 9) ∧
    gives (decodeCoded methodDefOrRefTags 1 (4 * 2 + 1)) (tokenOf Table.memberRef 4) ∧
    gives (decodeCoded typeOrMethodDefTags 1 (4 * 2 + 1)) (tokenOf Table.methodDef 4) := by
  decide +kernel
#print axioms coded_indices_decode

/-! ## Slices that must be refused -/

/-- A tag past the table list of a coded index. -/
theorem rejects_a_coded_index_with_an_unused_tag :
    failsWith (decodeCoded typeDefOrRefTags 2 3) (.badCodedIndex 3) = true := by decide +kernel
#print axioms rejects_a_coded_index_with_an_unused_tag

/-- A row one byte short of the length its table's widths give. -/
theorem rejects_a_row_of_the_wrong_length :
    failsWith (({ examplesSlice with rows := [(0x01000001, [6, 0, 57, 28, 12])] }).index.bind
      (·.typeRef 0x01000001)) (.rowLength 0x01000001 6 5) = true := by decide +kernel
#print axioms rejects_a_row_of_the_wrong_length

/-- Two rows of one token. -/
theorem rejects_a_duplicate_token :
    failsWith ({ examplesSlice with rows := examplesRows ++ examplesRows.take 1 }.index.map
      (fun _ => ())) (.duplicateEntry 0x01000001) = true := by decide +kernel
#print axioms rejects_a_duplicate_token

/-- Two heap entries at one offset. -/
theorem rejects_a_duplicate_heap_offset :
    failsWith ({ examplesSlice with strings := [(0, [0]), (0, [0])] }.index.map
      (fun _ => ())) (.duplicateEntry 0) = true := by decide +kernel
#print axioms rejects_a_duplicate_heap_offset

/-- Row 0 is no row. -/
theorem rejects_row_zero :
    failsWith (examplesSlice.index.bind (·.row 0x01000000)) (.tokenOutOfScope 0x01000000) =
      true := by decide +kernel
#print axioms rejects_row_zero

/-- A row past the header's row count of the table. -/
theorem rejects_a_row_past_the_table :
    failsWith (examplesSlice.index.bind (·.row 0x011FFFFF)) (.tokenOutOfScope 0x011FFFFF) =
      true := by decide +kernel
#print axioms rejects_a_row_past_the_table

/-- A row the slice does not carry. -/
theorem rejects_a_missing_row :
    failsWith (examplesSlice.index.bind (·.row 0x01000004)) (.missingRow 0x01000004) = true := by
  decide +kernel
#print axioms rejects_a_missing_row

/-- A table the checker does not read (`Param`, table 8). -/
theorem rejects_a_table_the_checker_does_not_read :
    failsWith (examplesSlice.index.bind (·.row 0x08000001)) (.unsupportedTable 0x08000001) =
      true := by decide +kernel
#print axioms rejects_a_table_the_checker_does_not_read

/-- A heap offset with no entry. -/
theorem rejects_a_missing_heap_entry :
    failsWith (examplesSlice.index.bind (·.string 5)) (.missingHeap 0 5) = true ∧
    failsWith (examplesSlice.index.bind (·.blob 5)) (.missingHeap 1 5) = true ∧
    failsWith (examplesSlice.index.bind (·.userString 5)) (.missingHeap 2 5) = true := by
  decide +kernel
#print axioms rejects_a_missing_heap_entry

/-- A string with no terminating zero, and one with a zero inside. -/
theorem rejects_malformed_strings :
    failsWith (({ examplesSlice with strings := [(7, [65, 66])] }).index.bind (·.string 7))
      (.malformedHeap 0 7) = true ∧
    failsWith (({ examplesSlice with strings := [(7, [65, 0, 66, 0])] }).index.bind (·.string 7))
      (.malformedHeap 0 7) = true := by
  decide +kernel
#print axioms rejects_malformed_strings

/-- A blob whose length prefix is not its remaining length. -/
theorem rejects_a_blob_with_the_wrong_length_prefix :
    failsWith (({ examplesSlice with blobs := [(7, [3, 1, 2])] }).index.bind (·.blob 7))
      (.malformedHeap 1 7) = true := by decide +kernel
#print axioms rejects_a_blob_with_the_wrong_length_prefix

/-- A user string whose terminal byte disagrees with its units: `"hi"` needs 0. -/
theorem rejects_a_wrong_user_string_terminal_byte :
    failsWith (({ examplesSlice with userStrings := [(7, [5, 104, 0, 105, 0, 1])] }).index.bind
      (·.userString 7)) (.malformedUserString 7) = true ∧
    gives (({ examplesSlice with userStrings := [(7, [5, 104, 0, 105, 0, 0])] }).index.bind
      (·.userString 7)) [104, 105] := by decide +kernel
#print axioms rejects_a_wrong_user_string_terminal_byte

/-- A user string with an odd byte count. -/
theorem rejects_a_user_string_of_odd_length :
    failsWith (({ examplesSlice with userStrings := [(7, [4, 104, 0, 105, 0])] }).index.bind
      (·.userString 7)) (.malformedUserString 7) = true := by decide +kernel
#print axioms rejects_a_user_string_of_odd_length

/-- A header with the extra-data heap flag, and one marking an edit-and-continue table. -/
theorem rejects_unsupported_table_streams :
    failsWith (decodeTableHeader (examplesHeader.set 6 0x40) |>.map (fun _ => ()))
      (.unsupportedTableStream 0x40) = true ∧
    failsWith (decodeTableHeader (examplesHeader.set 11 0x40) |>.map (fun _ => ()))
      (.unsupportedTableStream 0x100) = true := by
  decide +kernel
#print axioms rejects_unsupported_table_streams

/-- A header cut short, and one with a byte that is not a byte. -/
theorem rejects_malformed_headers :
    failsWith (decodeTableHeader (examplesHeader.take 30) |>.map (fun _ => ()))
      .malformedTableHeader = true ∧
    failsWith (decodeTableHeader (examplesHeader.set 0 256) |>.map (fun _ => ()))
      .invalidByte = true ∧
    failsWith (decodeTableHeader (examplesHeader ++ [0]) |>.map (fun _ => ()))
      .malformedTableHeader = true := by decide +kernel
#print axioms rejects_malformed_headers

/-- A heap entry that is not a byte. -/
theorem rejects_a_value_above_255 :
    failsWith ({ examplesSlice with blobs := [(7, [1, 256])] }.index.map (fun _ => ()))
      .invalidByte = true := by decide +kernel
#print axioms rejects_a_value_above_255

/-- The claimed version differs from the one the `Assembly` row spells. -/
theorem rejects_a_changed_assembly_identity :
    failsWith ({ examplesSlice with assembly := { examplesSlice.assembly with
        identity :=
          "Examples, Version=2.0.0.0, Culture=neutral, PublicKeyToken=null" } }.index.map
      (fun _ => ())) .identityMismatch = true := by decide +kernel
#print axioms rejects_a_changed_assembly_identity

/-- A reference with a public key flag has a token only SHA-1 can give. -/
theorem rejects_an_assembly_reference_with_a_full_key :
    failsWith (({ examplesSlice with rows := [(0x23000001,
        ((examplesRows.lookup 0x23000001).getD []).set 8 1)] }).index.bind
      (·.assemblyRefIdentity 0x23000001))
      (.unsupportedAssemblyRef 0x23000001) = true := by decide +kernel
#print axioms rejects_an_assembly_reference_with_a_full_key

/-! ## Signatures -/

/-- The signature blobs of `Examples.dll` and `System.Private.CoreLib.dll` decode to the types
    their bytes spell by ECMA-335 II.23.2. -/
theorem real_signatures_decode :
    -- `void (int)` on an instance
    gives (decodeMethodSig [32, 1, 1, 8]) ⟨0x20, 0, .primitive 1, [.primitive 8]⟩ ∧
    -- `uint (uint, uint)` as a static
    gives (decodeMethodSig [0, 2, 9, 9, 9])
      ⟨0, 0, .primitive 9, [.primitive 9, .primitive 9]⟩ ∧
    -- an instance method taking a value type named by a `TypeRef`
    gives (decodeMethodSig [32, 1, 1, 17, 17]) ⟨0x20, 0, .primitive 1, [.named true 0x01000004]⟩ ∧
    gives (decodeTypeSpec [21, 18, 72, 1, 8])
      (.genericInst false 0x02000012 (.cons (.primitive 8) .nil)) ∧
    gives (decodeLocalSig [7, 1, 21, 17, 89, 1, 17, 131, 36])
      [.genericInst true 0x01000016 (.cons (.named true 0x020000C9) .nil)] ∧
    gives (decodeFieldSig [6, 29, 17, 131, 36]) (.szarray (.named true 0x020000C9)) ∧
    gives (decodeMethodSpec [10, 1, 30, 1]) [.mvar 1] ∧
    gives (decodeTypeSpec [21, 17, 135, 0, 1, 11])
      (.genericInst true 0x020001C0 (.cons (.primitive 11) .nil)) ∧
    gives (decodeMethodSig [0, 7, 8, 24, 15, 3, 8, 15, 3, 8, 17, 138, 148, 15, 8])
      ⟨0, 0, .primitive 8, [.primitive 24, .pointer (.primitive 3), .primitive 8,
        .pointer (.primitive 3), .primitive 8, .named true 0x020002A5, .pointer (.primitive 8)]⟩
      := by
  decide +kernel
#print axioms real_signatures_decode

/-- Modifiers wrap the type that follows them, function pointers carry their convention, and
    generic methods state their arity. -/
theorem modifiers_function_pointers_and_generic_arity_decode :
    gives (decodeMethodSig [0x20, 1, 1, 0x1F, 13, 0x10, 9])
      ⟨0x20, 0, .primitive 1, [.modified true 0x01000003 (.byref (.primitive 9))]⟩ ∧
    gives (decodeMethodSig [0x30, 2, 2, 1, 0x13, 0, 0x1E, 1])
      ⟨0x30, 2, .primitive 1, [.var 0, .mvar 1]⟩ ∧
    gives (decodeFieldSig [6, 0x1B, 0, 1, 1, 8])
      (.functionPointer 0 (.primitive 1) (.cons (.primitive 8) .nil))
      ∧ gives (decodeMethodSig [0x20, 1, 0x1F, 13, 1, 8])
      ⟨0x20, 0, .modified true 0x01000003 (.primitive 1), [.primitive 8]⟩ := by
  decide +kernel
#print axioms modifiers_function_pointers_and_generic_arity_decode

/-- A general array, `typedref`, the vararg sentinel and a pinned local report their byte. -/
theorem rejects_signature_forms_the_model_lacks :
    failsWith (decodeMethodSig [0, 1, 1, 0x14, 8, 1, 3]) (.unsupportedSignature 3 0x14) = true ∧
    failsWith (decodeMethodSig [0, 1, 1, 0x16]) (.unsupportedSignature 3 0x16) = true ∧
    failsWith (decodeMethodSig [0, 1, 1, 0x41, 8]) (.unsupportedSignature 3 0x41) = true ∧
    failsWith (decodeLocalSig [7, 1, 0x45, 8]) (.unsupportedSignature 2 0x45) = true ∧
    failsWith (decodeMethodSig [0x05, 0, 1]) (.unsupportedSignature 0 0x05) = true ∧
    failsWith (decodeFieldSig [0x07, 8]) (.unsupportedSignature 0 0x07) = true ∧
    failsWith (decodeFieldSig [6, 0x1B, 0x10, 0, 1]) (.unsupportedSignature 2 0x10) = true := by
  decide +kernel
#print axioms rejects_signature_forms_the_model_lacks

/-- A byte after the last type, a blob that ends inside a type and a bad type token tag. -/
theorem rejects_malformed_signatures :
    failsWith (decodeMethodSig [0, 0, 1, 8]) (.unsupportedSignature 3 0x100) = true ∧
    failsWith (decodeMethodSig [0, 1, 1]) (.truncatedSignature 3) = true ∧
    failsWith (decodeFieldSig [6, 0x11]) (.truncatedSignature 2) = true ∧
    failsWith (decodeTypeSpec [0x11, 3]) (.badCodedIndex 3) = true ∧
    failsWith (decodeTypeSpec [0x15, 0x0E, 1, 1, 8]) (.unsupportedSignature 1 0x0E) = true := by
  decide +kernel
#print axioms rejects_malformed_signatures

end Tests.MetadataDecoding
