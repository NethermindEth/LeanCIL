namespace Examples.FSharp

open System.Runtime.CompilerServices

[<Struct; NoEquality; NoComparison>]
type Counter =
    val mutable Value: uint64

    new(value) = { Value = value }

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member this.Add(value) =
        this.Value <- this.Value + value

module Arithmetic =
    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let Add (x: uint64) (y: uint64) = x + y

    let WrongAdd (x: uint64) (y: uint64) = x - y

    let Minimum (x: uint64) (y: uint64) =
        if x < y then x else y

    let Calls (x: uint64) = Add (Add x 1UL) 2UL

    let Construct (x: uint64) = Counter(x)

    let Mutate (x: uint64) =
        let mutable counter = Counter(x)
        counter.Add(3UL)
        counter.Value

    let Store (target: byref<uint64>) (value: uint64) =
        target <- value
        target

    // Lists require runtime allocation outside the admitted subset.
    let UnsupportedList (value: uint64) = [value]
