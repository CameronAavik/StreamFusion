open FSharp.Quotations.Evaluator
open Streams.Streams
open Streams.StreamImpls

let evaluate expr=
    printf "%s" (QuotationPrinter.toString expr)
    QuotationEvaluator.Evaluate expr

// This uses the final stream definition
let example () =
    <@ [|0; 1; 2; 3; 4|] @>
    |> Stream.ofArray
    |> Stream.map (fun a -> <@ %a * %a @>)
    |> Stream.filter (fun x -> <@ %x > 2 @>)
    |> Stream.fold (fun x y -> <@ %x + %y @>) <@ 0 @>
    |> evaluate

// This example is currently broken due to https://github.com/fsprojects/FSharp.Quotations.Evaluator/issues/39
let iota n = Stream.unfold (fun n -> <@ Some (%n, (%n) + 1) @>) n
let complexExample () =
    Stream.zipWith (fun e1 e2 -> <@ (%e1, %e2) @>)
        (<@ [|0;1;2;3|] @>
         |> Stream.ofArray
         |> Stream.map (fun x -> <@ %x * %x @>)
         |> Stream.take <@ 12 @>
         |> Stream.filter (fun x -> <@ %x % 2 = 0 @>)
         |> Stream.map (fun x -> <@ %x * %x @>))
        (iota <@ 1 @>
         |> Stream.flatMap (fun x -> iota <@ (%x) + 1 @> |> Stream.take <@ 3 @>)
         |> Stream.filter (fun x -> <@ %x % 2 = 0 @>))
    |> Stream.fold (fun z a -> <@ (%a) :: (%z) @>) <@ [] @>
    |> evaluate

// All other examples here use simpler definitions of the stream and can be ignored for now. I'll move these somewhere else later.
let examplePull () =
    [|0; 1; 2; 3; 4|]
    |> PullStream.ofArray
    |> PullStream.map (fun a -> a * a)
    |> PullStream.fold (fun x y -> x + y) 0

let example1 () =
    <@ [|0; 1; 2; 3; 4|] @>
    |> StStream1.ofArray
    |> StStream1.map (fun a -> <@ %a * %a @>)
    |> StStream1.fold (fun x y -> <@ %x + %y @>) <@ 0 @>
    |> evaluate

let example2 () =
    <@ [|0; 1; 2; 3; 4|] @>
    |> StStream2.ofArray
    |> StStream2.map (fun a -> <@ %a * %a @>)
    |> StStream2.fold (fun x y -> <@ %x + %y @>) <@ 0 @>
    |> evaluate

let example3 () =
    <@ [|0; 1; 2; 3; 4|] @>
    |> StStream3.ofArray
    |> StStream3.map (fun a -> <@ %a * %a @>)
    |> StStream3.fold (fun x y -> <@ %x + %y @>) <@ 0 @>
    |> evaluate

let example4 () =
    <@ [|0; 1; 2; 3; 4|] @>
    |> Stream4.ofArray
    |> Stream4.map (fun a -> <@ %a * %a @>)
    |> Stream4.fold (fun x y -> <@ %x + %y @>) <@ 0 @>
    |> evaluate

[<EntryPoint>]
let main _ =
    printfn "%i" (example ())
    //printfn "%A" (complexExample ())
    printfn "%i" (examplePull ())
    printfn "%i" (example1 ())
    printfn "%i" (example2 ())
    printfn "%i" (example3 ())
    printfn "%i" (example4 ())
    0
