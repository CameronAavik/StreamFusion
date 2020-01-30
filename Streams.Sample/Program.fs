open FSharp.Quotations.Evaluator
open Streams.Streams
open Streams.StreamImpls

let evaluate expr =
    printf "%s" (QuotationPrinter.toString expr)
    QuotationEvaluator.Evaluate expr

// This uses the final stream definition
let example () =
    [|0; 1; 2; 3; 4|]
    |> Stream.ofArray
    |> Stream.map (fun a -> <@ %a * %a @>)
    |> Stream.filter (fun x -> <@ %x > 2 @>)
    |> Stream.fold (fun x y -> <@ %x + %y @>) 0
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
    printfn "%i" (examplePull ())
    printfn "%i" (example1 ())
    printfn "%i" (example2 ())
    printfn "%i" (example3 ())
    printfn "%i" (example4 ())
    0
