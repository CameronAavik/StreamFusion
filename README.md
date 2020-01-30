# StreamFusion
---

This implements the library design specified in the paper "Stream Fusion, to Completeness" by Kiselyov et. al

As an example it can convert the following code:

```fsharp
[|0; 1; 2; 3; 4|]
|> Stream.ofArray
|> Stream.map (fun a -> <@ %a * %a @>)
|> Stream.filter (fun x -> <@ %x > 2 @>)
|> Stream.fold (fun x y -> <@ %x + %y @>) 0
```

into the following equivalent imperative code:

```
let total = ref 0
let arr = [|0; 1; 2; 3; 4|]
for i in 0..(Array.length arr - 1) do
    let x = arr.[i]
    let y = x * x
    if y > 2 then
        total := !total + y
!total
```