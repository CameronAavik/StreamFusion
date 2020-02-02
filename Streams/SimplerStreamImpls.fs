namespace Streams

open Microsoft.FSharp.Quotations

(*
    This file contains definitions for the progressive stream definitions as they were defined
    in the "Stream Fusion, To Completeness" paper.

    The full definition is in Streams.fs
*)

module StreamImpls =
    type StreamShape<'x, 's> =
        | Nil
        | Cons of 'x * 's

    type PullStream<'x, 's> = 's * ('s -> StreamShape<'x, 's>)
    type PullStream =
        static member ofArray arr : PullStream<_, _> =
            let step (i, arr) =
                if i < Array.length arr
                    then Cons (arr.[i], (i + 1, arr))
                else Nil
            ((0, arr), step)

        static member fold folder initState ((s, step) : PullStream<_, _>) =
            let rec loop z s =
                match step s with
                | Nil -> z
                | Cons (a, t) -> loop (folder z a) t
            loop initState s

        static member map f ((s, step) : PullStream<_, _>) : PullStream<_, _> =
            let new_step s =
                match step s with
                | Nil -> Nil
                | Cons (a, t) -> Cons (f a, t)
            s, new_step

    type StStream1<'x, 's> = Expr<'s> * (Expr<'s> -> Expr<StreamShape<'x, 's>>)
    type StStream1 =
        static member ofArray arr : StStream1<_, _> =
            let step state =
                <@
                    match %state with
                    | (i, arr) ->
                        if i < Array.length arr
                            then Cons ((arr).[i], (i + 1, arr))
                        else Nil
                @>
            <@ (0, %arr) @>, step

        static member fold folder initState ((s, step) : StStream1<_, _>) =
            <@
                let rec loop z s =
                    match ((% ExprHelpers.lambda "s" step) s) with
                    | Nil -> z
                    | Cons (a, t) -> loop ((% ExprHelpers.lambda2 "z" "a" folder) z a) t
                loop %initState %s
            @>

        static member map f ((s, step) : StStream1<_, _>) : StStream1<_, _> =
            let new_step s =
                <@
                    match (% step s) with
                    | Nil -> Nil
                    | Cons (a, t) -> Cons ((% ExprHelpers.lambda "a" f) a, t)
                @>
            s, new_step

    type StStream2<'x, 's, 'w> = Expr<'s> * (Expr<'s> -> (StreamShape<Expr<'x>, Expr<'s>> -> Expr<'w>) -> Expr<'w>)
    type StStream2 =
        static member ofArray arr : StStream2<_, _, _> =
            let step state k =
                let buildStreamExpr i arr =
                    <@
                        if %i < Array.length %arr then
                            (% k (Cons (<@ (%arr).[%i] @>, <@ %i + 1, %arr @>)))
                        else (% k Nil)
                    @>
                ExprHelpers.genUnpackTuple "i" "arr" state buildStreamExpr
            <@ (0, %arr) @>, step

        static member fold folder initState ((s, step) : StStream2<_, _, _>) =
            let handleStream loop state  =
                function
                | Nil -> state
                | Cons (a, t) -> <@ (%loop) (% folder state a) %t @>

            ExprHelpers.genLetRec2 "loop" "z" "s" (fun loop z s -> step s (handleStream loop z)) (fun loop -> <@ (%loop) %initState %s @>)

        static member map f ((s, step) : StStream2<_, _, _>) : StStream2<_, _, _> =
            let new_step s k =
                let handleStream =
                    function
                    | Cons (a, t) -> ExprHelpers.genLet "a'" (f a) (fun a' -> k (Cons (a', t)))
                    | Nil -> k Nil
                step s handleStream
            s, new_step

    type StStream3<'x, 's, 'w> = 
        (('s -> Expr<'w>) -> Expr<'w>) *
        ('s -> (StreamShape<Expr<'x>, unit> -> Expr<'w>) -> Expr<'w>)

    type StStream3 =
        static member ofArray arr : StStream3<'a, _, _> =
            let init arr k =
                ExprHelpers.genLet2 "i" <@ ref 0 @> "arr" arr (fun i arr -> k (i, arr))

            let step (i, arr) k =
                let handleShouldStep =
                    ExprHelpers.genLet "elem" <@ Array.item !(%i) %arr @>
                        (fun elem -> <@ incr %i; (%k (Cons (elem, ()))) @>)

                <@ if !(%i) < Array.length %arr then %handleShouldStep else (%k Nil) @>
            (init arr, step)

        static member fold folder initState ((init, step) : StStream3<'a, 's, _>) =
            let handleStream loopExpr zExpr s =
                match s with
                | Nil -> zExpr
                | Cons (a, _) -> <@ (%loopExpr) (% folder zExpr a) @>

            let handleState s =
                ExprHelpers.genLetRec "loop" "z"
                    (fun loop z -> step s (handleStream loop z))
                    (fun loop -> <@ (%loop) %initState @>)

            init handleState

        static member map f ((s, step) : StStream3<_, _, _>) : StStream3<_, _, _> =
            let new_step s k =
                let handleStream =
                    function
                    | Cons (a, t) -> ExprHelpers.genLet "a'" (f a) (fun a' -> k (Cons (a', t)))
                    | Nil -> k Nil
                step s handleStream
            s, new_step
          
    type Producer4<'x, 's> =
        | For of upb : ('s -> Expr<int>) * index : ('s -> Expr<int> -> ('x -> Expr<unit>) -> Expr<unit>)
        | Unfold of term : ('s -> Expr<bool>) * step : ('s -> ('x -> Expr<unit>) -> Expr<unit>)

    type Init4<'s> =
        abstract member Invoke<'w> : ('s -> Expr<'w>) -> Expr<'w>

    type StStreamUnPack4<'T, 'R> = 
        abstract Invoke<'S> : (Init4<'S> * Producer4<'T, 'S>) -> 'R

    type StStream4<'T> = 
        abstract Invoke<'R> : StStreamUnPack4<'T, 'R> -> 'R

    type StStreamConstr<'S, 'T>(init : Init4<'S>, producer : Producer4<'T, 'S>) = 
        interface StStream4<'T> with
            member _.Invoke<'R> (producerUnPack : StStreamUnPack4<'T, 'R>) = 
                producerUnPack.Invoke<'S>(init, producer)

    type StStream4 =
        static member forUnfold (stStream : StStream4<'a>) : StStream4<'a> =
            let unpack =
                { new StStreamUnPack4<'a, StStream4<'a>> with
                    member _.Invoke<'s>(s) =
                        match s with
                        | (init, For (upb, index)) ->
                            let init =
                                { new Init4<_> with
                                    member _.Invoke k = 
                                        let init' s0 = ExprHelpers.genLet "i" <@ ref 0 @> (fun i -> k (i, s0))
                                        init.Invoke init' }

                            let term (i, s0 : 's) = <@ !(%i) <= (% upb s0) @>
                            let step (i, s0) (k : 'a -> Expr<unit>) =
                                let step' (a : 'a) = <@ incr %i; (% k a) @>
                                index s0 <@ !(%i) @> step'

                            let producer = Unfold (term, step)
                            StStreamConstr(init, producer) :> StStream4<'a>
                        | _ -> stStream }
            stStream.Invoke unpack

        static member mapRaw (tr : 'a -> ('b -> Expr<unit>) -> Expr<unit>) (stStream : StStream4<'a>) : StStream4<'b> =
            let unpack =
                { new StStreamUnPack4<'a, StStream4<'b>> with
                    member _.Invoke<'s>(s : (Init4<'s> * Producer4<'a, 's>)) =
                        match s with
                        | (init, For (upb, index)) ->
                            let index s i (k : 'b -> Expr<unit>) = index s i (fun e -> tr e k)
                            StStreamConstr(init, For (upb, index)) :> StStream4<'b>
                        | (init, Unfold (term, step)) ->
                            let step s k = step s (fun e -> tr e k)
                            StStreamConstr(init, Unfold (term, step)) :> StStream4<'b> }
            stStream.Invoke unpack 

        static member foldRaw consumer (stStream : StStream4<'a>) =
            let unpack =
                { new StStreamUnPack4<_, _> with
                    member _.Invoke s =
                        match s with
                        | (init, For (upb, index)) ->
                            init.Invoke (fun sp -> ExprHelpers.genFor "i" <@ 0 @> (upb sp) (fun i -> index sp i consumer))
                        | (init, Unfold (term, step)) ->
                            init.Invoke (fun sp -> <@ while (%term sp) do (% step sp consumer) @>) }
            stStream.Invoke unpack 

    type Stream4<'x> = StStream4<Expr<'x>>
    type Stream4 =
        static member ofArray arr : Stream4<_> =
            let init k = ExprHelpers.genLet "arr" arr k
            let upb arr = <@ (Array.length %arr) - 1 @>
            let index arr i k = ExprHelpers.genLet "elem" <@ Array.item %i %arr @> k

            let initObj = { new Init4<_> with member _.Invoke k = init k }
            StStreamConstr(initObj, For (upb, index)) :> Stream4<_>

        static member fold folder initState (str : Stream4<_>) =
            ExprHelpers.genLet "state" <@ ref %initState @> 
                (fun state -> <@ (% (StStream4.foldRaw (fun a -> <@ (%state) := (% folder <@ !(%state) @> a) @>) str); !(%state)) @> )

        static member map f (str : Stream4<_>) : Stream4<_> =
            let newStep a k = ExprHelpers.genLet "var" (f a) k
            StStream4.mapRaw newStep str