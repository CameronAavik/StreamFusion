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
        static member ofArray (arr : Expr<'a array>) : StStream1<'a, int * 'a array> =
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
                    match ((% ExprHelpers.lambda step) s) with
                    | Nil -> z
                    | Cons (a, t) -> loop ((% ExprHelpers.lambda2 folder) z a) t
                loop %initState %s
            @>

        static member map (f : Expr<'a> -> Expr<'b>) ((s, step) : StStream1<'a, 'c>) : StStream1<'b, 'c> =
            let new_step s =
                <@
                    match (% step s) with
                    | Nil -> Nil
                    | Cons (a, t) -> Cons ((% ExprHelpers.lambda f) a, t)
                @>
            s, new_step

    type StStream2<'x, 's, 'w> = Expr<'s> * (Expr<'s> -> (StreamShape<Expr<'x>, Expr<'s>> -> Expr<'w>) -> Expr<'w>)
    type StStream2 =
        static member ofArray (arr : Expr<'a array>) : StStream2<'a, _, _> =
            let iVar = ExprHelpers.generateVar typeof<int>
            let iExpr = Expr.Cast<int>(Expr.Var(iVar))

            let arrVar = ExprHelpers.generateVar typeof<'a array>
            let arrExpr = Expr.Cast<'a array>(Expr.Var(arrVar))

            let step state k =
                let buildStreamExpr =
                    <@
                        if %iExpr < Array.length %arrExpr then
                            (% k (Cons (<@ (%arrExpr).[%iExpr] @>, <@ %iExpr + 1, %arrExpr @>)))
                        else (% k Nil)
                    @>
                Expr.Cast<_>(
                    Expr.Let(iVar, Expr.TupleGet(state, 0), 
                        Expr.Let(arrVar, Expr.TupleGet(state, 1), 
                            buildStreamExpr)))
            <@ (0, %arr) @>, step

        static member fold (folder : Expr<'b> -> Expr<'a> -> Expr<'b>) (initState : Expr<'b>) ((s, step) : StStream2<'a, 's, _>) =
            let handleStream loop state : StreamShape<Expr<'a>, Expr<'s>> -> Expr<'b> =
                function
                | Nil -> state
                | Cons (a, t) -> <@ (%loop) (% folder state a) %t @>

            let loopVar = ExprHelpers.generateVar typeof<'b -> 's -> 'b>
            let zVar = ExprHelpers.generateVar typeof<'b>
            let sVar = ExprHelpers.generateVar typeof<'s>

            let loopBody = step (Expr.Cast<_>(Expr.Var(sVar))) (handleStream (Expr.Cast<_>(Expr.Var(loopVar))) (Expr.Cast<_>(Expr.Var(zVar))))

            // loop %z %s
            let callLoopExpr = Expr.Application(Expr.Application(Expr.Var(loopVar), initState), s)

            // let rec loop z s = loopBody in callLoopExpr 
            let loopDefExpr = 
                Expr.LetRecursive(
                    [loopVar, Expr.Lambda(zVar, Expr.Lambda(sVar, loopBody))],
                    callLoopExpr)

            Expr.Cast<'b>(loopDefExpr)

        static member map f ((s, step) : StStream2<'a, _, _>) : StStream2<'b, _, _> =
            let var = ExprHelpers.generateVar typeof<'a>
            let new_step s k =
                let handleStream =
                    function
                    | Cons (a, t) ->
                        let applyMapExpr = k (Cons (Expr.Cast<'b>(Expr.Var(var)), t)) // k (Cons (<@ a' @>, t))
                        Expr.Cast<'b>(Expr.Let(var, f a, applyMapExpr)) // let a' = (% f a) in applyMapExpr
                    | Nil -> k Nil
                step s handleStream
            s, new_step

    type StStream3<'x, 's, 'w> = 
        (('s -> Expr<'w>) -> Expr<'w>) *
        ('s -> (StreamShape<Expr<'x>, unit> -> Expr<'w>) -> Expr<'w>)

    type StStream3 =
        static member ofArray (arr : Expr<'a array>) : StStream3<'a, _, _> =
            let iVar = ExprHelpers.generateVar typeof<int ref>
            let iExpr = Expr.Cast<_>(Expr.Var(iVar))
            let arrVar = ExprHelpers.generateVar typeof<'a array>
            let arrExpr = Expr.Cast<'a array>(Expr.Var(arrVar))
            let elemVar = ExprHelpers.generateVar typeof<'a>
            let elemExpr = Expr.Cast<'a>(Expr.Var(elemVar))

            let init arr k =
                Expr.Cast<_>(
                    Expr.Let(iVar, <@ ref 0 @>,
                        Expr.Let(arrVar, arr,
                            k (iExpr, arrExpr))))

            let step (i, arr) k =
                Expr.Cast<_>(
                    Expr.IfThenElse(
                        <@ !(%i) < Array.length %arr @>,
                        Expr.Let(elemVar, <@ (%arr).[!(%i)] @>,
                            <@
                                incr %i
                                (%k (Cons (elemExpr, ())))
                            @>),
                        <@ (%k Nil) @>))

            (init arr, step)

        static member fold (folder : Expr<'b> -> Expr<'a> -> Expr<'b>) (initState : Expr<'b>) ((init, step) : StStream3<'a, 's, _>) =
            let loopVar = ExprHelpers.generateVar typeof<'b -> 'b>
            let loopExpr = Expr.Cast<_>(Expr.Var(loopVar))
            let zVar = ExprHelpers.generateVar typeof<'b>
            let zExpr = Expr.Cast<'b>(Expr.Var(zVar))

            let handleStream s =
                match s with
                | Nil -> zExpr
                | Cons (a, _) -> <@ (%loopExpr) (% folder zExpr a) @>

            let handleState s =
                Expr.Cast<_>(
                    Expr.LetRecursive(
                        [loopVar, Expr.Lambda(zVar, step s handleStream)],
                        <@ (%loopExpr) %initState @>))

            init handleState

        static member map f ((s, step) : StStream3<'a, _, _>) : StStream3<'b, _, _> =
            let var = ExprHelpers.generateVar typeof<'a>
            let new_step s k =
                let handleStream =
                    function
                    | Cons (a, t) ->
                        let applyMapExpr = k (Cons (Expr.Cast<'b>(Expr.Var(var)), t)) // k (Cons (<@ a' @>, t))
                        Expr.Cast<'b>(Expr.Let(var, f a, applyMapExpr)) // let a' = (% f a) in applyMapExpr
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
                            let iVar = ExprHelpers.generateVar typeof<int ref>
                            let iExpr = Expr.Cast<_>(Expr.Var(iVar))

                            let init =
                                { new Init4<_> with
                                    member _.Invoke k = 
                                        let init' s0 =
                                            Expr.Cast<_>(
                                                Expr.Let(iVar, <@ ref 0 @>,
                                                    k (iExpr, s0)))
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

        static member foldRaw (consumer : 'a -> Expr<unit>) (stStream : StStream4<'a>) =
            let unpack =
                { new StStreamUnPack4<'a, Expr<unit>> with
                    member _.Invoke<'s>(s : (Init4<'s> * Producer4<'a, 's>)) =
                        match s with
                        | (init, For (upb, index)) ->
                            let iVar = ExprHelpers.generateVar typeof<int>
                            let iExpr = Expr.Cast<int>(Expr.Var(iVar))
                            init.Invoke (fun sp -> Expr.Cast<_>(Expr.ForIntegerRangeLoop(iVar, <@ 0 @>, upb sp, <@ (% index sp iExpr consumer) @>)))
                        | (init, Unfold (term, step)) ->
                            init.Invoke (fun sp -> <@ while (%term sp) do (% step sp consumer) @>) }
            stStream.Invoke unpack 

    type Stream4<'x> = StStream4<Expr<'x>>
    type Stream4 =
        static member ofArray (arr : Expr<'a array>) : Stream4<'a> =
            let arrVar = ExprHelpers.generateVar typeof<'a array>
            let arrExpr = Expr.Cast<'a array>(Expr.Var(arrVar))
            let elemVar = ExprHelpers.generateVar typeof<'a>
            let elemExpr = Expr.Cast<'a>(Expr.Var(elemVar))

            let init = 
                { new Init4<Expr<'a array>> with 
                    member _.Invoke (k : Expr<'a array> -> Expr<'w>) = 
                        Expr.Cast<'w>(
                            Expr.Let(arrVar, arr, 
                                k arrExpr)) }

            let upb arr = <@ (Array.length %arr) - 1 @>
            let index arr i k =
                Expr.Cast<_>(
                    Expr.Let(elemVar, <@ Array.item %i %arr @>,
                        k elemExpr))

            StStreamConstr(init, For (upb, index)) :> Stream4<'a>

        static member fold (folder : Expr<'b> -> Expr<'a> -> Expr<'b>) (initState : Expr<'b>) (str : Stream4<'a>) =
            let stateVar = ExprHelpers.generateVar typeof<'b ref>
            let stateExpr = Expr.Cast<'b ref>(Expr.Var(stateVar))
            Expr.Cast<_>(
                Expr.Let(stateVar, <@ ref %initState @>,
                    <@ (% (StStream4.foldRaw (fun a -> <@ (%stateExpr) := (% folder <@ !(%stateExpr) @> a) @>) str); !(%stateExpr)) @> ))

        static member map (f : Expr<'a> -> Expr<'b>) (str : Stream4<'a>) : Stream4<'b> =
            let var = ExprHelpers.generateVar typeof<'b>
            let varExpr = Expr.Cast<'b>(Expr.Var(var))
            let newStep (a : Expr<'a>) (k : Expr<'b> -> Expr<unit>) = Expr.Cast<unit>(Expr.Let(var, f a, k varExpr))
            StStream4.mapRaw newStep str