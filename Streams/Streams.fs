namespace Streams

open Microsoft.FSharp.Quotations

module ExprHelpers =
    let counter = ref 0
    let generateVar<'T> name : Var * Expr<'T> = 
        incr counter
        let var = new Var(sprintf "%s_%d" name !counter, typeof<'T>)
        var, Expr.Cast<'T>(Expr.Var(var))

    let genLet<'T, 'U> name (value : Expr<'T>) (body : Expr<'T> -> Expr<'U>) =
        let var, expr = generateVar<'T> name
        Expr.Cast<'U>(Expr.Let(var, value, body expr))

    let genLet2<'T, 'S, 'U> name1 (value1 : Expr<'T>) name2 (value2 : Expr<'S>) (body : Expr<'T> -> Expr<'S> -> Expr<'U>) =
        let var1, expr1 = generateVar<'T> name1
        let var2, expr2 = generateVar<'S> name2
        Expr.Cast<'U>(Expr.Let(var1, value1, Expr.Let(var2, value2, body expr1 expr2)))

    let genFor loopVarName (minVal : Expr<int>) (maxVal : Expr<int>) (body : Expr<int> -> Expr<unit>) =
        let loopVar, expr = generateVar<int> loopVarName
        Expr.Cast<unit>(Expr.ForIntegerRangeLoop(loopVar, minVal, maxVal, body expr))

    let genMatchOption matchVarName (optionExpr : Expr<'T option>) (handleSome : Expr<'T> -> Expr<'U>) (handleNone : Expr<'U>) =
        <@
            if Option.isSome (%optionExpr) then
                (% genLet matchVarName <@ Option.get (%optionExpr) @> handleSome)
            else %handleNone
        @>

    let genUnpackTuple item1Name item2Name (tupleExpr : Expr<'T * 'U>) (body : Expr<'T> -> Expr<'U> -> Expr<'R>) =
        let fromTuple i = Expr.Cast<_>(Expr.TupleGet(tupleExpr, i))
        genLet2 item1Name (fromTuple 0) item2Name (fromTuple 1) body

    let genLetRec funcName paramName (body : Expr<'T -> 'U> -> Expr<'T> -> Expr<'U>) (cont : Expr<'T -> 'U> -> Expr<'R>) =
        let func, funcExpr = generateVar<'T -> 'U> funcName
        let param, paramExpr = generateVar<'T> paramName
        Expr.Cast<'R>(Expr.LetRecursive([func, Expr.Lambda(param, body funcExpr paramExpr)], cont funcExpr))

    let genLetRec2 funcName param1Name param2Name (body : Expr<'T -> 'S -> 'U> -> Expr<'T> -> Expr<'S> -> Expr<'U>) (cont : Expr<'T -> 'S -> 'U> -> Expr<'R>) =
        let param2, param2Expr = generateVar<'S> param2Name
        genLetRec funcName param1Name (fun func param1 -> Expr.Cast<_>(Expr.Lambda(param2, body func param1 param2Expr))) cont

    let lambda paramName (f : Expr<'T> -> Expr<'R>) : Expr<'T -> 'R> =
        let var, expr = generateVar<'T> paramName
        Expr.Cast<_>(Expr.Lambda(var,  f expr))

    let lambda2 param1Name param2Name (f : Expr<'T> -> Expr<'S> -> Expr<'R>) : Expr<'T -> 'S -> 'R> =
        let var, expr = generateVar<'T> param1Name
        let var', expr' = generateVar<'S> param2Name
        Expr.Cast<_>(Expr.Lambda(var, Expr.Lambda(var',  f expr expr')))


(*
    This code is more a less a direct port of https://github.com/strymonas/staged-streams.ocaml/blob/master/lib/stream_combinators.ml to F#
    There are some minor differences due to F# not supporting rank 2 types and existential types, so this is why you will see various interfaces with Accept and Invoke to facilitate that
*)
module Streams =
    type CardType = AtMost1 | Many
    
    and ProducerShape<'T, 'S> =
        | For    of ProducerFor<'T, 'S>
        | Unfold of ProducerUnfold<'T, 'S>

    and ProducerFor<'T, 'S> =
        { Upb :   'S -> Expr<int>;
          Index : 'S -> Expr<int> -> ('T -> Expr<unit>) -> Expr<unit> }

    and ProducerUnfold<'T, 'S> =
        { Term : 'S -> Expr<bool>;
          Card : CardType;
          Step : 'S -> ('T -> Expr<unit>) -> Expr<unit> }

    type Init<'S> = 
        abstract member Invoke<'R> : ('S -> Expr<'R>) -> Expr<'R>

    type Producer<'T> =
        abstract Accept : ProducerFunc<'T, 'R> -> 'R

    and Producer<'T, 'S> = 
        { Init : Init<'S>; Shape : ProducerShape<'T, 'S> }
        interface Producer<'T> with
            member p.Accept f = f.Invoke<'S> p

    and ProducerFunc<'T, 'R> =
        abstract Invoke<'S> : Producer<'T, 'S> -> 'R

    type StStream<'T> =
        | Linear of Producer<'T>
        | Nested of NestedStream<'T>

    and NestedStream<'T> =
        abstract Accept : NestedStreamFunc<'T, 'R> -> 'R

    and NestedStream<'T, 'U> =
        { Producer : Producer<'T>; GetNestedStream : 'T -> StStream<'U> }
        interface NestedStream<'U> with
            member ns.Accept f = f.Invoke<'T> ns

    and NestedStreamFunc<'U, 'R> =
        abstract Invoke<'T> : NestedStream<'T, 'U> -> 'R

    type Stream<'T> = StStream<Expr<'T>>

    module Producer =
        let forUnfold (producer : Producer<'T>) =
            let forUnfold' { Init=init; Shape=shape } =
                match shape with
                | For { Upb=upb; Index=index } -> 
                    let init k = 
                        let init' s0 = ExprHelpers.genLet "i" <@ ref 0 @> (fun i -> k (i, s0))
                        init.Invoke init'

                    let term (i, s0) = <@ !(%i) <= (% upb s0) @>
                    let step (i, s0) k =
                        let step' a = <@ incr %i; (% k a) @>
                        index s0 <@ !(%i) @> step'

                    let initObj = { new Init<_> with member _.Invoke i = init i }
                    { Init=initObj; Shape = Unfold { Term=term; Card=Many; Step=step } } :> Producer<_>
                | _ -> producer
            producer.Accept { new ProducerFunc<_, _> with member _.Invoke p = forUnfold' p }

        let rec zipProducer (p1 : Producer<'T>) (p2 : Producer<'U>) =
            let zipProducer' prod1 prod2 =
                match (prod1, prod2) with
                | ({ Shape=For f1 }, { Shape=For f2 }) ->
                    let init =
                        { new Init<_> with
                            member _.Invoke k =
                                prod1.Init.Invoke (fun s1 -> prod2.Init.Invoke (fun s2 -> k (s1, s2))) }
                    let upb (s1, s2) = <@ min (% f1.Upb s1) (% f2.Upb s2) @>
                    let index (s1, s2) i k =
                        f1.Index s1 i (fun e1 -> f2.Index s2 i (fun e2 -> k (e1, e2)))
                    { Init=init; Shape=For { Upb=upb; Index=index } } :> Producer<_>
                | ({ Shape=Unfold u1 }, { Shape=Unfold u2 }) ->
                    let init =
                        { new Init<_> with
                            member _.Invoke k =
                                prod1.Init.Invoke (fun s1 -> prod2.Init.Invoke (fun s2 -> k (s1, s2))) }
                    let term (s1, s2) = <@ (% u1.Term s1) && (% u2.Term s2) @>
                    let step (s1, s2) k = u1.Step s1 (fun e1 -> u2.Step s2 (fun e2 -> k (e1, e2)))
                    { Init=init; Shape=Unfold { Term=term; Card=Many; Step=step } } :> Producer<_>
                | _ -> zipProducer (forUnfold prod1) (forUnfold prod2)

            p1.Accept { new ProducerFunc<_, _> with member _.Invoke prod1 = p2.Accept { new ProducerFunc<_, _> with member _.Invoke prod2 = zipProducer' prod1 prod2 } }

    module StStream =
        type FoldRaw = abstract Invoke<'T> : ('T -> Expr<unit>) -> StStream<'T> -> Expr<unit>
        let rec private foldRaw' consumer stream =
            match stream with
            | Linear prod ->
                let handleProd { Init=init; Shape=shape } =
                    let getProducerCode sp =
                        match shape with
                        | For { Upb=upb; Index=index } ->
                            ExprHelpers.genFor "i" <@ 0 @> (upb sp) (fun i -> index sp i consumer)
                        | Unfold { Term=term; Card=AtMost1; Step=step } ->
                            <@ if (% term sp) then (% step sp consumer) @>
                        | Unfold { Term=term; Step=step } ->
                            <@ while (% term sp) do (% step sp consumer) @>
                    init.Invoke getProducerCode
                prod.Accept { new ProducerFunc<_, _> with member _.Invoke p = handleProd p }
            | Nested nestedStream ->
                let handleNestedStream { Producer=prod; GetNestedStream=nestf } =
                    foldRaw.Invoke (fun e -> foldRaw.Invoke consumer (nestf e)) (Linear prod)
                nestedStream.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNestedStream ns }
        and foldRaw : FoldRaw = { new FoldRaw with member _.Invoke consumer stream = foldRaw' consumer stream }

        type MapRaw = abstract Invoke<'T, 'U> : ('T -> ('U -> Expr<unit>) -> Expr<unit>) -> StStream<'T> -> StStream<'U>
        let rec private mapRaw' f stream =
            match stream with
            | Linear prod ->
                let handleProd { Init=init; Shape=shape} =
                    match shape with
                    | For { Upb=upb; Index=index } -> 
                        let index s i k = index s i (fun e -> f e k)
                        Linear { Init=init; Shape=For { Upb=upb; Index=index } }
                    | Unfold { Term=term; Card=card; Step=step } ->
                        let step s k = step s (fun e -> f e k)
                        Linear { Init=init; Shape=Unfold { Term=term; Card=card; Step=step } }
                prod.Accept { new ProducerFunc<_, _> with member _.Invoke p = handleProd p }
            | Nested nestedStream ->
                let handleNestedStream { Producer=prod; GetNestedStream=nestf } =
                    Nested { Producer = prod; GetNestedStream = (fun a -> mapRaw.Invoke f (nestf a)) }
                nestedStream.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNestedStream ns }
        and mapRaw : MapRaw = { new MapRaw with member _.Invoke f stream = mapRaw' f stream }
            

        let rec flatMapRaw f stream =
            match stream with
            | Linear prod -> 
                prod.Accept 
                    { new ProducerFunc<_, _> with 
                        member _.Invoke(prod) = Nested { Producer=prod; GetNestedStream=f} }
            | Nested nestedStream ->
                nestedStream.Accept
                    { new NestedStreamFunc<_, _> with
                        member _.Invoke { Producer=prod; GetNestedStream=nestf } =
                            let getNested a = flatMapRaw f (nestf a)
                            Nested { Producer=prod; GetNestedStream=getNested} }

        let rec moreTermination newTerm str =
            let rec addToProducer newTerm (prod : Producer<_>) =
                prod.Accept
                    { new ProducerFunc<_, _> with 
                        member _.Invoke(prod) =
                            match prod with
                            | { Shape=Unfold { Card=AtMost1 } } -> prod :> Producer<_>
                            | { Shape=Unfold ({ Card=Many; Term=term } as u) } ->
                                let term s = <@ %newTerm && (% term s) @>
                                { prod with Shape=Unfold { u with Term=term } } :> Producer<_>
                            | _ -> addToProducer newTerm (Producer.forUnfold prod) }
            match str with
            | Linear prod -> Linear (addToProducer newTerm prod)
            | Nested nested ->
                nested.Accept
                    { new NestedStreamFunc<_, _> with
                        member _.Invoke { Producer=prod; GetNestedStream=nestf } =
                            let prod' = addToProducer newTerm prod
                            let nestf' a = moreTermination newTerm (nestf a)
                            Nested { Producer=prod'; GetNestedStream=nestf' } }

        type AddNR =
            abstract Invoke<'T> : Expr<int> -> Producer<'T> -> Producer<Expr<int ref> * 'T>

        let takeRaw (n : Expr<int>) (str : StStream<'a>) : StStream<'a> =
            let addNR =
                { new AddNR with
                    member _.Invoke n prod =
                        prod.Accept
                            { new ProducerFunc<_, _> with
                                member _.Invoke { Init=init; Shape=shape } =
                                    match shape with
                                    | Unfold { Term=term; Card=card; Step=step } ->
                                        let init = 
                                            { new Init<_> with
                                                member _.Invoke k =
                                                    let init' s = ExprHelpers.genLet "nr" <@ ref %n @> (fun nr -> k (nr, s))
                                                    init.Invoke init' }
                                        let prod =
                                            Unfold
                                                { Card=card
                                                  Term=(fun (nr, s) -> if card = Many then <@ !(%nr) > 0 && (% term s) @> else term s)
                                                  Step=(fun (nr, s) k -> step s (fun el -> k (nr, el))) }
                                        { Init=init; Shape=prod } :> Producer<_> } }
            let updateNR (nr, el) k = <@ decr %nr; (% k el) @>
            match str with
            | Linear prod ->
                prod.Accept
                    { new ProducerFunc<_, _> with
                        member _.Invoke(prod) =
                            match prod with
                            | {Shape=For ({Upb=upb} as f)} ->
                                let upb s = <@ min (%n - 1) (%upb s) @>
                                Linear { prod with Shape=For { f with Upb=upb} }
                            | prod ->
                                mapRaw.Invoke updateNR (Linear (addNR.Invoke n prod)) }
            | Nested nested ->
                nested.Accept
                    { new NestedStreamFunc<_, _> with
                        member _.Invoke { Producer=prod; GetNestedStream=nestf } =
                            let prod' = addNR.Invoke n (Producer.forUnfold prod)
                            let nestf' (nr, a) = mapRaw.Invoke (fun a -> updateNR (nr, a)) (moreTermination <@ !(%nr) > 0 @> (nestf a))
                            Nested { Producer=prod'; GetNestedStream=nestf' } }

        let pushLinear (prod1 : Producer<_>) ((prod2 : Producer<_>), nestf2) =
            let pushLinear' { Init=init1; Shape=Unfold {Card=Many; Term=term1; Step=step1 }} { Init=init2; Shape=Unfold p2 } =
                let init =
                    { new Init<_> with
                        member _.Invoke k =
                            let init' s1 s2 = 
                                ExprHelpers.genLet "term1r" <@ ref (% term1 s1) @> (fun term1r -> k (term1r, s1, s2))
                            init1.Invoke (fun s1 -> init2.Invoke (fun s2 -> init' s1 s2)) }
                let term (term1r, s1, s2) = <@ !(%term1r) && (% p2.Term s2) @>
                let step (term1r, s1, s2) k = p2.Step s2 (fun b -> k (term1r, s1, b))
                let prod = { Init=init; Shape=Unfold { Term=term; Card=Many; Step=step } }
                let getNested (term1r, s1, b) =
                    mapRaw.Invoke (fun c k -> step1 s1 (fun a -> <@ %term1r := (% term1 s1); (% k (a, c)) @>)) (moreTermination <@ !(%term1r) @> (nestf2 b))
                Nested { Producer = prod; GetNestedStream=getNested }
            prod1.Accept { new ProducerFunc<_, _> with member _.Invoke p1 = prod2.Accept { new ProducerFunc<_, _> with member _.Invoke p2 = pushLinear' p1 p2 }}

        type MakeAdv =
            abstract Invoke<'T> : Expr<(unit -> unit) option ref> -> ('T -> Expr<unit>) -> StStream<'T> -> Expr<unit>

        let rec makeLinear stream =
            let rec makeAdv' (nadv : Expr<(unit -> unit) option ref>) k stream =
                match stream with
                | Linear prod ->
                    let handleProd { Init=init; Shape=shape } =
                        match shape with
                        | Unfold { Card=AtMost1; Term=term; Step=step } ->
                            init.Invoke (fun s -> <@ if (% term s) then (% step s k) @>)
                        | Unfold { Term=term; Step=step } ->
                            init.Invoke (fun s ->
                                ExprHelpers.genLet "oldAdv" <@ !(%nadv) @> (fun oldAdv ->
                                    ExprHelpers.genLet "adv1"
                                        (ExprHelpers.lambda "unit" (fun _ ->
                                            <@ if (% term s) then (% step s k) else (%nadv) := %oldAdv @>))
                                        (fun adv1 -> <@ (%nadv) := Some %adv1; (%adv1) () @>)))
                    prod.Accept { new ProducerFunc<_, _> with member _.Invoke p = handleProd p }
                | Nested nestedStream ->
                    let handleNestedStream { Producer=prod; GetNestedStream=nestf } =
                        makeAdv.Invoke nadv (fun e -> makeAdv.Invoke nadv k (nestf e)) (Linear prod)
                    nestedStream.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNestedStream ns }
            and makeAdv : MakeAdv = { new MakeAdv with member _.Invoke nadv k stream = makeAdv' nadv k stream }

            match stream with
            | Linear prod -> prod
            | Nested nested ->
                let handleNestedStream { Producer=prod; GetNestedStream=nestf } =
                    let handleProd { Init=init; Shape=shape } =
                        match shape with
                        | For _ -> makeLinear (Nested { Producer=Producer.forUnfold prod; GetNestedStream=nestf })
                        | Unfold { Card=Many; Term=term; Step=step } ->
                            let init k =
                                let init' s0 =
                                    ExprHelpers.genLet2 
                                        "curr" <@ ref None @> 
                                        "nadv" <@ ref None @> 
                                        (fun curr nadv ->
                                            ExprHelpers.genLet "adv"
                                                (ExprHelpers.lambda "unit" (fun _ ->
                                                    <@
                                                        %curr := None
                                                        while !(%curr) = None && (Option.isSome !(%nadv) || (% term s0)) do
                                                            (%
                                                                ExprHelpers.genMatchOption "adv" <@ !(%nadv) @>
                                                                    (fun adv -> <@ (%adv) () @>)
                                                                    (step s0 (fun e0 -> makeAdv.Invoke nadv (fun e -> <@ %curr := Some %e @>) (nestf e0))))
                                                    @>))
                                                (fun adv -> <@ (%adv) (); (% k (curr, adv)) @>))
                                init.Invoke init'
                            let term (curr, _) = <@ !(%curr) <> None @>
                            let step (curr, adv) k =
                                ExprHelpers.genLet "currVal" <@ !(%curr) @> (fun currVal ->
                                    ExprHelpers.genMatchOption "el" currVal
                                        (fun el -> <@ (%adv) (); (% k el) @>)
                                        <@ () @>)
                            let initObj = { new Init<_> with member _.Invoke i = init i }
                            { Init=initObj; Shape=Unfold { Card=Many; Term=term; Step=step } } :> Producer<_>
                    prod.Accept { new ProducerFunc<_, _> with member _.Invoke p = handleProd p }
                nested.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNestedStream ns }

        let rec zipRaw str1 str2 =
            match (str1, str2) with
            | (Linear prod1, Linear prod2) -> Linear (Producer.zipProducer prod1 prod2)
            | (Linear prod1, Nested nested) ->
                let handleNested { Producer=prod2; GetNestedStream=nestf } =
                    pushLinear (Producer.forUnfold prod1) (Producer.forUnfold prod2, nestf)
                nested.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNested ns }
            | (Nested nested, Linear prod2) ->
                let handleNested { Producer=prod1; GetNestedStream=nestf } =
                    mapRaw.Invoke (fun (y, x) k -> k (x, y)) (pushLinear (Producer.forUnfold prod2) (Producer.forUnfold prod1, nestf))
                nested.Accept { new NestedStreamFunc<_, _> with member _.Invoke ns = handleNested ns }
            | (Nested _, Nested _) ->
                zipRaw (Linear (makeLinear str1)) str2

    module Stream =
        let fold f z str =
            let foldRawBody s = 
                let consumer a = <@ %s := (% f <@ !(%s) @> a) @>
                <@ (% StStream.foldRaw.Invoke consumer str); !(%s) @>
            ExprHelpers.genLet "s" <@ ref %z @> foldRawBody

        let foldTupled f1 z1 f2 z2 str =
            let foldRawBody s1 s2 =
                let consumer a = <@ %s1 := (% f1 <@ !(%s1) @> a); %s2 := (% f2 <@ !(%s2) @> a) @>
                <@ (% StStream.foldRaw.Invoke consumer str); !(%s1), !(%s2) @>

            ExprHelpers.genLet2 "s1" <@ ref %z1 @> "s2" <@ ref %z2 @> foldRawBody

        let ofArray arr =
            let init k = ExprHelpers.genLet "arr" arr k
            let upb arr = <@ (Array.length %arr) - 1 @>
            let index arr i k = ExprHelpers.genLet "elem" <@ Array.item %i %arr @> k

            let initObj = { new Init<_> with member _.Invoke k = init k }
            Linear { Init=initObj; Shape=For { Upb=upb; Index=index } }

        let unfold (p : Expr<'z> -> Expr<Option<'a * 'z>>) (z : Expr<'z>) : Stream<'a> =
            let init k = ExprHelpers.genLet "s" <@ ref (% p z) @> k
            let term s = <@ !(%s) <> None @>

            let step s body =
                ExprHelpers.genLet "sVal" <@ !(%s) @> (fun sVal ->
                    ExprHelpers.genMatchOption "s'" sVal
                        (fun s' -> ExprHelpers.genUnpackTuple "el" "state" s' (fun el state -> <@ (%s) := (% p state); (% body el) @>))
                        <@ () @>)

            let initObj = { new Init<_> with member _.Invoke k = init k }
            Linear { Init=initObj; Shape=Unfold { Term=term; Card=Many; Step=step } }

        let map f stream =
            let mapExpr a k = ExprHelpers.genLet "t" (f a) k
            StStream.mapRaw.Invoke mapExpr stream

        let flatMap f stream = StStream.flatMapRaw f stream

        let filter f stream =
            let producer a =
                let init = { new Init<_> with member _.Invoke k = k a }    
                { Init=init; Shape=Unfold { Card=AtMost1; Term=f; Step=(fun a k -> k a) } }
            StStream.flatMapRaw (fun x -> Linear (producer x)) stream

        let take n stream = StStream.takeRaw n stream

        let zipWith f str1 str2 = StStream.mapRaw.Invoke (fun (x, y) k -> k (f x y)) (StStream.zipRaw str1 str2)