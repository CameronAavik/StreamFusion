namespace Streams

open System
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Reflection

module Msp =
    let counter = ref 0
    let generateVar (typ : Type) : Var = 
        incr counter
        new Var(sprintf "__genVar_%d" !counter, typ)

    let lambda (f : Expr<'T> -> Expr<'R>) : Expr<'T -> 'R> =
        let var = generateVar typeof<'T>
        Expr.Cast<_>(Expr.Lambda(var,  f (Expr.Cast<_>(Expr.Var var))))

    let lambda2 (f : Expr<'T> -> Expr<'S> -> Expr<'R>) : Expr<'T -> 'S -> 'R> =
        let var = generateVar typeof<'T>
        let var' = generateVar typeof<'S>
        Expr.Cast<_>(Expr.Lambda(var, Expr.Lambda(var',  f (Expr.Cast<_>(Expr.Var var)) (Expr.Cast<_>(Expr.Var var')))))

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
            producer.Accept
                { new ProducerFunc<_, _> with
                    member _.Invoke { Init=init; Shape=shape } = 
                        match shape with
                        | For { Upb=upb; Index=index } -> 
                            let iVar = Msp.generateVar typeof<int ref>
                            let iExpr = Expr.Cast<_>(Expr.Var(iVar))

                            let init =
                                { new Init<_> with
                                    member _.Invoke k = 
                                        let init' s0 =
                                            Expr.Cast<_>(Expr.Let(iVar, <@ ref 0 @>, k (iExpr, s0)))
                                        init.Invoke init' }

                            let term (i, s0) = <@ !(%i) <= (% upb s0) @>
                            let step (i, s0) k =
                                let step' a = <@ incr %i; (% k a) @>
                                index s0 <@ !(%i) @> step'

                            { Init=init; Shape = Unfold { Term=term; Card=Many; Step=step } } :> Producer<'T>
                        | _ -> producer }

    module StStream =
        type FoldRawData =
            abstract Accept : FoldRawDataFunc<'R> -> 'R
        and FoldRawData<'T> = 
            { Stream : StStream<'T>
              Consumer : 'T -> Expr<unit> }
            interface FoldRawData with member frd.Accept f = f.Invoke<'T> frd
        and FoldRawDataFunc<'R> =
            abstract Invoke<'T> : FoldRawData<'T> -> 'R

        let rec foldRaw (foldRawData : FoldRawData) =
            foldRawData.Accept
                { new FoldRawDataFunc<_> with
                    member _.Invoke { Stream=stream; Consumer=consumer } =
                        match stream with
                        | Linear prod ->
                            prod.Accept 
                                { new ProducerFunc<_, _> with 
                                    member _.Invoke { Init=init; Shape=shape } =
                                        let getProducerCode sp =
                                            match shape with
                                            | For { Upb=upb; Index=index } ->
                                                let iVar = Msp.generateVar typeof<int>
                                                let iExpr = Expr.Cast<int>(Expr.Var(iVar))
                                                Expr.Cast<_>(Expr.ForIntegerRangeLoop(iVar, <@ 0 @>, upb sp, <@ (% index sp iExpr consumer) @>))
                                            | Unfold { Term=term; Card=AtMost1; Step=step } ->
                                                <@ if (% term sp) then (% step sp consumer) @>
                                            | Unfold { Term=term; Step=step } ->
                                                <@ while (% term sp) do (% step sp consumer) @>
                                        init.Invoke getProducerCode }
                        | Nested nestedStream ->
                            nestedStream.Accept
                                { new NestedStreamFunc<_, _> with
                                    member _.Invoke { Producer=prod; GetNestedStream=nestf } =
                                        let data =
                                            { Stream = Linear prod
                                              Consumer = (fun e -> foldRaw {Stream=nestf e; Consumer=consumer }) }
                                        foldRaw data } }

        let rec mapRaw f stream =
            match stream with
            | Linear prod ->
                prod.Accept
                    { new ProducerFunc<_, _> with
                        member _.Invoke { Init=init; Shape=shape} =
                            match shape with
                            | For ({ Index=index } as forShape) -> 
                                let index s i k = index s i (fun e -> f e k)
                                Linear { Init=init; Shape=For { forShape with Index=index } }
                            | Unfold ({ Step=step } as unfoldShape) ->
                                let step s k = step s (fun e -> f e k)
                                Linear { Init=init; Shape=Unfold { unfoldShape with Step=step } } }
            | Nested nestedStream ->
                nestedStream.Accept
                    { new NestedStreamFunc<_, _> with
                        member _.Invoke { Producer=prod; GetNestedStream=nestf } =
                            Nested { Producer = prod; GetNestedStream = (fun a -> mapRaw f (nestf a)) } }

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
            

    module Stream =
        let foldExpr f z str =
            let sVar = Msp.generateVar typeof<'z ref>
            let sExpr = Expr.Cast<'z ref>(Expr.Var(sVar))
            let foldRawBody = 
                Expr.Sequential(
                    StStream.foldRaw
                        { StStream.FoldRawData.Stream = str
                          StStream.FoldRawData.Consumer = (fun a -> <@ %sExpr := (% f <@ !(%sExpr) @> a) @>)},
                    <@ !(%sExpr) @>)
            Expr.Cast<_>(Expr.Let(sVar, <@ ref %z @>, foldRawBody))

        let fold f z str = foldExpr f <@ z @> str

        let foldTupled f1 z1 f2 z2 str =
            let s1Var = Msp.generateVar typeof<'z1 ref>
            let s1Expr = Expr.Cast<'z1 ref>(Expr.Var(s1Var))
            let s2Var = Msp.generateVar typeof<'z2 ref>
            let s2Expr = Expr.Cast<'z2 ref>(Expr.Var(s2Var))
            let foldRawBody = 
                Expr.Sequential(
                    StStream.foldRaw
                        { StStream.FoldRawData.Stream = str
                          StStream.FoldRawData.Consumer = (fun a -> <@ %s1Expr := (% f1 <@ !(%s1Expr) @> a); %s2Expr := (% f2 <@ !(%s2Expr) @> a) @>)},
                    <@ !(%s1Expr), !(%s2Expr) @>)
            Expr.Cast<_>(
                Expr.Let(s1Var, <@ ref %z1 @>, 
                    Expr.Let(s2Var, <@ ref %z2 @>, foldRawBody)))

        let ofArrayExpr arr =
            let arrVar = Msp.generateVar typeof<'a array>
            let arrExpr = Expr.Cast<'a array>(Expr.Var(arrVar))
            let elemVar = Msp.generateVar typeof<'a>
            let elemExpr = Expr.Cast<'a>(Expr.Var(elemVar))

            let init = 
                { new Init<_> with 
                    member _.Invoke k = 
                        Expr.Cast<_>(
                            Expr.Let(arrVar, arr, 
                                k arrExpr)) }

            let upb arr = <@ (Array.length %arr) - 1 @>
            let index arr i k = Expr.Cast<_>(Expr.Let(elemVar, <@ Array.item %i %arr @>, k elemExpr))
            Linear { Init=init; Shape=For { Upb=upb; Index=index } }

        let ofArray arr = ofArrayExpr <@ arr @>

        let unfold (p : Expr<'z> -> Expr<Option<'a * 'z>>) (z : Expr<'z>) =
            let sVar = Msp.generateVar typeof<Option<'a * 'z> ref>
            let sExpr = Expr.Cast<Option<'a * 'z> ref>(Expr.Var(sVar))
            let matchVar = Msp.generateVar typeof<Option<'a * 'z>>
            let matchExpr = Expr.Cast<Option<'a * 'z>>(Expr.Var(matchVar))
            let elVar = Msp.generateVar typeof<'a>
            let elExpr = Expr.Cast<'a>(Expr.Var(elVar))
            let stateVar = Msp.generateVar typeof<'z>
            let stateExpr = Expr.Cast<'z>(Expr.Var(stateVar))

            let someUnionCase = FSharpType.GetUnionCases(typeof<Option<'a * 'z>>).[1]
            let valueOptionField = someUnionCase.GetFields().[0]

            let init = 
                { new Init<_> with 
                    member _.Invoke k = 
                        Expr.Cast<_>(Expr.Let(sVar, <@ ref (% p z) @>, k sExpr)) }

            let term s = <@ !(%s) <> None @>

            let extractOptionValueExpr = Expr.PropertyGet(matchExpr, valueOptionField)

            let step s body =
                Expr.Cast<_>(
                    Expr.Let(matchVar, <@ !(%s) @>,
                        Expr.IfThenElse(
                            Expr.UnionCaseTest(matchExpr, someUnionCase),
                            Expr.Let(stateVar, Expr.TupleGet(extractOptionValueExpr, 1),
                                Expr.Let(elVar, Expr.TupleGet(extractOptionValueExpr, 0),
                                    <@ (%s) := (% p %stateExpr); (% body %elExpr) @>)),
                            <@ () @>)))

            Linear { Init=init; Shape=Unfold { Term=term; Card=Many; Step=step } }

        let map f stream =
            let tVar = Msp.generateVar typeof<'b>
            let tExpr = Expr.Cast<'b>(Expr.Var(tVar))
            let mapExpr a k = Expr.Cast<_>(Expr.Let(tVar, f a, k tExpr))
            StStream.mapRaw mapExpr stream

        let flatMap f stream = StStream.flatMapRaw f stream

        let filter f stream =
            let producer a =
                let init = { new Init<_> with member _.Invoke k = k a }    
                { Init=init; Shape=Unfold { Card=AtMost1; Term=f; Step=(fun a k -> k a) } }
            StStream.flatMapRaw (fun x -> Linear (producer x)) stream

        