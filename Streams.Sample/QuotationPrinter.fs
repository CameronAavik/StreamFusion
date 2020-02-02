module QuotationPrinter
    type E = Microsoft.FSharp.Quotations.Expr
    type V = Microsoft.FSharp.Quotations.Var
    type FST = Microsoft.FSharp.Reflection.FSharpType

    module P = Microsoft.FSharp.Quotations.Patterns
    module DP = Microsoft.FSharp.Quotations.DerivedPatterns
    module Shape = Microsoft.FSharp.Quotations.ExprShape

    open System.CodeDom.Compiler

    let toString (e : E) = 
        let sw = new System.IO.StringWriter()
        let w = new IndentedTextWriter(sw)
    
        let tab() = w.Indent <- w.Indent + 1
        let newline() = w.WriteLine()
        let untab(newLine) = 
            w.Indent <- w.Indent - 1
            if newLine then newline()

        let print fmt = Printf.fprintf w fmt
        let println fmt = Printf.fprintfn w fmt

        let rec go (e : E) = 
            match e with
            | P.Var(v) -> print "%s" v.Name
            | P.Value(v, _) -> print "%A" v
            | P.NewRecord(ty, args) ->
                let fields = FST.GetRecordFields(ty)
                print "new %s {" ty.Name
                tab()
                (fields, args) 
                ||> Seq.zip 
                |> Seq.iteri (fun i (f, v) ->
                    if i <> 0 then
                        println "," 
                    print "%s = ( " f.Name
                    go(v)
                    print ")"            )            
                untab(true)
                println "}"
            | DP.SpecificCall <@ (=) @>(_, _, [a; b]) ->
                go(a)
                print " = "
                go(b)
            | DP.SpecificCall <@ (-) @> (_, _, [a; b]) ->
                go(a)
                print " - "
                go(b)
            | DP.SpecificCall <@ (*) @> (_, _, [a; b]) ->
                go(a)
                print " * "
                go(b)
            | DP.SpecificCall <@ (+) @> (_, _, [a; b]) ->
                go(a)
                print " + "
                go(b)
            | DP.SpecificCall <@ ignore @>(_, _, [a]) -> 
                print "ignore"
                go(a)
                print ")"
            | P.Let(var, value, body) -> 
                println "let %s : %s = " var.Name var.Type.Name
                tab()
                go(value)
                newline()
                println "in"
                go(body)
                untab(false)
            | P.LetRecursive([var, value], body) -> 
                println "let rec %s : %s = " var.Name var.Type.Name
                tab()
                go(value)
                newline()
                println "in"
                go(body)
                untab(false)
            | P.PropertyGet(Some inst, pi, _) -> 
                go(inst)
                print ".%s" pi.Name
            | P.NewObject(ci, args) ->
                print "new %s (" ci.DeclaringType.Name
                if List.length args > 0 then
                    tab()
                    newline()
                    args
                    |> Seq.iteri (fun i v ->
                        if i <> 0 then
                            println "," 
                        go(v)
                    )            
                    untab(true)
                println ")"
            | P.NewArray(ty, args) ->
                println "new %s [" ty.Name
                if List.length args > 0 then
                    tab()
                    args |> Seq.iteri (fun i arg ->
                        if i <> 0 then
                            println "," 
                        go(arg)
                    )
                    untab(true)
                println "]"
            | P.Call(_, mi, args) -> 
                println "%s (" mi.Name
                if List.length args > 0 then
                    tab()
                    args |> Seq.iteri (fun i arg ->
                        if i <> 0 then
                            println "," 
                        go(arg)
                    )
                    untab(true)
                println ")"
            | P.Application(app, arg) ->
                go(app)
                println "("
                tab()
                go(arg)
                untab(true)
                println ")"
            | P.WhileLoop(cond, body) ->
                println "while("
                go(cond)
                println ") {"
                tab()
                go(body)
                untab(true)
                println "}"
            | P.ForIntegerRangeLoop(var, s, e, body) -> 
                print "for("
                go (E.Var var)
                print " in "
                go(s)
                print ".."
                go(e)
                println " {"
                tab()
                go(body)
                untab(true)
                println "}"
            | P.Lambda(var, body) ->
                println "(fun %s : %s -> " var.Name var.Type.Name
                tab()
                go(body)
                untab(true)
                println ")"
            | P.IfThenElse(cond, ifTrue, ifFalse) ->
                println "if ("
                go(cond)
                println ") {"
                tab()
                go(ifTrue)
                untab(true)
                println "} else {"
                tab()
                go(ifFalse)
                untab(true)
                println "}"
            | P.UnionCaseTest(e, ucase) -> 
                print "UnionCaseTest ("
                go(e)
                print ") is %s" ucase.Name
            | P.NewUnionCase(ucase, args) ->
                print "%s" ucase.Name
                if List.length args > 0 then
                    tab()
                    newline()
                    args
                    |> Seq.iteri (fun i v ->
                        if i <> 0 then
                            println "," 
                        go(v)
                    )            
                    untab(true)
                println ")"
            | P.Sequential(a, b) ->
                go(a)
                newline()
                go(b)
            | P.PropertySet(Some inst, pi, _, value) ->
                go(inst)
                print ".%s <-" pi.Name
                go(value)
            | P.FieldGet(Some inst, fi) ->
                go(inst)
                print ".%s" fi.Name
            | P.FieldSet(Some inst, fi, value) ->
                go(inst)
                print ".%s <-" fi.Name
                go(value)
            | P.TupleGet(expr, idx) ->
                print "TupleGet ("
                go (expr)
                print ", %i)" idx
            | P.NewTuple(exprs) ->
                match exprs with
                | [] -> print "()"
                | x :: xs ->
                    print "("
                    go (x)
                    xs |> Seq.iter (fun expr ->
                        print ", "
                        go (expr))
                    print ")"
            | x -> failwithf "unexpected %A" x
        
        go(e)
        sw.ToString()

    let normalize (s : string) = 
        s.Replace("\r", "")
         .Split([|'\n'|], System.StringSplitOptions.RemoveEmptyEntries) 
         |> Array.map (fun s -> s.Trim()) |> String.concat "\n"