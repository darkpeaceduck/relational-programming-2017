open GT
open MiniKanren
open MiniKanrenStd

@type ('string, 'int, 'expr) expr = 
  | Var   of 'string 
  | Op    of 'string * 'expr * 'expr
  | Const of 'int with show, gmap

@type ('string, 'expr, 'args, 'command) command = 
  | Assign of 'string * 'expr 
  | If     of 'expr * 'command * 'command
  | While  of 'expr * 'command
  | Return of 'expr 
  | Seq    of 'command * 'command 
  | Block  of 'args * 'command with show, gmap

@type ('string, 'args, 'body) func = Func of 'string * 'args * 'body with show, gmap 

let reify_env e = List.reify reify e
let show_env  e = show(List.logic) (show(logic) (show(string))) e

module LExpr = Fmap3 (
  struct
    type ('a, 'b, 'c) t = ('a, 'b, 'c) expr
    let fmap fa fb fc x = gmap(expr) fa fb fc x
  end
)

let var   s     = Var   s        |> LExpr.distrib |> inj
let op    s x y = Op   (s, x, y) |> LExpr.distrib |> inj
let const x     = Const x        |> LExpr.distrib |> inj

let reify_expr e = 
  let rec r e = LExpr.reify reify reify r @@ e in
  r e

let rec show_expr e = 
  show(logic) 
    (show(expr)
       (show(logic) (show(string)))
       (show(logic) (show(int)))
       show_expr
    ) e

module LCommand = Fmap4 (
  struct
    type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) command
    let fmap fa fb fc fd x = gmap(command) fa fb fc fd x
  end
)

let assign s e   = Assign (s, e)    |> LCommand.distrib |> inj
let cond   c t e = If     (c, t, e) |> LCommand.distrib |> inj
let loop   c e   = While  (c, e)    |> LCommand.distrib |> inj
let return e     = Return  e        |> LCommand.distrib |> inj
let seq    s1 s2 = Seq    (s1, s2)  |> LCommand.distrib |> inj
let block  vs s  = Block  (vs, s)   |> LCommand.distrib |> inj

let rec reify_command c = LCommand.reify reify reify_expr reify_env reify_command c
let rec show_command c =
  show(logic) (
    show(command) 
      (show(logic) (show(string)))
      show_expr
      show_env
      show_command
  ) c

module LFunc = Fmap3 (
  struct
    type ('a, 'b, 'c) t = ('a, 'b, 'c) func
    let fmap fa fb fc x = gmap(func) fa fb fc x
  end
)

let reify_func f = LFunc.reify reify reify_env reify_command f
let show_func  f = 
  show(logic) 
    (show(func)
       (show(logic) (show(string)))
       show_env
       show_command
    ) f

let func name args body = Func (name, args, body) |> LFunc.distrib |> inj 

let (!) = (!!)

let rec lookupo env s =
  fresh (h t) (
    (env === h % t) &&&
    ((h === s) |||
     ((h =/= s) &&& (lookupo t s))
    )
  )

let rec wfExpr env expr =
  conde [
    fresh (s x y) (
      (expr === op s x y) &&&
      (wfExpr env x) &&&
      (wfExpr env y)
    );
    fresh (i) (expr === const i);
    fresh (s) (
       (expr === var s) &&&
       (lookupo env s)
    )
  ]    

let rec wfCommand env command =
  conde [
    fresh (s e) ?& [command === assign s e;
                    wfExpr env e;
                    lookupo env s];
    fresh (c t e) ?& [command === cond c t e;
                      wfExpr env c;
                      wfCommand env t;
                      wfCommand env e];
    fresh (c b) ?& [command === loop c b;
                    wfExpr env c;
                    wfCommand env b];
    fresh (e) ?& [command === return e; wfExpr env e];
    fresh (s1 s2) ?& [command === seq s1 s2;
                      wfCommand env s1;
                      wfCommand env s2];
    fresh (vs s) ?& [command === block vs s;
                     fresh (env')
                        (List.appendo env vs env')
                        (wfCommand env' s)
                    ]
  ]

let wfFunc f =
  fresh (name args body) 
    ((args === (!"a" % (!"b" %< !"c"))) &&& 
     (wfCommand args body) &&& 
     (f === func name args body))
   
let _ =
  run q (fun q  -> wfExpr q (op !"+" (var !"a") (var !"b")))
        (fun qs ->
           List.iter (fun e -> Printf.printf "%s\n" (show_env (e#reify reify_env)))
                     (Stream.take ~n:10 qs) 
        )

let _ =
  run q (fun q  -> wfExpr (!"a" % (!"b" %< !"c")) q)
        (fun qs ->
           List.iter (fun e -> Printf.printf "%s\n-----------\n" (show_expr (e#reify reify_expr)))
                     (Stream.take ~n:10 qs) 
        )

let _ =
  run q (fun q  -> wfFunc q)
        (fun qs ->
           List.iter (fun f -> Printf.printf "%s\n-----------\n" (show_func (f#reify reify_func)))
                     (Stream.take ~n:10000 qs) 
        )


