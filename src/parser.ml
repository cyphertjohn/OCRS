type token =
  | INT of (int)
  | FLOAT of (float)
  | VAR of (string)
  | COMMA
  | UNDERSCORE
  | BINOMIAL
  | EQUALS
  | LESS
  | LESSEQ
  | GREATER
  | GREATEREQ
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | POW
  | LPAREN
  | RPAREN
  | LCURL
  | RCURL
  | EOL
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Type_def

let rec substitute_expr expr old_term new_term =
  if expr = old_term then new_term
  else
    (match expr with
    | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ | Output_variable _ ->
      expr
    | Pow (base, exp) ->
      Pow (substitute_expr base old_term new_term, substitute_expr exp old_term new_term)
    | Times (left, right) ->
      Times (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Plus (left, right) ->
      Plus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Minus (left, right) ->
      Minus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Divide (left, right) ->
      Divide (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Binomial (left, right) ->
      Binomial (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Log (base, expression) ->
      Log (base, substitute_expr expression old_term new_term)
    | Factorial expression ->
      Factorial (substitute_expr expression old_term new_term)
    | Product prodList ->
      Product (List.map (fun x -> substitute_expr x old_term new_term) prodList)
    | Sum sumList ->
      Sum (List.map (fun x -> substitute_expr x old_term new_term) sumList))
  ;;

let substitute ineq old_term new_term =
  match ineq with
  | Equals (left, right) ->
    Equals(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Less (left, right) ->
    Less(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | LessEq (left, right) ->
    LessEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Greater (left, right) ->
    Greater(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | GreaterEq (left, right) ->
    GreaterEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  ;;  
# 72 "parser.ml"
let yytransl_const = [|
  260 (* COMMA *);
  261 (* UNDERSCORE *);
  262 (* BINOMIAL *);
  263 (* EQUALS *);
  264 (* LESS *);
  265 (* LESSEQ *);
  266 (* GREATER *);
  267 (* GREATEREQ *);
  268 (* PLUS *);
  269 (* MINUS *);
  270 (* TIMES *);
  271 (* DIV *);
  272 (* POW *);
  273 (* LPAREN *);
  274 (* RPAREN *);
  275 (* LCURL *);
  276 (* RCURL *);
  277 (* EOL *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* FLOAT *);
  259 (* VAR *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\004\000\004\000\
\004\000\004\000\004\000\000\000"

let yylen = "\002\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\001\000\
\001\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000\
\003\000\005\000\005\000\003\000\003\000\001\000\003\000\003\000\
\003\000\003\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\009\000\000\000\000\000\000\000\028\000\
\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\021\000\020\000\000\000\000\000\010\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\001\000\002\000\000\000\
\000\000\019\000\018\000\023\000\025\000\024\000\026\000"

let yydgoto = "\002\000\
\008\000\009\000\010\000\044\000"

let yysindex = "\004\000\
\024\255\000\000\000\000\000\000\004\255\024\255\024\255\000\000\
\061\255\123\255\005\255\000\000\017\255\025\255\024\255\024\255\
\024\255\024\255\024\255\024\255\024\255\024\255\024\255\024\255\
\024\255\000\000\000\000\076\255\076\255\000\000\001\000\075\255\
\134\255\134\255\134\255\134\255\134\255\137\255\137\255\250\254\
\250\254\075\255\248\254\085\255\095\255\000\000\000\000\037\255\
\111\255\000\000\000\000\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\036\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\049\255\
\120\255\121\255\122\255\138\255\140\255\098\255\110\255\074\255\
\086\255\062\255\016\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\252\255\098\000"

let yytablesize = 278
let yytable = "\015\000\
\047\000\012\000\013\000\048\000\001\000\026\000\049\000\027\000\
\011\000\025\000\032\000\033\000\034\000\035\000\036\000\037\000\
\038\000\039\000\040\000\041\000\042\000\028\000\015\000\029\000\
\003\000\004\000\005\000\031\000\021\000\022\000\023\000\024\000\
\025\000\027\000\030\000\027\000\006\000\052\000\053\000\022\000\
\007\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
\022\000\022\000\022\000\022\000\017\000\022\000\017\000\017\000\
\017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
\014\000\015\000\017\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\015\000\013\000\043\000\015\000\
\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
\013\000\014\000\025\000\013\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\011\000\050\000\014\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\054\000\
\055\000\012\000\051\000\011\000\012\000\012\000\012\000\012\000\
\012\000\012\000\012\000\003\000\004\000\005\000\045\000\012\000\
\015\000\016\000\017\000\018\000\019\000\020\000\021\000\022\000\
\023\000\024\000\025\000\015\000\000\000\006\000\015\000\007\000\
\000\000\021\000\022\000\023\000\024\000\025\000\023\000\024\000\
\025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\046\000"

let yycheck = "\006\001\
\000\000\006\000\007\000\012\001\001\000\001\001\015\001\003\001\
\005\001\016\001\015\000\016\000\017\000\018\000\019\000\020\000\
\021\000\022\000\023\000\024\000\025\000\017\001\006\001\019\001\
\001\001\002\001\003\001\003\001\012\001\013\001\014\001\015\001\
\016\001\018\001\018\001\020\001\013\001\001\001\002\001\004\001\
\017\001\006\001\007\001\008\001\009\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\004\001\018\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\004\001\004\001\018\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\004\001\003\001\018\001\
\007\001\008\001\009\001\010\001\011\001\012\001\013\001\014\001\
\015\001\004\001\016\001\018\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\004\001\018\001\018\001\
\007\001\008\001\009\001\010\001\011\001\012\001\013\001\001\001\
\002\001\004\001\020\001\018\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\004\001\004\001\004\001\029\000\018\001\
\006\001\007\001\008\001\009\001\010\001\011\001\012\001\013\001\
\014\001\015\001\016\001\006\001\255\255\004\001\006\001\004\001\
\255\255\012\001\013\001\014\001\015\001\016\001\014\001\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\021\001"

let yynames_const = "\
  COMMA\000\
  UNDERSCORE\000\
  BINOMIAL\000\
  EQUALS\000\
  LESS\000\
  LESSEQ\000\
  GREATER\000\
  GREATEREQ\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  POW\000\
  LPAREN\000\
  RPAREN\000\
  LCURL\000\
  RCURL\000\
  EOL\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  FLOAT\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'ineq) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 64 "parser.mly"
                              ( (substitute _1 (Symbolic_Constant _3) (Input_variable _3)) )
# 257 "parser.ml"
               : Type_def.inequation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'ineq) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 65 "parser.mly"
                             ( (substitute _1 (Symbolic_Constant _3) (Input_variable _3)) )
# 265 "parser.ml"
               : Type_def.inequation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                     ( Equals(_1, _3) )
# 273 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                   ( Less(_1, _3) )
# 281 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                     ( LessEq(_1, _3) )
# 289 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 72 "parser.mly"
                      ( Greater(_1, _3) )
# 297 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                        ( GreaterEq(_1, _3) )
# 305 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 76 "parser.mly"
              ( Rational(Mpq.init_set_si _1 1) )
# 312 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 77 "parser.mly"
                            ( Rational(Mpq.init_set_d (_1)) )
# 319 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 78 "parser.mly"
                            ( _2 )
# 326 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 79 "parser.mly"
                            ( Plus(_1, _3) )
# 334 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 80 "parser.mly"
                            ( Minus(_1, _3) )
# 342 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 81 "parser.mly"
                            ( Times(_1, _3) )
# 350 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                            ( Divide(_1, _3) )
# 358 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                      ( Pow(_1, _3) )
# 366 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                            ( Times(Rational (Mpq.init_set_si (-1) 1), _2) )
# 373 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                           ( Binomial(_1, _3) )
# 381 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'sub) in
    Obj.repr(
# 86 "parser.mly"
                                        ( Output_variable (_1, _4) )
# 389 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'sub) in
    Obj.repr(
# 87 "parser.mly"
                                        ( Output_variable (_1, _4) )
# 397 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 88 "parser.mly"
                            ( Output_variable (_1, SSVar _3) )
# 405 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "parser.mly"
                           ( Symbolic_Constant (_1 ^ "_" ^ (string_of_int _3)) )
# 413 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
              ( Symbolic_Constant (_1) )
# 420 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 93 "parser.mly"
                 ( SAdd (_1, _3) )
# 428 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 94 "parser.mly"
                 ( SSDiv (_1, _3) )
# 436 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 95 "parser.mly"
                   ( SAdd (_1, int_of_float _3) )
# 444 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 96 "parser.mly"
                  ( SSDiv (_1, int_of_float _3) )
# 452 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 97 "parser.mly"
          ( SSVar _1 )
# 459 "parser.ml"
               : 'sub))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Type_def.inequation)
