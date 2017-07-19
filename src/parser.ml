type token =
  | INT of (int)
  | FLOAT of (float)
  | VAR of (string)
  | COMMA
  | UNDERSCORE
  | PI
  | BINOMIAL
  | MOD
  | FLOOR
  | SIN
  | COS
  | ARCTAN
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
    | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ | Output_variable _ | Arctan _ | Pi | Iif _ ->
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
      Sum (List.map (fun x -> substitute_expr x old_term new_term) sumList)
    | IDivide (num, denom) ->
      IDivide (substitute_expr num old_term new_term, denom)
    | Sin expression ->
      Sin (substitute_expr expression old_term new_term)
    | Cos expression ->
      Cos (substitute_expr expression old_term new_term)
    | Mod (left, right) ->
      Mod (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Shift (shift_v, expression) ->
      Shift (shift_v, substitute_expr expression old_term new_term))
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
# 88 "parser.ml"
let yytransl_const = [|
  260 (* COMMA *);
  261 (* UNDERSCORE *);
  262 (* PI *);
  263 (* BINOMIAL *);
  264 (* MOD *);
  265 (* FLOOR *);
  266 (* SIN *);
  267 (* COS *);
  268 (* ARCTAN *);
  269 (* EQUALS *);
  270 (* LESS *);
  271 (* LESSEQ *);
  272 (* GREATER *);
  273 (* GREATEREQ *);
  274 (* PLUS *);
  275 (* MINUS *);
  276 (* TIMES *);
  277 (* DIV *);
  278 (* POW *);
  279 (* LPAREN *);
  280 (* RPAREN *);
  281 (* LCURL *);
  282 (* RCURL *);
  283 (* EOL *);
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
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\004\000\004\000\
\004\000\004\000\004\000\000\000"

let yylen = "\002\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\001\000\
\001\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000\
\003\000\005\000\005\000\003\000\003\000\001\000\006\000\006\000\
\002\000\002\000\002\000\002\000\003\000\001\000\003\000\003\000\
\003\000\003\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\009\000\000\000\030\000\000\000\000\000\
\000\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\
\000\000\025\000\026\000\028\000\027\000\016\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\021\000\020\000\000\000\000\000\
\000\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\002\000\000\000\000\000\019\000\
\018\000\000\000\000\000\031\000\033\000\032\000\034\000\024\000\
\023\000"

let yydgoto = "\002\000\
\013\000\014\000\054\000\057\000"

let yysindex = "\008\000\
\036\255\000\000\000\000\000\000\038\255\000\000\235\254\036\255\
\036\255\019\255\036\255\036\255\000\000\040\255\220\255\011\255\
\036\255\000\000\000\000\000\000\000\000\000\000\202\255\048\255\
\036\255\036\255\036\255\036\255\036\255\036\255\036\255\036\255\
\036\255\036\255\036\255\036\255\000\000\000\000\053\255\053\255\
\236\255\000\000\001\000\043\255\043\255\241\255\241\255\241\255\
\241\255\241\255\253\254\253\254\042\255\042\255\043\255\241\254\
\034\255\041\255\051\255\000\000\000\000\021\255\039\255\000\000\
\000\000\045\255\049\255\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\064\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\083\255\101\255\062\255\071\255\072\255\
\085\255\088\255\173\255\189\255\137\255\155\255\119\255\245\254\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\002\000\011\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\000\000\255\255\053\000"

let yytablesize = 289
let yytable = "\015\000\
\061\000\017\000\062\000\025\000\026\000\063\000\018\000\019\000\
\001\000\022\000\023\000\037\000\035\000\038\000\035\000\041\000\
\034\000\035\000\036\000\020\000\021\000\068\000\069\000\044\000\
\045\000\046\000\047\000\048\000\049\000\050\000\051\000\052\000\
\053\000\039\000\055\000\040\000\003\000\004\000\005\000\070\000\
\071\000\006\000\016\000\024\000\007\000\008\000\009\000\010\000\
\025\000\026\000\043\000\066\000\067\000\005\000\011\000\056\000\
\006\000\064\000\012\000\007\000\008\000\009\000\010\000\036\000\
\036\000\003\000\065\000\022\000\072\000\011\000\022\000\022\000\
\073\000\012\000\004\000\005\000\022\000\022\000\022\000\022\000\
\022\000\022\000\022\000\022\000\022\000\022\000\017\000\022\000\
\006\000\017\000\017\000\007\000\058\000\000\000\000\000\017\000\
\017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
\029\000\000\000\017\000\029\000\029\000\000\000\000\000\000\000\
\000\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
\029\000\029\000\015\000\000\000\029\000\015\000\015\000\000\000\
\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\013\000\000\000\015\000\000\000\
\000\000\000\000\000\000\000\000\000\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\014\000\000\000\
\013\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\011\000\000\000\014\000\000\000\000\000\000\000\000\000\000\000\
\000\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\012\000\000\000\000\000\000\000\011\000\000\000\000\000\000\000\
\000\000\012\000\012\000\012\000\012\000\012\000\012\000\012\000\
\025\000\026\000\000\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\032\000\033\000\034\000\035\000\036\000\
\000\000\042\000\025\000\026\000\000\000\000\000\000\000\000\000\
\027\000\028\000\029\000\030\000\031\000\032\000\033\000\034\000\
\035\000\036\000\025\000\026\000\000\000\000\000\000\000\025\000\
\026\000\000\000\000\000\000\000\000\000\032\000\033\000\034\000\
\059\000\036\000\032\000\033\000\034\000\035\000\036\000\000\000\
\008\000\008\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\009\000\009\000\008\000\008\000\008\000\008\000\008\000\
\000\000\000\000\000\000\060\000\009\000\009\000\009\000\009\000\
\009\000"

let yycheck = "\001\000\
\000\000\023\001\018\001\007\001\008\001\021\001\008\000\009\000\
\001\000\011\000\012\000\001\001\024\001\003\001\026\001\017\000\
\020\001\021\001\022\001\001\001\002\001\001\001\002\001\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\034\000\023\001\036\000\025\001\001\001\002\001\003\001\001\001\
\002\001\006\001\005\001\004\001\009\001\010\001\011\001\012\001\
\007\001\008\001\003\001\001\001\002\001\003\001\019\001\003\001\
\006\001\024\001\023\001\009\001\010\001\011\001\012\001\022\001\
\022\001\004\001\026\001\004\001\024\001\019\001\007\001\008\001\
\024\001\023\001\004\001\004\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\004\001\024\001\
\004\001\007\001\008\001\004\001\040\000\255\255\255\255\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\020\001\021\001\
\004\001\255\255\024\001\007\001\008\001\255\255\255\255\255\255\
\255\255\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\020\001\021\001\004\001\255\255\024\001\007\001\008\001\255\255\
\255\255\255\255\255\255\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\004\001\255\255\024\001\255\255\
\255\255\255\255\255\255\255\255\255\255\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\004\001\255\255\
\024\001\255\255\255\255\255\255\255\255\255\255\255\255\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\020\001\021\001\
\004\001\255\255\024\001\255\255\255\255\255\255\255\255\255\255\
\255\255\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\004\001\255\255\255\255\255\255\024\001\255\255\255\255\255\255\
\255\255\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\007\001\008\001\255\255\255\255\024\001\255\255\255\255\255\255\
\255\255\255\255\255\255\018\001\019\001\020\001\021\001\022\001\
\255\255\024\001\007\001\008\001\255\255\255\255\255\255\255\255\
\013\001\014\001\015\001\016\001\017\001\018\001\019\001\020\001\
\021\001\022\001\007\001\008\001\255\255\255\255\255\255\007\001\
\008\001\255\255\255\255\255\255\255\255\018\001\019\001\020\001\
\021\001\022\001\018\001\019\001\020\001\021\001\022\001\255\255\
\007\001\008\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\007\001\008\001\018\001\019\001\020\001\021\001\022\001\
\255\255\255\255\255\255\027\001\018\001\019\001\020\001\021\001\
\022\001"

let yynames_const = "\
  COMMA\000\
  UNDERSCORE\000\
  PI\000\
  BINOMIAL\000\
  MOD\000\
  FLOOR\000\
  SIN\000\
  COS\000\
  ARCTAN\000\
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
# 77 "parser.mly"
                              ( (substitute _1 (Symbolic_Constant _3) (Input_variable _3)) )
# 300 "parser.ml"
               : Type_def.inequation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'ineq) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 78 "parser.mly"
                             ( (substitute _1 (Symbolic_Constant _3) (Input_variable _3)) )
# 308 "parser.ml"
               : Type_def.inequation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                     ( Equals(_1, _3) )
# 316 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                   ( Less(_1, _3) )
# 324 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                     ( LessEq(_1, _3) )
# 332 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                      ( Greater(_1, _3) )
# 340 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 86 "parser.mly"
                        ( GreaterEq(_1, _3) )
# 348 "parser.ml"
               : 'ineq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "parser.mly"
              ( Rational(Mpq.init_set_si _1 1) )
# 355 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 90 "parser.mly"
                            ( Rational(Mpq.init_set_d (_1)) )
# 362 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 91 "parser.mly"
                            ( _2 )
# 369 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 92 "parser.mly"
                            ( Plus(_1, _3) )
# 377 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                            ( Minus(_1, _3) )
# 385 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                            ( Times(_1, _3) )
# 393 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                            ( Divide(_1, _3) )
# 401 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                      ( Pow(_1, _3) )
# 409 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                            ( Times(Rational (Mpq.init_set_si (-1) 1), _2) )
# 416 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                           ( Binomial(_1, _3) )
# 424 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'sub) in
    Obj.repr(
# 99 "parser.mly"
                                        ( Output_variable (_1, _4) )
# 432 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'sub) in
    Obj.repr(
# 100 "parser.mly"
                                        ( Output_variable (_1, _4) )
# 440 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 101 "parser.mly"
                            ( Output_variable (_1, SSVar _3) )
# 448 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 102 "parser.mly"
                           ( Symbolic_Constant (_1 ^ "_" ^ (string_of_int _3)) )
# 456 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 103 "parser.mly"
              ( Symbolic_Constant (_1) )
# 463 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : float) in
    Obj.repr(
# 104 "parser.mly"
                                       ( IDivide(_3, Mpq.init_set_d (_5)) )
# 471 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 105 "parser.mly"
                                     ( IDivide(_3, Mpq.init_set_si _5 1) )
# 479 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                  ( Sin(_2) )
# 486 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                  ( Cos(_2) )
# 493 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 108 "parser.mly"
                     ( Arctan(Mpq.init_set_d _2) )
# 500 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 109 "parser.mly"
                      ( Arctan(Mpq.init_set_si _2 1) )
# 507 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                      ( Mod (_1, _3) )
# 515 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 111 "parser.mly"
             ( Pi )
# 521 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 114 "parser.mly"
                 ( SAdd (_1, _3) )
# 529 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 115 "parser.mly"
                 ( SSDiv (_1, _3) )
# 537 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 116 "parser.mly"
                   ( SAdd (_1, int_of_float _3) )
# 545 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 117 "parser.mly"
                  ( SSDiv (_1, int_of_float _3) )
# 553 "parser.ml"
               : 'sub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 118 "parser.mly"
          ( SSVar _1 )
# 560 "parser.ml"
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
