open Type_def

let rec subscript_to_string e = 
  match e with
  | SAdd (left, right) ->
    "{" ^ left ^ " + " ^ (string_of_int right) ^ "}"
  | SSVar ident ->
    ident
  ;;

(* convert an expression to a string *)
let rec expr_to_string e =
  match e with
  | Plus (left, right) ->
      "(" ^ expr_to_string left ^ " + " ^ expr_to_string right ^ ")"
  | Minus (left, right) ->
      "(" ^ expr_to_string left ^ " - " ^ expr_to_string right ^ ")"
  | Times (left, right) ->
      "("  ^ expr_to_string left ^ " * " ^ expr_to_string right ^ ")"
  | Divide (left, right) ->
      "(" ^ expr_to_string left ^ " / " ^ expr_to_string right ^ ")"
  | Product expr_list ->
      "(" ^ (String.concat " * " (List.map expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with star *)
  | Sum expr_list ->
      "(" ^ (String.concat " + " (List.map expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with + *)
  | Symbolic_Constant ident ->
      ident
  | Base_case (ident, index) ->
      ident ^ "_" ^ (string_of_int index)
  | Output_variable (ident , subscript) ->
      ident ^ "_" ^ (subscript_to_string subscript)
  | Input_variable str ->
      str
  | Rational rat ->
      string_of_float (Mpfr.to_float rat)
  | Log expression ->
      "log(" ^ expr_to_string expression ^ ")"
  | Pow (left, right) ->
      expr_to_string left ^ " ^ " ^ expr_to_string right			(* Since Power has top precedence don't think need parens *)
  | Binomial (top, bottom) ->
      "(" ^ expr_to_string top ^ " choose " ^ expr_to_string bottom ^ ")"
  | Factorial child ->
      (expr_to_string child) ^ "!"
  | Undefined ->
      "UNDEFINED"
  ;;

(* convert an inequation to a string *)
let inequation_to_string e =
  match e with
  | Equals (left, right) ->
      expr_to_string left ^ " == " ^ expr_to_string right
  | LessEq (left, right) ->
      expr_to_string left ^ " <= " ^ expr_to_string right
  | Less (left, right) ->
      expr_to_string left ^ " < " ^ expr_to_string right
  | GreaterEq (left, right) ->
      expr_to_string left ^ " >= " ^ expr_to_string right
  | Greater (left, right) ->
      expr_to_string left ^ " > " ^  expr_to_string right
  ;;


(* Maybe this isn't right *)

let rec op_expr_to_string e =
  match e with
  | OpPlus (left, right) ->
      "(" ^ op_expr_to_string left ^ " + " ^ op_expr_to_string right ^ ")"
  | OpMinus (left, right) ->
      "(" ^ op_expr_to_string left ^ " - " ^ op_expr_to_string right ^ ")"
  | OpTimes (left, right) ->
      "("  ^ op_expr_to_string left ^ " * " ^ op_expr_to_string right ^ ")"
  | OpDivide (left, right) ->
      "(" ^ op_expr_to_string left ^ " / " ^ op_expr_to_string right ^ ")"
  | OpProduct expr_list ->
      "(" ^ (String.concat " * " (List.map op_expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with star *)
  | OpSum expr_list ->
      "(" ^ (String.concat " + " (List.map op_expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with + *)
  | OpSymbolic_Constant ident ->
      ident
  | OpBase_case (ident, index) ->
      ident ^ "_" ^ (string_of_int index)
  | OpOutput_variable (ident , subscript) ->
      ident ^ "_" ^ (subscript_to_string subscript)
  | OpInput_variable str ->
      str
  | OpRational rat ->
      string_of_float (Mpfr.to_float rat)
  | OpLog expression ->
      "log(" ^ op_expr_to_string expression ^ ")"
  | OpPow (left, right) ->
      op_expr_to_string left ^ " ^ " ^ op_expr_to_string right                        (* Since Power has top precedence don't think need parens *)
  | Q ->
      "q"
  | OpUndefined ->
      "UNDEFINED"
  ;;

(* convert an inequation to a string *)
let op_inequation_to_string e =
  match e with
  | OpEquals (left, right) ->
      op_expr_to_string left ^ " == " ^ op_expr_to_string right
  | OpLessEq (left, right) ->
      op_expr_to_string left ^ " <= " ^ op_expr_to_string right
  | OpLess (left, right) ->
      op_expr_to_string left ^ " < " ^ op_expr_to_string right
  | OpGreaterEq (left, right) ->
      op_expr_to_string left ^ " >= " ^ op_expr_to_string right
  | OpGreater (left, right) ->
      op_expr_to_string left ^ " > " ^ op_expr_to_string right
  ;;

