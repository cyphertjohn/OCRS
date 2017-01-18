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


let rec op_expr_to_string_IR e =
  match e with
  | OpPlus (left, right) ->
      "OpPlus (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpMinus (left, right) ->
      "OpMinus (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpTimes (left, right) ->
      "OpTimes (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpDivide (left, right) ->
      "OpDivide (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpProduct expr_list ->
      "OpProduct [" ^ (String.concat "; " (List.map op_expr_to_string_IR expr_list))^ "]"
  | OpSum expr_list ->
      "OpSum [" ^ (String.concat "; " (List.map op_expr_to_string_IR expr_list))^ "]"
  | OpSymbolic_Constant ident ->
      "OpSymbolic_Constant (" ^ ident ^ ")"
  | OpBase_case (ident, index) ->
      "OpBase_case (" ^ ident ^ ", " ^ string_of_int index ^ ")"
  | OpOutput_variable (ident , subscript) ->
      "OpOutput_variable (" ^ ident ^ ", " ^ (subscript_to_string subscript) ^ ")"
  | OpInput_variable str ->
      "OpInput_variable (" ^ str ^ ")"
  | OpRational rat ->
      "OpRational (" ^ (Mpfr.to_string rat) ^ ")"
  | OpLog expression ->
      "OpLog (" ^ (op_expr_to_string_IR expression)^ ")"
  | OpPow (left, right) ->
      "OpPow (" ^ (op_expr_to_string_IR left) ^ ", " ^ (op_expr_to_string_IR right) ^ ")"
  | Q ->
      "Q"
  | OpUndefined ->
      "UNDEFINED"
  ;;

(* convert an inequation to a string *)
let op_inequation_to_string_IR e =
  match e with
  | OpEquals (left, right) ->
      "OpEquals (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpLessEq (left, right) ->
      "OpLessEq (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpLess (left, right) ->
      "OpLess (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpGreaterEq (left, right) ->
      "OpGreaterEq (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpGreater (left, right) ->
      "OpGreater (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  ;;


let rec expr_to_string_IR e =
  match e with
  | Plus (left, right) ->
      "Plus (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Minus (left, right) ->
      "Minus (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Times (left, right) ->
      "Times (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Divide (left, right) ->
      "Divide (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Product expr_list ->
      "Product [" ^ (String.concat "; " (List.map expr_to_string_IR expr_list))^ "]"
  | Sum expr_list ->
      "Sum [" ^ (String.concat "; " (List.map expr_to_string_IR expr_list))^ "]"
  | Symbolic_Constant ident ->
      "Symbolic_Constant (" ^ ident ^ ")"
  | Base_case (ident, index) ->
      "Base_case (" ^ ident ^ ", " ^ string_of_int index ^ ")"
  | Output_variable (ident , subscript) ->
      "Output_variable (" ^ ident ^ ", " ^ (subscript_to_string subscript) ^ ")"
  | Input_variable str ->
      "Input_variable (" ^ str ^ ")"
  | Rational rat ->
      "Rational (" ^ (Mpfr.to_string rat) ^ ")"
  | Binomial (top, bottom) ->
      "Binomial (" ^ expr_to_string top ^ ", " ^ expr_to_string bottom ^ ")"
  | Factorial child ->
      "Factorial (" ^ (expr_to_string child) ^ ")"
  | Log expression ->
      "Log (" ^ (expr_to_string_IR expression)^ ")"
  | Pow (left, right) ->
      "Pow (" ^ (expr_to_string_IR left) ^ ", " ^ (expr_to_string_IR right) ^ ")"
  | Undefined ->
      "UNDEFINED"
  ;;

(* convert an inequation to a string *)
let inequation_to_string_IR e =
  match e with
  | Equals (left, right) ->
      "Equals (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | LessEq (left, right) ->
      "LessEq (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Less (left, right) ->
      "Less (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | GreaterEq (left, right) ->
      "GreaterEq (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Greater (left, right) ->
      "Greater (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  ;;


