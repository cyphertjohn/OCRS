open Subscript_def

type expr = Plus of expr * expr		(* a + b *)
          | Minus of expr * expr	(* a - b *)
	  | Times of expr * expr	(* a * b *)
	  | Divide of expr * expr	(* a / b *)
	  | Product of expr list	(* a*b*c*... *)
					(* want these two for flattening AST not indexed sums and products *)
	  | Sum of expr list		(* a+b+c+... *)
	  | Symbolic_Constant of string (* a symbolic constant *)
	  | Base_case of string * int	(* y_0, y_1, ... *)
	  | Output_variable of string * subscript	(* y_n, y_n+1, y_0, ... *)
	  | Input_variable of string	(* n *)
	  (* Maybe just make everything floats? *)
	  | Rational of Mpfr.t		(* ...,1.3, 3.5,... *)
	  | Log of expr			(* natural log *)
	  | Pow of expr * expr		(* power *)
	  | Binomial of expr * expr	(* binomial coeficient *)
          | Factorial of expr		(* n!, 2!, etc *)
          | Undefined			(* if we hit divide by 0 or something similar *)
          ;;

type inequation = Equals of expr * expr 	(* = *)
		| LessEq of expr * expr		(* <= *)
		| Less of expr * expr		(* < *)
		| GreaterEq of expr * expr	(* >= *)
		| Greater of expr * expr	(* > *)
                ;;

let rec expr_order a b = 
    match (a, b) with
    | (Rational a_v, Rational b_v) ->		(* O-1 *)
        Mpfr.cmp a_v b_v
    | (Symbolic_Constant a_str, Symbolic_Constant b_str) | (Input_variable a_str, Input_variable b_str) -> (* O-2 *)
        String.compare a_str b_str
    | (Base_case (a_ident, a_index), Base_case (b_ident, b_index)) ->
        if a_ident <> b_ident then String.compare a_ident b_ident
        else compare a_index b_index
    | (Output_variable (a_ident, a_sub), Output_variable (b_ident, b_sub)) ->
        if a_ident <> b_ident then String.compare a_ident b_ident
        else subscript_order a_sub b_sub
    | (Sum a_list, Sum b_list) | (Product a_list, Product b_list) ->
        let a_rev = List.rev a_list in
        let b_rev = List.rev b_list in
        let rec aux x y = 
            (match (x, y) with
            | ([], []) -> 0		(* the two lists are equal *)
            | ([], y1) -> (-1)		(* n>m *)	(* O-3-3 *)
            | (x1, []) -> 1		(* m>n *)	(* O-3-3 *)
            | (x_hd :: x_rest, y_hd :: y_rest) ->
                if (expr_order x_hd y_hd) = 0 then aux x_rest y_rest	(* O-3-2 *)
                else expr_order x_hd y_hd		(* O-3-1 *)
            ) in aux a_rev b_rev
    | (Pow (a_bas, a_exp), Pow (b_bas, b_exp)) ->
        if (expr_order a_bas b_bas) <> 0 then				(* O-4-1 *)
            expr_order a_bas b_bas
        else expr_order a_exp b_exp			(* O-4-2 *)
    | (Log a_log, Log b_log) ->
        expr_order a_log b_log
    | (Binomial (a_top, a_bot), Binomial (b_top, b_bot)) ->
        if (expr_order a_top b_top) = 0 then expr_order a_bot b_bot
        else expr_order a_top b_top
    | (Factorial a_fac, Factorial b_fac) ->
        expr_order a_fac b_fac				(* O-5 *)
    | (Rational _, _) -> (-1)				(* O-7 *)
    | (_, Rational _) -> (1)
    | (Product _, _) (*| (Product _, Sum _) | (Product _, Factorial _) | (Product _, Log _) | (Product _, Binomial _) | (Product _,   | (Product _, Symbol _) *) ->		(* might need to add binomial and log *)
        expr_order a (Product [b])			(* O-8 *)
    | ( _, Product _) (*| (Sum _, Product _) | (Factorial _, Product _)*) ->	
        expr_order (Product [a]) b			(* O-8 *)
    | (Pow _, _) (*| (Pow _, Factorial _) | (Pow _, Symbol _) *) ->
        expr_order a (Pow (b, Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))))	(* O-9 *)
    | (_, Pow _) (*| (Factorial _, Pow _) | (Symbol _, Pow _) *) ->
        expr_order (Pow (a, Rational (snd (Mpfr.init_set_si 1 Mpfr.Near)))) b	(* O-9 *)
    | (Sum _, _) (* | (Sum _, Symbol _) *) ->
        expr_order a (Sum [b])				(* O-10 *)
    | (_, Sum _) (* | (Symbol _, Sum _) *) ->
        expr_order (Sum [a]) b
    | (Factorial _, _) ->
        expr_order a (Factorial b)
    | ( _, Factorial _) ->
        expr_order (Factorial a) b
    | (Log _, _) ->
        expr_order a (Log b)
    | (_, Log _) ->
        expr_order (Log a) b
    | (Binomial _, _) ->
        expr_order a (Binomial (b, Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))))
    | (_, Binomial _) ->
        expr_order (Binomial (a, Rational (snd (Mpfr.init_set_si 1 Mpfr.Near)))) b
    | (Output_variable _, _) -> 1
    | (_, Output_variable _) -> (-1)
    | (Input_variable _, _) -> 1
    | (_, Input_variable _) -> (-1)
    | (Base_case _, _) -> 1
    | (_, Base_case _) -> (-1)
    | (Symbolic_Constant _, _) -> 1
    | (_, Symbolic_Constant _) -> (-1)
    | _ -> failwith "all cases should have been taken care of"
    ;;
(* I think this needs to be made a module with all the simplification rules*)
type op_expr = OpPlus of op_expr * op_expr         (* a + b *)
             | OpMinus of op_expr * op_expr        (* a - b *)
             | OpTimes of op_expr * op_expr        (* a * b *)
             | OpDivide of op_expr * op_expr       (* a / b *)
             | OpProduct of op_expr list	         (* a*b*c*... *)
                                        	 (* want these two for flattening AST not indexed sums and products *)
             | OpSum of op_expr list           	 (* a+b+c+... *)
             | OpSymbolic_Constant of string	 (* symbolic constant *)
	     | OpBase_case of string * int	 (* y_0, y_1, y_2, ... *)
	     | OpOutput_variable of string * subscript  (* y_n, y_n+1, y_n-1, y_n/2, y_sqrt(n), y_0, y_1 ... *)
             | OpInput_variable of string   	 (* n *)
              (* Maybe just make everything floats? *)
             | OpRational of Mpfr.t           	 (* ...,-1,0,1,2,... *)
             | OpLog of op_expr                	 (* natural log *)
             | OpPow of op_expr * op_expr        (* power *)
             | Q
             | OpUndefined			 (* undefined mathematical value *)
             ;;


type opCalc_inequation = OpEquals of op_expr * op_expr
		       | OpLessEq of op_expr * op_expr
		       | OpLess of op_expr * op_expr
		       | OpGreaterEq of op_expr * op_expr
		       | OpGreater of op_expr * op_expr
		       ;;
