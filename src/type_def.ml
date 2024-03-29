(** This modules contains definitions for the interface of the intermediate representation of OCRS *)

(** {6 Subscript} *)

type subscript = 
  | SAdd of string * int        	(** n+1, n+2, ... *)
  | SSVar of string			(** n *)
  | SSDiv of string * int		(** n/2, n/3, .. *)
  ;;

(** Definition of the comparison between two subscripts. 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
let subscript_order a b =
  match (a, b) with
  | (SSVar a_str, SSVar b_str) ->
      String.compare a_str b_str
  | (SSVar a_str, SAdd (b_str, _)) ->
      if a_str <> b_str then String.compare a_str b_str
      else (-1)
  | (SSVar a_str, SSDiv (b_str, _)) ->
      if a_str <> b_str then String.compare a_str b_str
      else (-1)
  | (SAdd (a_str, _), SSVar b_str) ->
      if a_str <> b_str then String.compare a_str b_str
      else 1
  | (SSDiv(a_str, _), SSVar b_str) ->
      if a_str <> b_str then String.compare a_str b_str
      else 1
  | (SAdd (a_str, a_index), SAdd (b_str, b_index)) ->
      if a_str <> b_str then String.compare a_str b_str
      else compare a_index b_index
  | (SSDiv(a_str, a_index), SSDiv (b_str, b_index)) ->
      if a_str <> b_str then String.compare a_str b_str
      else compare b_index a_index
  | (SSDiv(a_str, _), SAdd (b_str, _)) ->
      if a_str <> b_str then String.compare a_str b_str
      else (-1) 
  | (SAdd(a_str, _), SSDiv (b_str, _)) ->
      if a_str <> b_str then String.compare a_str b_str
      else 1
  ;;


(** {6 Recurrences in Elementary form} *)

type expr = 
          | Plus of expr * expr		(** Binary addition *)
          | Minus of expr * expr	(** Binary subtraction *)
	  | Times of expr * expr	(** Binary multiplication *)
	  | Divide of expr * expr	(** Binary division *)
	  | Product of expr list	(** N-ary multiplication *)
					(* want these two for flattening AST not indexed sums and products *)
	  | Sum of expr list		(** N-ary addition *)
	  | Symbolic_Constant of string (** "x", "y", etc *)
	  | Base_case of string * int	(** y_0, y_1, ... *)
	  | Output_variable of string * subscript (** y_n, y_n+1, y_n+2, ... *)
	  | Input_variable of string	(** Index variable *)
	  (* Maybe just make everything floats? *)
	  | Rational of Mpq.t		(** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
	  | Log of Mpq.t *  expr	(** Base b log *)
	  | Pow of expr * expr		(** Binary exponentiation *)
	  | Binomial of expr * expr	(** Binomial coeffiecient *)
          | IDivide of expr * Mpq.t	(** Integer Division *)
	  | Sin of expr			(** Trigonometric sine *)
	  | Cos of expr			(** Trigonometric cosine *)
          | Arctan of Mpq.t		(** Inverse tangent function *)
          | Mod of expr * expr		(** Modular expression *)
          | Pi				(** The trancendental number pi *)
          | Factorial of expr		(** Factorial *)
          | Iif of string * subscript	(** Impliciltly intrepreted function *)
          | Shift of int * expr		(** first argument represents amount to shift by. Neg ints represent left shifts *)
          | Undefined			(** An expression whose value is undefined. ie x/0, log(-1), etc *)
          ;;

type inequation = Equals of expr * expr 	(** = *)
		| LessEq of expr * expr		(** <= *)
		| Less of expr * expr		(** < *)
		| GreaterEq of expr * expr	(** >= *)
		| Greater of expr * expr	(** > *)
                ;;



type interval = Bounded of int * int
              | BoundBelow of int
              ;;

type piece_ineq = PieceWiseIneq of string * ((interval * inequation) list) ;;

type piece_expr = PieceWiseExpr of string * ((interval * expr) list);;


(** {7 Expression comparison} *)

(** Definition of the comparison between two expressions. See Computer Algebra and Symbolic Computation: Mathematical Methods by Joel S. Cohen 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
let rec expr_order a b = 
    match (a, b) with
    | (Rational a_v, Rational b_v) ->		(* O-1 *)
        Mpq.cmp a_v b_v
    | (Symbolic_Constant a_str, Symbolic_Constant b_str) | (Input_variable a_str, Input_variable b_str) -> (* O-2 *)
        String.compare a_str b_str
    | (Iif (op_expr_stra, subscript_a), Iif (op_expr_strb, subscript_b)) ->
        if (subscript_order subscript_a subscript_b) <> 0 then (subscript_order subscript_a subscript_b)
        else String.compare op_expr_stra op_expr_strb
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
            | ([], _) -> (-1)		(* n>m *)	(* O-3-3 *)
            | (_, []) -> 1		(* m>n *)	(* O-3-3 *)
            | (x_hd :: x_rest, y_hd :: y_rest) ->
                if (expr_order x_hd y_hd) = 0 then aux x_rest y_rest	(* O-3-2 *)
                else expr_order x_hd y_hd		(* O-3-1 *)
            ) in aux a_rev b_rev
    | (Pow (a_bas, a_exp), Pow (b_bas, b_exp)) ->
        if (expr_order a_bas b_bas) <> 0 then				(* O-4-1 *)
            expr_order a_bas b_bas
        else expr_order a_exp b_exp			(* O-4-2 *)
    | (Log (b, a_log), Log (c, b_log)) ->
	if (Mpq.cmp b c) = 0 then expr_order a_log b_log
	else (Mpq.cmp b c)
    | (Binomial (a_top, a_bot), Binomial (b_top, b_bot)) ->
        if (expr_order a_top b_top) = 0 then expr_order a_bot b_bot
        else expr_order a_top b_top
    | (Factorial a_fac, Factorial b_fac) ->
        expr_order a_fac b_fac				(* O-5 *)
    | (Rational _, _) -> (-1)				(* O-7 *)
    | (_, Rational _) -> (1)
    | (Base_case _, _) -> (-1)
    | (_, Base_case _) -> 1
    | (Symbolic_Constant _, _) -> (-1)
    | (_, Symbolic_Constant _) -> (1)
    | (Shift (shift_a, expr_a), Shift (shift_b, expr_b)) ->
        let expr_cmp = expr_order expr_a expr_b in
        if expr_cmp <> 0 then expr_cmp
        else compare shift_a shift_b
    | (Product _, _) ->
        expr_order a (Product [b])			(* O-8 *)
    | ( _, Product _)  ->	
        expr_order (Product [a]) b			(* O-8 *)
    | (Pow _, _) ->
        expr_order a (Pow (b, Rational (Mpq.init_set_si 1 1)))	(* O-9 *)
    | (_, Pow _) ->
        expr_order (Pow (a, Rational (Mpq.init_set_si 1 1))) b	(* O-9 *)
    | (Sum _, _) ->
        expr_order a (Sum [b])				(* O-10 *)
    | (_, Sum _) ->
        expr_order (Sum [a]) b				(* O-10 *)
    | (Factorial _, _) ->
        expr_order a (Factorial b)
    | ( _, Factorial _) ->
        expr_order (Factorial a) b
    | (Log (x, _), _) ->
        let res = expr_order a (Log (x,b)) in
        if res = 0 then 1
        else res
    | (_, Log (x, _)) ->
        let res = expr_order (Log (x, a)) b in
        if res = 0 then (-1)
        else res
    | (Binomial _, _) ->
        expr_order a (Binomial (b, Rational (Mpq.init_set_si 1 1)))
    | (_, Binomial _) ->
        expr_order (Binomial (a, Rational (Mpq.init_set_si 1 1))) b
    | (Output_variable _, _) -> 1
    | (_, Output_variable _) -> (-1)
    | (Input_variable _, _) -> 1
    | (_, Input_variable _) -> (-1)
    | (Iif _, _) -> 1
    | (_, Iif _) -> (-1)
    | (Shift _, _) -> 1
    | (_, Shift _) -> (-1)
    | _ -> failwith "all cases should have been taken care of"
    ;;

(** {6 Operational Calculus expressions} *)

type op_expr = OpPlus of op_expr * op_expr         (** Binary addition *)
             | OpMinus of op_expr * op_expr        (** Binary subtraction *)
             | OpTimes of op_expr * op_expr        (** Binary ring multiplication  *)
             | OpDivide of op_expr * op_expr       (** Binary division *)
             | OpProduct of op_expr list           (** N-ary ring multiplication *)
                                                 (* want these two for flattening AST not indexed sums and products *)
             | OpSum of op_expr list             (** N-ary addition a+b+c+... *)
             | OpSymbolic_Constant of string     (** "x", "y", etc *)
             | OpBase_case of string * int       (** y_0, y_1, ... *)
             | OpOutput_variable of string * subscript  (** y_n, y_n+1, y_n+2, ... *)
             | OpInput_variable of string        (** Index variable *)
              (* Maybe just make everything floats? *)
             | OpRational of Mpq.t               (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
             | OpLog of Mpq.t * op_expr          (** Base b log *)
             | OpPow of op_expr * op_expr        (** Binary exponentiation *)
             | SymBinom of op_expr * op_expr     (** Symbolic Binomial *)
             | SymIDivide of op_expr * Mpq.t     (** Symbolic Integer Divide *)
             | SymSin of op_expr                 (** Symbolic sine *)
             | SymCos of op_expr                 (** Symbolic cosine *)
             | OpArctan of Mpq.t                 (** Symbolic Arctan *)
             | SymMod of op_expr * op_expr       (** Symbolic mod *)
             | OpPi                              (** The constant pi *)
             | Q                                 (** q element in the operational calculus field *)
             | OpUndefined                       (** An expression whose value is undefined. ie x/0, log(-1), etc *)
             ;;
                  
type op_inequation = OpEquals of op_expr * op_expr	(** = *)
		       | OpLessEq of op_expr * op_expr	(** <= *)
		       | OpLess of op_expr * op_expr	(** < *)
		       | OpGreaterEq of op_expr * op_expr (** >= *)
		       | OpGreater of op_expr * op_expr	(** > *)
		       ;;

(** {7 OpExpression comparison} *)

(** Definition of the comparison between two op_expressions. See Computer Algebra and Symbolic Computation: Mathematical Methods by Joel S. Cohen 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
let rec op_expr_order a b = 
    match (a, b) with
    | (OpRational a_v, OpRational b_v) ->		(* O-1 *)
        Mpq.cmp a_v b_v
    | (Q, Q) -> 0
    | (OpSymbolic_Constant a_str, OpSymbolic_Constant b_str) | (OpInput_variable a_str, OpInput_variable b_str) -> (* O-2 *)
        String.compare a_str b_str
    | (OpBase_case (a_ident, a_index), OpBase_case (b_ident, b_index)) ->
        if a_ident <> b_ident then String.compare a_ident b_ident
        else compare a_index b_index
    | (OpOutput_variable (a_ident, a_sub), OpOutput_variable (b_ident, b_sub)) ->
        if a_ident <> b_ident then String.compare a_ident b_ident
        else subscript_order a_sub b_sub
    | (OpSum a_list, OpSum b_list) | (OpProduct a_list, OpProduct b_list) ->
        let a_rev = List.rev a_list in
        let b_rev = List.rev b_list in
        let rec aux x y = 
            (match (x, y) with
            | ([], []) -> 0		(* the two lists are equal *)
            | ([], _) -> (-1)		(* n>m *)	(* O-3-3 *)
            | (_, []) -> 1		(* m>n *)	(* O-3-3 *)
            | (x_hd :: x_rest, y_hd :: y_rest) ->
                if (op_expr_order x_hd y_hd) = 0 then aux x_rest y_rest	(* O-3-2 *)
                else op_expr_order x_hd y_hd		(* O-3-1 *)
            ) in aux a_rev b_rev
    | (OpPow (a_bas, a_exp), OpPow (b_bas, b_exp)) ->
        if (op_expr_order a_bas b_bas) <> 0 then				(* O-4-1 *)
            op_expr_order a_bas b_bas
        else op_expr_order a_exp b_exp			(* O-4-2 *)
    | (OpLog (b, a_log), OpLog (c, b_log)) ->
	if (Mpq.cmp b c) = 0 then op_expr_order a_log b_log
	else (Mpq.cmp b c)
    | (OpRational _, _) -> (-1)				(* O-7 *)
    | (_, OpRational _) -> (1)
    | (Q, _) -> (-1)
    | (_, Q) -> 1
    | (OpProduct _, _) ->
        op_expr_order a (OpProduct [b])			(* O-8 *)
    | ( _, OpProduct _)  ->	
        op_expr_order (OpProduct [a]) b			(* O-8 *)
    | (OpPow _, _) ->
        op_expr_order a (OpPow (b, OpRational (Mpq.init_set_si 1 1)))	(* O-9 *)
    | (_, OpPow _) ->
        op_expr_order (OpPow (a, OpRational (Mpq.init_set_si 1 1))) b	(* O-9 *)
    | (OpSum _, _) ->
        op_expr_order a (OpSum [b])				(* O-10 *)
    | (_, OpSum _) ->
        op_expr_order (OpSum [a]) b				(* O-10 *)
    | (OpLog (x, _), _) ->
        op_expr_order a (OpLog (x,b))
    | (_, OpLog (x, _)) ->
        op_expr_order (OpLog (x, a)) b
    | (OpBase_case _, _) -> (-1)
    | (_, OpBase_case _) -> (1)
    | (OpSymbolic_Constant _, _) -> (-1)
    | (_, OpSymbolic_Constant _) -> (1)
    | (OpOutput_variable _, _) -> 1
    | (_, OpOutput_variable _) -> (-1)
    | (OpInput_variable _, _) -> 1
    | (_, OpInput_variable _) -> (-1)
    | _ -> failwith "all cases should have been taken care of"
    ;;



(** {6 Matrix Recurrences} *)

type ovec = Ovec of string array * subscript;;

type matrix_rec =
          | VEquals of ovec * Mpq.t array array * ovec * expr array
          | VLess of ovec * Mpq.t array array * ovec * expr array
          | VLessEq of ovec * Mpq.t array array * ovec * expr array
          | VGreater of ovec * Mpq.t array array * ovec * expr array
          | VGreaterEq of ovec * Mpq.t array array * ovec * expr array
          ;;


type matrix_rec_piece_add =
          | PVEquals of ovec * Mpq.t array array * ovec * piece_expr array
          | PVLess of ovec * Mpq.t array array * ovec * piece_expr array
          | PVLessEq of ovec * Mpq.t array array * ovec * piece_expr array
          | PVGreater of ovec * Mpq.t array array * ovec * piece_expr array
          | PVGreaterEq of ovec * Mpq.t array array * ovec * piece_expr array
          ;;
