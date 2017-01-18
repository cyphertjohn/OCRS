(** This modules contains definitions for the interface of the intermediate representation of OCRS *)

(** {6 Subscript} *)

type subscript = 
  | SAdd of string * int		(** n+1, n+2, ... *)
  | SSVar of string			(** n *)
  | SSDiv of string * int		(** n/2, n/3, ... *)


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
	  | Rational of Mpfr.t		(** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpfr.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
	  | Log of Mpfr.t * expr	(** Base b log *)
	  | Pow of expr * expr		(** Binary exponentiation *)
	  | Binomial of expr * expr	(** Binomial coeffiecient *)
          | Factorial of expr		(** Factorial *)
          | Undefined			(** An expression whose value is undefined. ie x/0, log(-1), etc *)

type inequation = Equals of expr * expr 	(** = *)
		| LessEq of expr * expr		(** <= *)
		| Less of expr * expr		(** < *)
		| GreaterEq of expr * expr	(** >= *)
		| Greater of expr * expr	(** > *)


(** {7 Expression Order} *)

(** Definition of the comparison between two expressions. 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
val expr_order : expr -> expr -> int


(** {6 Operational Calculus expressions} *)

type op_expr = OpPlus of op_expr * op_expr         (** Binary addition *)
             | OpMinus of op_expr * op_expr        (** Binary subtraction *)
             | OpTimes of op_expr * op_expr        (** Binary ring multiplication  *)
             | OpDivide of op_expr * op_expr       (** Binary division *)
             | OpProduct of op_expr list	   (** N-ary ring multiplication *)
                                        	 (* want these two for flattening AST not indexed sums and products *)
             | OpSum of op_expr list           	 (** N-ary addition a+b+c+... *)
             | OpSymbolic_Constant of string	 (** "x", "y", etc *)
	     | OpBase_case of string * int	 (** y_0, y_1, ... *)
	     | OpOutput_variable of string * subscript  (** y_n, y_n+1, y_n+2, ... *)
             | OpInput_variable of string   	 (** Index variable *)
              (* Maybe just make everything floats? *)
             | OpRational of Mpfr.t           	 (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpfr.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
             | OpLog of op_expr                	 (** Base 2 log *)
             | OpPow of op_expr * op_expr        (** Binary exponentiation *)
             | Q				 (** q element in the operational calculus field *)
             | OpUndefined			 (** An expression whose value is undefined. ie x/0, log(-1), etc *)
                  
type op_inequation = OpEquals of op_expr * op_expr	(** = *)
		       | OpLessEq of op_expr * op_expr	(** <= *)
		       | OpLess of op_expr * op_expr	(** < *)
		       | OpGreaterEq of op_expr * op_expr (** >= *)
		       | OpGreater of op_expr * op_expr	(** > *)


(** {7 Expression Order} *)

(** Definition of the comparison between two expressions. 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
val op_expr_order : op_expr -> op_expr -> int

