(** This modules contains definitions for the interface of the intermediate representation of OCRS *)

(** {6 Subscript} *)

type subscript = 
  | SAdd of string * int		(** n+1, n+2, ... *)
  | SSVar of string			(** n *)
  | SSDiv of string * int		(** n/2, n/3, ... *)


(** {6 Recurrences in Elementary form} *)

type expr =
          | Plus of expr * expr         (** Binary addition *)
          | Minus of expr * expr        (** Binary subtraction *)
          | Times of expr * expr        (** Binary multiplication *)
          | Divide of expr * expr       (** Binary division *)
          | Product of expr list        (** N-ary multiplication *)
                                        (* want these two for flattening AST not indexed sums and products *)
          | Sum of expr list            (** N-ary addition *)
          | Symbolic_Constant of string (** "x", "y", etc *)
          | Base_case of string * int   (** y_0, y_1, ... *)
          | Output_variable of string * subscript (** y_n, y_n+1, y_n+2, ... *)
          | Input_variable of string    (** Index variable *)
          (* Maybe just make everything floats? *)
          | Rational of Mpq.t           (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
          | Log of Mpq.t *  expr        (** Base b log *)
          | Pow of expr * expr          (** Binary exponentiation *)
          | Binomial of expr * expr     (** Binomial coeffiecient *)
          | IDivide of expr * Mpq.t     (** Integer Division. Currently unsupported *)
          | Sin of expr                 (** Trigonometric sine. Currently unsupported *)
          | Cos of expr                 (** Trigonometric cosine. Currently unsupported *)
          | Arctan of Mpq.t             (** Inverse tangent function. Currently unsupported *)
          | Mod of expr * expr          (** Modular expression. Currently unsupported *)
          | Pi                          (** The trancendental number pi. Currently unsupported *)
          | Factorial of expr           (** Factorial. Currently unsupported *)
          | Iif of string * subscript	(** Implicitly interpreted function *)
          | Shift of int * expr		(** first argument represents amount to shift by. Neg ints represent left shifts *)
          | Undefined                   (** An expression whose value is undefined. ie x/0, log(-1), etc *)
          ;;

type inequation = Equals of expr * expr 	(** = *)
		| LessEq of expr * expr		(** <= *)
		| Less of expr * expr		(** < *)
		| GreaterEq of expr * expr	(** >= *)
		| Greater of expr * expr	(** > *)
                ;;

(** {7 Expression Order} *)

(** Definition of the comparison between two expressions. 
    @return < 0 if a < b, 0 if a = b, and > 0 if a > b *)
val expr_order : expr -> expr -> int ;;


(** {6 Piece-wise functions} *)

type interval = Bounded of int * int		(** \[a, b\] *)
              | BoundBelow of int		(** \[a, inf) *)
              ;;

(** The first argument is the variable used in the guard. The second argument is a list of pairs where the first
    argument is an interval, such that when the variable used in the guard is within the interval then the inequation
    is the second argument of the pair *)
type piece_ineq = PieceWiseIneq of string * ((interval * inequation) list) ;;

(** The first argument is the variable used in the guard. The second argument is a list of pairs where the first
    argument is an interval, such that when the variable used in the guard is within the interval then the expression
    is the second argument of the pair *)
type piece_expr = PieceWiseExpr of string * ((interval * expr) list);;


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
             | OpRational of Mpq.t           	 (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
             | OpLog of Mpq.t * op_expr       	 (** Base b log *)
             | OpPow of op_expr * op_expr        (** Binary exponentiation *)
             | SymBinom of op_expr * op_expr	 (** Symbolic Binomial *)
             | SymIDivide of op_expr * Mpq.t     (** Symbolic Integer Divide *)
             | SymSin of op_expr                 (** Symbolic sine *)
             | SymCos of op_expr                 (** Symbolic cosine *)
             | OpArctan of Mpq.t                 (** Symbolic Arctan *)
             | SymMod of op_expr * op_expr       (** Symbolic mod *)
             | OpPi                              (** The constant pi *)
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


(** {6 Matrix Recurrences} *)

(** A vector of output variables. An array of strings bound by a subscript *)
type ovec = Ovec of string array * subscript;;

(** A matrix recurrence is a 4-tuple (x', A, x, b) over say variable n, representing x' >=< x*A+b, where 
- x' is an ovec with subscript n+1
- A is a matrix with entries of type Mpq.t
- x is an ovec with subscript n
- b is an array of expressions 

*)
type matrix_rec =
          | VEquals of ovec * Mpq.t array array * ovec * expr array	(** = *)
          | VLess of ovec * Mpq.t array array * ovec * expr array	(** < *)
          | VLessEq of ovec * Mpq.t array array * ovec * expr array	(** <= *)
          | VGreater of ovec * Mpq.t array array * ovec * expr array	(** > *)
          | VGreaterEq of ovec * Mpq.t array array * ovec * expr array	(** >= *)
          ;;

(** The same as matrix_rec except the additive array is a piece-wise expression *)
type matrix_rec_piece_add =
          | PVEquals of ovec * Mpq.t array array * ovec * piece_expr array	(** = *)
          | PVLess of ovec * Mpq.t array array * ovec * piece_expr array	(** < *)
          | PVLessEq of ovec * Mpq.t array array * ovec * piece_expr array	(** <= *)
          | PVGreater of ovec * Mpq.t array array * ovec * piece_expr array	(** > *)
          | PVGreaterEq of ovec * Mpq.t array array * ovec * piece_expr array	(** >= *)
          ;;
