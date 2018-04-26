(** This module contains some basic useful operations for dealing with expressions and inequations *)

(** Convert an expression to a string *)
val expr_to_string : Type_def.expr -> string

(** Convert an inequation to a string *)
val inequation_to_string : Type_def.inequation -> string

(** Convert a piece-wise inequation to string *)
val piece_to_string : Type_def.piece_ineq -> string 

(** Convert an operational calculus expression to a string *)
val op_expr_to_string : Type_def.op_expr -> string

(** Convert an operational calculus inequation to a string *)
val op_inequation_to_string : Type_def.op_inequation -> string

(** Produce a string that shows the intermediate representation of an operational calculus expression *)
val op_expr_to_string_IR : Type_def.op_expr -> string

(** Produce a string that shows the intermediate representation of an operational calculus inequation *)
val op_inequation_to_string_IR : Type_def.op_inequation -> string


(** Produce a string that shows the intermediate representation of a subscript *)
val subscript_to_string_IR : Type_def.subscript -> string

(** Produce a string that shows the intermediate representation of a expression *)
val expr_to_string_IR : Type_def.expr -> string

(** Produce a string that shows the intermediate representation of a inequation *)
val inequation_to_string_IR : Type_def.inequation -> string

(** Takes in a list of inequations and splits the inequations into left and right sides. 
    @return a 3-tuple of three lists of equal length, say (a, b, c). Then, \{(List.nth a i) (List.nth c i) (List.nth b i)\} == List.nth input i *)
val get_right_left_constr : Type_def.inequation list -> (Type_def.expr list) * (Type_def.expr list) * (string list) 

(** Tells whether an expression is a constant expression or not *)
val is_const : Type_def.expr -> string -> bool

(** Substitutes all occurences of an expression with another for a given expression. substitute_expr x old_expr new_expr, will return a new expression where all occurrences of old_expr are replaced with new_expr in x *)
val substitute_expr : Type_def.expr -> Type_def.expr -> Type_def.expr -> Type_def.expr

(** The same as the previous function except the first argument is an inequation. *)
val substitute : Type_def.inequation -> Type_def.expr -> Type_def.expr -> Type_def.inequation 

(** A function that finds all unique output variables and input variables.
    @return a pair of two lists with unique entries, where the first element of the pair is all the output variables in the expression and the second element is all the input variables. *)
val find_ovar_ivar_expr : Type_def.expr -> (string list) * (string list)

(** The same as the previous function except takes an inequation in as input *)
val find_ovar_ivar : Type_def.inequation -> (string list) * (string list)
