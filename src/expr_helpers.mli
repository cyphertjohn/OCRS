(* convert an expression to a string *)
val expr_to_string : Type_def.expr -> string

(* convert an inequation to a string *)
val inequation_to_string : Type_def.inequation -> string

val piece_to_string : Type_def.piece_ineq -> string 

val op_expr_to_string : Type_def.op_expr -> string

val op_inequation_to_string : Type_def.op_inequation -> string

val op_expr_to_string_IR : Type_def.op_expr -> string

val op_inequation_to_string_IR : Type_def.op_inequation -> string

val subscript_to_string_IR : Type_def.subscript -> string

val expr_to_string_IR : Type_def.expr -> string

val inequation_to_string_IR : Type_def.inequation -> string

val get_right_left_constr : Type_def.inequation list -> (Type_def.expr list) * (Type_def.expr list) * (string list) 

val is_const : Type_def.expr -> bool

val substitute_expr : Type_def.expr -> Type_def.expr -> Type_def.expr -> Type_def.expr

val substitute : Type_def.inequation -> Type_def.expr -> Type_def.expr -> Type_def.inequation 

val find_ovar_ivar_expr : Type_def.expr -> (string list) * (string list)

val find_ovar_ivar : Type_def.inequation -> (string list) * (string list)
