(* convert an expression to a string *)
val expr_to_string : Type_def.expr -> string

(* convert an inequation to a string *)
val inequation_to_string : Type_def.inequation -> string

val op_expr_to_string : Type_def.op_expr -> string

val op_inequation_to_string : Type_def.op_inequation -> string

val op_expr_to_string_IR : Type_def.op_expr -> string

val op_inequation_to_string_IR : Type_def.op_inequation -> string

val subscript_to_string_IR : Type_def.subscript -> string

val expr_to_string_IR : Type_def.expr -> string

val inequation_to_string_IR : Type_def.inequation -> string

val is_const : Type_def.expr -> bool
