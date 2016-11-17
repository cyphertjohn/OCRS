(** Automatically simplify an expression bottom up *)
val op_automatic_simplify : Type_def.op_expr -> Type_def.op_expr 

(** Simplifies the expressions on either side of the constraint *)
val op_automatic_simplify_inequation : Type_def.op_inequation -> Type_def.op_inequation
