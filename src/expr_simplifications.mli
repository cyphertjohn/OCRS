val is_int : Mpq.m Mpq.tt -> bool

val factorial_int : Mpq.m Mpq.tt -> Mpq.m Mpq.tt

val binomial : Mpq.m Mpq.tt -> Mpq.m Mpq.tt -> Mpq.m Mpq.tt

val exp_by_squaring_int : Mpq.m Mpq.tt -> Mpq.m Mpq.tt -> Mpq.m Mpq.tt

(** Automatically simplify an expression bottom up *)
val automatic_simplify : Type_def.expr -> Type_def.expr 

(** Simplifies the expressions on either side of the constraint *)
val automatic_simplify_inequation : Type_def.inequation -> Type_def.inequation
