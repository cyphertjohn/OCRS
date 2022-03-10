open Type_def

val expand_product : expr -> expr -> expr

val expand_power : expr -> Mpq.t -> expr

val algebraic_expand : expr -> expr
  
val algebraic_expand_inequation : inequation -> inequation

val inverse_binomial : expr -> expr

val inverse_binomial_ineq : inequation -> inequation