open Type_def

val remove_left_shifts : expr -> expr
val sort_and_remove_duplicates : 'a list -> 'a list
val get_break_points : expr -> int list
val deshift :
  expr ->
  expr -> string -> string -> piece_ineq
val deshift_ineq : inequation -> piece_ineq
