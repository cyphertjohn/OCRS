(** This function solves a given recurrence in the internal representation format
    @param inequation_to_solve the recurrence to solve *)
val solve_rec : Type_def.inequation -> Type_def.inequation 

(** This function solves a given recurrence represented by a string, followed by a comma and the changing variable identifier
    @param str the recurrence to solve as a string *)
val solve_rec_str : string -> Type_def.inequation 

(** This function solves a list of recurrences by substitution
    @param ineq_list the set of recurrences to solve *)
val solve_rec_list : Type_def.inequation list -> Type_def.inequation list 
