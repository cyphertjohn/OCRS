(** This function solves for an output variable with the given identifier and the given input identifier
    @param inequation_to_solve the inequation to manipulate
    @param ident the identifier for the output variable
    @param input_ident the identifier for the input variable *)
val solve_for_Ovar : Type_def.op_inequation -> string -> string -> Type_def.op_inequation 
