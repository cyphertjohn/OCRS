open Type_def

val multiply_scalar_through_vector : op_expr array -> op_expr -> op_expr array

val invert_matrix_fast : op_expr array array -> op_expr array array

val add_vectors : op_expr array -> op_expr array -> op_expr array

val sub_matrix : op_expr array array -> op_expr array array -> op_expr array array

val matrix_times_vector : op_expr array array -> op_expr array -> op_expr array

