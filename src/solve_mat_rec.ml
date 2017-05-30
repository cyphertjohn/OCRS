open Type_def


let solve_mat_rec primed matrix unprimed add constr = 
  (* check to make sure primed subscript is n+1 *)
  let size = Array.length matrix in
  let q_matrix = Array.make_matrix size size (OpRational (Mpq.init_set_si 0 1)) in
  let _ = 
    for i = 0 to size - 1 do
      q_matrix.(i).(i) <- Q
    done in
  let (primed_idents, primed_subscript) = 
    (match primed with
    | Ovec (idents, sub) -> (idents, sub)) in

  let (unprimed_idents, unprimed_subscript) = 
    (match unprimed with
    | Ovec (idents, sub) -> (idents, sub)) in
  let _ = if unprimed_idents <> primed_idents then failwith "Variables do not match in recurrence" in
  let ivar_ident = 
    (match primed_subscript with
    | SAdd (ident, 1) -> ident
    | _ -> failwith "Primed input is only allowed n+1 for now") in
  let _ = if unprimed_subscript <> (SSVar ivar_ident) then failwith "Unprimed input is only allowed n for now" in
  let base_case_vec = Array.map (fun x -> OpBase_case (x, 0)) primed_idents in
  let op_rational_matrix = 
    (
    let ans = Array.make_matrix size size (OpRational (Mpq.init_set_si 0 1)) in
    let _ = 
      for i = 0 to size - 1 do
        for j = 0 to size - 1 do
          ans.(i).(j) <- (OpRational (matrix.(i).(j)))
        done
      done in
    ans
    ) in
  let add_vec_op_calc = Array.map Expr_to_opcalc.expr_to_opCalc add in
  let new_vec = Mat_functions.multiply_scalar_through_vector base_case_vec (OpMinus(Q, OpRational (Mpq.init_set_si 1 1))) in
  let new_vec = Mat_functions.add_vectors new_vec add_vec_op_calc in
  let new_matrix = Mat_functions.invert_matrix_fast (Mat_functions.sub_matrix q_matrix op_rational_matrix) in
  let op_calc_results = Mat_functions.matrix_times_vector new_matrix new_vec in
  let expanded_results = Array.map Op_transforms.algebraic_expand op_calc_results in
  let _ = Array.iter (fun x -> print_endline (Expr_helpers.op_expr_to_string x)) expanded_results in
  let partial_fraction = Array.map Op_transforms.partial_fraction expanded_results in
  let result_exprs = Array.map (fun x -> Tau_inverse.tau_inverse x ivar_ident) partial_fraction in
  let answer_vec_with_subs = Mat_helpers.apply_subscript_to_ovec (Ovec (primed_idents, (SSVar ivar_ident))) in
  let result_exprs_list = Array.to_list result_exprs in
  let answer_vec_with_subs_list = Array.to_list answer_vec_with_subs in
  (match constr with
  | "==" ->
    List.map2 (fun x y -> Equals(x, y)) answer_vec_with_subs_list result_exprs_list
  | "<" ->
    List.map2 (fun x y -> Less(x, y)) answer_vec_with_subs_list result_exprs_list
  | "<=" ->
    List.map2 (fun x y -> LessEq(x, y)) answer_vec_with_subs_list result_exprs_list
  | ">" ->
    List.map2 (fun x y -> Greater(x, y)) answer_vec_with_subs_list result_exprs_list
  | _ ->
    List.map2 (fun x y -> GreaterEq(x, y)) answer_vec_with_subs_list result_exprs_list
  )
  ;;


let solve_mat_rec mat_ineq = 
  match mat_ineq with
  | VEquals (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "=="
  | VLess (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "<"
  | VLessEq (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "<="
  | VGreater (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add ">"
  | VGreaterEq (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add ">="
  ;;
