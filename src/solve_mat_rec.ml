open Type_def

(*
let rec get_num_denom_of_term unsimp_term =
  let term = Op_simplifications.op_automatic_simplify unsimp_term in
  (match term with 
  | OpPow (base, OpRational exp) when (Mpq.cmp_si exp 0 1) < 0 ->
    let pos_exp = Mpq.init () in
    let _ = Mpq.neg pos_exp exp in
    (OpRational (Mpq.init_set_si 1 1), Op_simplifications.op_automatic_simplify (OpPow(base, OpRational pos_exp)))
  | OpProduct prod_list ->
    let num_denom_list = List.map get_num_denom_of_term prod_list in
    let (num_list, denom_list) = List.split num_denom_list in
    (Op_simplifications.op_automatic_simplify (OpProduct num_list), Op_simplifications.op_automatic_simplify (OpProduct denom_list))
  | _ -> (term, OpRational (Mpq.init_set_si 1 1))
  )
  ;;

let rec make_rat_expr unsimp_expr = 
  let expr = Op_simplifications.op_automatic_simplify unsimp_expr in
  (match expr with
  | OpSum sumList ->
    let rat_sum_list = List.map make_rat_expr sumList in
    let (nums, denoms) = List.split (List.map get_num_denom_of_term rat_sum_list) in
    let new_denom = Op_simplifications.op_automatic_simplify (OpProduct denoms) in
    let new_num_list = List.map2 (fun num denom -> fst (Op_transforms.polynomial_division (Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (OpProduct [new_denom; num]))) (Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand denom)))) nums denoms in
    let rat_num = OpSum new_num_list in
    Op_simplifications.op_automatic_simplify (OpDivide(rat_num, new_denom))
  | OpProduct prodList ->
    Op_simplifications.op_automatic_simplify (OpProduct (List.map make_rat_expr prodList))
  | OpPow (base, exp) ->
    Op_simplifications.op_automatic_simplify (OpPow (make_rat_expr base, make_rat_expr exp))
  | OpPlus _ | OpMinus _ | OpTimes _ | OpDivide _ -> make_rat_expr expr
  | _ -> expr
  )
  ;;
*)

let new_part_frac expr = 
  match expr with
  | OpProduct prodList ->
    let is_denom in_expr =
      (match in_expr with
      | OpPow (_, OpRational exp) when (Mpq.cmp_si exp 0 1)<0 && Expr_simplifications.is_int exp ->
        true
      | _ ->
        false
      ) in
    let (denom, num) = List.partition is_denom prodList in
    let num_expr = Op_simplifications.op_automatic_simplify (OpProduct num) in
    let denom_expr = Op_simplifications.op_automatic_simplify (OpProduct denom) in
    let expanded_num = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify num_expr)) in
    let expanded_denom = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpPow(denom_expr, OpRational (Mpq.init_set_si (-1) 1))))) in
    let (q, r) = Op_transforms.polynomial_division expanded_num expanded_denom in
    if (Type_def.op_expr_order r (OpRational (Mpq.init_set_si 0 1))) = 0 then Op_simplifications.op_automatic_simplify q
    else (
      let factored_inverse_denom = Factor.factor_q expanded_denom in
      Op_simplifications.op_automatic_simplify (OpSum[q; Op_transforms.partial_fraction_3 (Op_simplifications.op_automatic_simplify r) factored_inverse_denom])
    )
  | _ -> Op_transforms.partial_fraction expr
  ;;


let simplify_inv_matrix matrix = 
  Array.map (fun x -> Array.map (fun y -> Op_transforms.simp_rat_expr (Op_transforms.make_rat_expr y)) x) matrix
  (*Array.map (fun x -> Array.map Op_transforms.make_rat_expr x) matrix*)
  ;;

let solve_mat_rec primed matrix unprimed add constr print = 
  (* check to make sure primed subscript is n+1 *)
  let _ = if print then print_endline (Mat_helpers.matrix_rec_to_string (VEquals(primed, matrix, unprimed, add))) in
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
  let add_vec_op_calc = Array.map (fun x -> Expr_to_opcalc.expr_to_opCalc (Expr_simplifications.automatic_simplify (Expr_transforms.algebraic_expand (Expr_simplifications.automatic_simplify x))) ivar_ident) add in
  let new_vec = Mat_functions.multiply_scalar_through_vector base_case_vec (OpMinus(Q, OpRational (Mpq.init_set_si 1 1))) in
  let new_vec = Mat_functions.add_vectors new_vec add_vec_op_calc in
  let new_matrix = Mat_functions.invert_matrix_fast (Mat_functions.sub_matrix q_matrix op_rational_matrix) in
  let simp_matrix = simplify_inv_matrix new_matrix in
  let op_calc_results = Mat_functions.matrix_times_vector simp_matrix new_vec in
  let rat_expr_results = Array.map (fun x -> (Op_transforms.make_rat_expr x)) op_calc_results in
  let _ = 
    if print then
      let _ = Array.iter (fun x -> print_endline (Expr_helpers.op_expr_to_string x)) rat_expr_results in
      print_endline "" 
    in
  let partial_fraction = Array.map new_part_frac rat_expr_results in
  let _ = 
    if print then
      let _ = Array.iter (fun x -> print_endline (Expr_helpers.op_expr_to_string x)) partial_fraction in
      print_endline "" 
    in
  let result_exprs = Array.map (fun x -> Tau_inverse.tau_inverse x ivar_ident) partial_fraction in
  let _ = 
    if print then
      let _ = Array.iter (fun x -> print_endline (Expr_helpers.expr_to_string x)) result_exprs in
      print_endline "" 
    in
  let simp_result_exprs = Array.map (fun x -> Expr_transforms.algebraic_expand (Expr_transforms.inverse_binomial (Expr_simplifications.automatic_simplify x))) result_exprs in
  let answer_vec_with_subs = Mat_helpers.apply_subscript_to_ovec (Ovec (primed_idents, (SSVar ivar_ident))) in
  let result_exprs_list = Array.to_list simp_result_exprs in
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


let solve_mat_rec_ineq mat_ineq print = 
  match mat_ineq with
  | VEquals (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "==" print
  | VLess (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "<" print
  | VLessEq (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add "<=" print
  | VGreater (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add ">" print
  | VGreaterEq (primed, mat, unprimed, add) ->
    solve_mat_rec primed mat unprimed add ">=" print
  ;;
