open Solve_rec
open Type_def

let old_solve_rec ineq print_steps =
  try
    let _ = if print_steps then Printf.printf "Input Expression:\t %s\n" (Expr_helpers.inequation_to_string ineq) in 
    let simp_ineq = Expr_simplifications.automatic_simplify_inequation ineq in
    let identifier_res = Expr_helpers.find_ovar_ivar simp_ineq in
    let ovar_idents = fst identifier_res in
    let ivar_idents = snd identifier_res in
    if (List.length ovar_idents)>1 || (List.length ivar_idents)>1 then
      raise (Solve_exc "OCRS is unable to solve multivariate recurrences")
    else
      let ovar_ident = List.nth ovar_idents 0 in
      let ivar_ident = List.nth ivar_idents 0 in
      solve_rec_recur simp_ineq ovar_ident ivar_ident print_steps
    with e ->
      let _ = Printf.printf "%s%s\n" (Printexc.to_string e) (Printexc.get_backtrace ()) in
      Equals(Undefined, Undefined)
  ;;

let solve_rec ineq print_steps = 
  let result = old_solve_rec ineq print_steps in
  Deshift.deshift_ineq result
  ;;

let old_solve_rec_str str =
  try
    let lexbuf = Lexing.from_string str in
    let result = Parser.main Lexer.token lexbuf in
    old_solve_rec result true
  with e ->
    let _ = Printf.printf "%s%s\n" (Printexc.to_string e) (Printexc.get_backtrace ()) in
    Equals(Undefined, Undefined)
  ;;

let solve_rec_str str = 
  let result = old_solve_rec_str str in
  Deshift.deshift_ineq result
  ;;

let old_solve_rec_list ineq_list =
  let rec sub_and_solve lis previous_ovar_sol=
    (match lis with
    | [] -> []
    | hd :: tl ->
      let rec sub_previous_sol pair_list ineq =
        (match pair_list with
        | [] -> ineq
        | hd :: tl ->
          let new_ineq = Expr_helpers.substitute ineq (fst hd) (snd hd) in
          sub_previous_sol tl new_ineq
        ) in
      let new_ineq_to_solve = sub_previous_sol previous_ovar_sol hd in
      let rec_sol = old_solve_rec new_ineq_to_solve false in
      let (left, right) = get_right_left_ineq rec_sol in
      rec_sol :: (sub_and_solve tl (previous_ovar_sol @ [(left, right)]))) in
  sub_and_solve ineq_list []
  ;;

let solve_rec_list ineq_list = 
  let results = old_solve_rec_list ineq_list in
  List.map Deshift.deshift_ineq results
  ;;

let old_solve_rec_list_pair pair_list = 
  let rec sub_and_solve lis previous_ovar_sol =
    (match lis with
    | [] -> []
    | hd :: tl ->
      let rec sub_previous_sol pair_list ineq =
        (match pair_list with
        | [] -> ineq
        | hd :: tl ->
          let new_ineq = Expr_helpers.substitute ineq (fst hd) (snd hd) in
          sub_previous_sol tl new_ineq
        ) in
      let new_ineq_to_solve = sub_previous_sol previous_ovar_sol (snd hd) in
      let rec_sol = old_solve_rec new_ineq_to_solve false in
      let (left_of_rec_sol, _) = get_right_left_ineq rec_sol in
      let base_case_ident = List.nth (fst (Expr_helpers.find_ovar_ivar rec_sol)) 0 in 
      let after_subbing_left = Expr_helpers.substitute rec_sol left_of_rec_sol (fst hd) in
      let after_base_sub = sub_base_cases_ineq (fst hd) after_subbing_left base_case_ident in
      let (after_base_left, after_base_right) = get_right_left_ineq after_base_sub in
      let is_Ovar expr =
        (match expr with
        | Output_variable _ -> true
        | _ -> false
        ) in
      if is_Ovar (fst hd) then after_base_sub :: (sub_and_solve tl (previous_ovar_sol @ [(after_base_left, after_base_right)]))
      else after_base_sub :: (sub_and_solve tl previous_ovar_sol)) in
  sub_and_solve pair_list []
  ;;

let solve_rec_list_pair pair_list = 
  let results = old_solve_rec_list_pair pair_list in
  List.map Deshift.deshift_ineq results
  ;;

let solve_mat_recurrence mat_rec print = 
  Solve_mat_rec.solve_mat_rec_ineq mat_rec print
  ;;


let solve_mat_rec mat_rec print = 
  let results = solve_mat_recurrence mat_rec print in
  List.map Deshift.deshift_ineq results
  ;;


let solve_mat_rec_piece mat_rec_piece print = 
  let new_rec = 
    (match mat_rec_piece with
    | PVEquals (primed, mat, unprimed, add) ->
      let shift_add = Array.map Shift.shift_piece_expr add in
      VEquals (primed, mat, unprimed, shift_add)
    | PVLess (primed, mat, unprimed, add) ->
      let shift_add = Array.map Shift.shift_piece_expr add in
      VLess (primed, mat, unprimed, shift_add)
    | PVLessEq (primed, mat, unprimed, add) ->
      let shift_add = Array.map Shift.shift_piece_expr add in
      VLessEq (primed, mat, unprimed, shift_add)
    | PVGreater (primed, mat, unprimed, add) ->
      let shift_add = Array.map Shift.shift_piece_expr add in
      VGreater (primed, mat, unprimed, shift_add)
    | PVGreaterEq (primed, mat, unprimed, add) ->
      let shift_add = Array.map Shift.shift_piece_expr add in
      VGreaterEq (primed, mat, unprimed, shift_add)
    )
  in
  solve_mat_rec new_rec print
  ;;

let solve_mat_recurrence_list mat_rec_list print_steps =
  let rec sub_and_solve lis previous_sol_pairs = 
    (match lis with
    | [] -> []
    | hd :: tl ->
      let rec sub_previous_sol pair_list mat_rec =
        (match pair_list with
        | [] -> mat_rec
        | hd :: tl ->
          (match mat_rec with
          | VEquals (primed, mat, unprimed, add) ->
            let new_add = Array.map (fun x -> Expr_helpers.substitute_expr x (fst hd) (snd hd)) add in
            let new_mat_rec = VEquals (primed, mat, unprimed, new_add) in
            sub_previous_sol tl new_mat_rec
          | VLess (primed, mat, unprimed, add) ->
            let new_add = Array.map (fun x -> Expr_helpers.substitute_expr x (fst hd) (snd hd)) add in
            let new_mat_rec = VLess (primed, mat, unprimed, new_add) in
            sub_previous_sol tl new_mat_rec
          | VLessEq (primed, mat, unprimed, add) ->
            let new_add = Array.map (fun x -> Expr_helpers.substitute_expr x (fst hd) (snd hd)) add in
            let new_mat_rec = VLessEq (primed, mat, unprimed, new_add) in
            sub_previous_sol tl new_mat_rec
          | VGreater (primed, mat, unprimed, add) ->
            let new_add = Array.map (fun x -> Expr_helpers.substitute_expr x (fst hd) (snd hd)) add in
            let new_mat_rec = VGreater (primed, mat, unprimed, new_add) in
            sub_previous_sol tl new_mat_rec
          | VGreaterEq (primed, mat, unprimed, add) ->
            let new_add = Array.map (fun x -> Expr_helpers.substitute_expr x (fst hd) (snd hd)) add in
            let new_mat_rec = VGreaterEq (primed, mat, unprimed, new_add) in
            sub_previous_sol tl new_mat_rec
          )
        ) in
      let new_mat_rec_to_solve = sub_previous_sol previous_sol_pairs hd in
      let rec_sol = solve_mat_recurrence new_mat_rec_to_solve print_steps in
      let left_right_lis = List.map get_right_left_ineq rec_sol in
      rec_sol :: (sub_and_solve tl (previous_sol_pairs @ left_right_lis))
    ) in
  let results = List.concat (sub_and_solve mat_rec_list []) in
  List.map Deshift.deshift_ineq results
  ;;
