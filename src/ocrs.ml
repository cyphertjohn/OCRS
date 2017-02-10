open Solve_rec
open Type_def

let solve_rec ineq print_steps =
  try
    let _ = if print_steps then Printf.printf "Input Expression:\t %s\n" (Expr_helpers.inequation_to_string ineq) in 
    let simp_ineq = Expr_simplifications.automatic_simplify_inequation ineq in
    let identifier_res = find_ovar_ivar simp_ineq in
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


let solve_rec_str str =
  try
    let lexbuf = Lexing.from_string str in
    let result = Parser.main Lexer.token lexbuf in
    solve_rec result true
  with e ->
    let _ = Printf.printf "%s%s\n" (Printexc.to_string e) (Printexc.get_backtrace ()) in
    Equals(Undefined, Undefined)
  ;;

let solve_rec_list ineq_list =
  let rec sub_and_solve lis previous_ovar_sol=
    (match lis with
    | [] -> []
    | hd :: tl ->
      let rec sub_previous_sol pair_list ineq =
        (match pair_list with
        | [] -> ineq
        | hd :: tl ->
          let new_ineq = substitute ineq (fst hd) (snd hd) in
          sub_previous_sol tl new_ineq
        ) in
      let new_ineq_to_solve = sub_previous_sol previous_ovar_sol hd in
      let rec_sol = solve_rec new_ineq_to_solve false in
      let (left, right) = get_right_left_ineq rec_sol in
      rec_sol :: (sub_and_solve tl (previous_ovar_sol @ [(left, right)]))) in
  sub_and_solve ineq_list []
  ;;

let solve_rec_list_pair pair_list = 
  let rec sub_and_solve lis previous_ovar_sol =
    (match lis with
    | [] -> []
    | hd :: tl ->
      let rec sub_previous_sol pair_list ineq =
        (match pair_list with
        | [] -> ineq
        | hd :: tl ->
          let new_ineq = substitute ineq (fst hd) (snd hd) in
          sub_previous_sol tl new_ineq
        ) in
      let new_ineq_to_solve = sub_previous_sol previous_ovar_sol (snd hd) in
      let rec_sol = solve_rec new_ineq_to_solve false in
      let (left_of_rec_sol, _) = get_right_left_ineq rec_sol in
      let base_case_ident = List.nth (fst (find_ovar_ivar rec_sol)) 0 in 
      let after_subbing_left = substitute rec_sol left_of_rec_sol (fst hd) in
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
