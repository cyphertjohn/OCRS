open Type_def

exception Solve_exc of string

let get_right_left_op_ineq ineq =
  match ineq with
  | OpEquals (left, right) ->
    (left, right)
  | OpLess (left, right) ->
    (left, right)
  | OpLessEq (left, right) ->
    (left, right)
  | OpGreater (left, right) ->
    (left, right)
  | OpGreaterEq (left, right) ->
    (left, right)
  ;;


let rec find_ovar_ivar_expr expr = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined ->
    ([], [])
  | Output_variable (ovar_ident, subscript) ->
    (match subscript with 
    | SAdd (ivar_ident, _) | SSDiv (ivar_ident, _) -> (ovar_ident :: [], ivar_ident :: [])
    | SSVar ivar_ident -> (ovar_ident :: [], ivar_ident :: []))
  | Input_variable ivar_ident -> ([], ivar_ident :: [])
  | Pow (base, exp) ->
    let base_res = find_ovar_ivar_expr base in
    let exp_res = find_ovar_ivar_expr exp in
    ((fst base_res) @ (fst exp_res), (snd base_res) @ (snd exp_res))
  | Times (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    ((fst left_res) @ (fst right_res), (snd left_res) @ (snd right_res))
  | Plus (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    ((fst left_res) @ (fst right_res), (snd left_res) @ (snd right_res))
  | Product prodList ->
    let list_res = List.map find_ovar_ivar_expr prodList in
    let rec aux lst acc = 
      (match lst with
      | [] -> acc
      | (ovar, ivar) :: [] -> ((fst acc) @ ovar, (snd acc) @ ivar)
      | hd :: tl -> 
        let new_acc = ((fst acc) @ (fst hd), (snd acc) @ (snd hd)) in
        aux tl new_acc) in
    aux list_res ([], []) 
  | Sum sumList ->
    let list_res = List.map find_ovar_ivar_expr sumList in
    let rec aux lst acc = 
      (match lst with
      | [] -> acc
      | (ovar, ivar) :: [] -> ((fst acc) @ ovar, (snd acc) @ ivar)
      | hd :: tl -> 
        let new_acc = ((fst acc) @ (fst hd), (snd acc) @ (snd hd)) in
        aux tl new_acc) in
    aux list_res ([], [])
  | Divide (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    ((fst left_res) @ (fst right_res), (snd left_res) @ (snd right_res))
  | Minus (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    ((fst left_res) @ (fst right_res), (snd left_res) @ (snd right_res))
  | Log (_, expr) ->
    find_ovar_ivar_expr expr
  | Factorial expr ->
    find_ovar_ivar_expr expr
  | Binomial (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    ((fst left_res) @ (fst right_res), (snd left_res) @ (snd right_res))
  ;;
      
let find_ovar_ivar ineq = 
  let rec remove_dup lst = 
    (match lst with
    | [] -> []
    | h::t -> h::(remove_dup (List.filter (fun x -> x<>h) t))) in
  (match ineq with
  | Equals (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | Less (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | LessEq (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | Greater (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | GreaterEq (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list))))
  ;;
  

let solve_add_linear_rec ineq ovar_ident ivar_ident = 
  let simp_ineq = Expr_simplifications.automatic_simplify_inequation ineq in
  let _ = Printf.printf "Expression to Solve:\t %s\n" (Expr_helpers.inequation_to_string simp_ineq) in
  let op_ineq = Op_simplifications.op_automatic_simplify_inequation (Expr_to_opcalc.inequation_to_opCalc simp_ineq) in
  let _ = Printf.printf "Operational Calculus:\t %s\n" (Expr_helpers.op_inequation_to_string op_ineq) in
  let isolated_op_ineq = Isolate_Ovar.solve_for_Ovar op_ineq ovar_ident ivar_ident in
  let _ = Printf.printf "Isolated Expression:\t %s\n" (Expr_helpers.op_inequation_to_string isolated_op_ineq) in
  let expanded_ineq = Op_simplifications.op_automatic_simplify_inequation (Op_transforms.algebraic_expand_inequation isolated_op_ineq) in
  let _ = Printf.printf "Expanded Expression:\t %s\n" (Expr_helpers.op_inequation_to_string expanded_ineq) in
  if (Tau_inverse.complete_tiling (snd(get_right_left_op_ineq expanded_ineq))) then
    let initial_result = Tau_inverse.tau_inverse_inequation expanded_ineq ivar_ident in
    let _ = Printf.printf "Initial Result:\t\t %s\n" (Expr_helpers.inequation_to_string initial_result) in
    let result = Expr_simplifications.automatic_simplify_inequation (Expr_transforms.algebraic_expand_inequation (Expr_transforms.inverse_binomial_ineq (Expr_simplifications.automatic_simplify_inequation initial_result))) in
    let _ = Printf.printf "Final Result:\t\t %s\n" (Expr_helpers.inequation_to_string result) in
    result
  else
    let (left_side, right_side) = get_right_left_op_ineq expanded_ineq in
    let expand_terms_with_no_transform expr = 
      match expr with
      | OpSum sumList ->
        let rec expand_terms expr_list acc i = 
          if i = List.length expr_list then Op_simplifications.op_automatic_simplify (OpSum acc)
          else
            let curr = List.nth expr_list i in
            if Tau_inverse.complete_tiling curr then expand_terms expr_list (acc @ [curr]) (i+1)
            else expand_terms expr_list (acc @ [Op_transforms.partial_fraction curr]) (i+1)
          in expand_terms sumList [] 0
      | _ -> Op_transforms.partial_fraction expr in
    let right_part_frac = expand_terms_with_no_transform right_side in
    let new_ineq = OpEquals(left_side, right_part_frac) in
    let _ = Printf.printf "After Partial Fraction:\t %s\n" (Expr_helpers.op_inequation_to_string new_ineq) in
    let initial_result = Tau_inverse.tau_inverse_inequation new_ineq ivar_ident in
    let _ = Printf.printf "Initial Result:\t\t %s\n" (Expr_helpers.inequation_to_string initial_result) in
    let result = Expr_simplifications.automatic_simplify_inequation (Expr_transforms.algebraic_expand_inequation (Expr_transforms.inverse_binomial_ineq (Expr_simplifications.automatic_simplify_inequation initial_result))) in
    let _ = Printf.printf "Final Result:\t\t %s\n" (Expr_helpers.inequation_to_string result) in
    result
  ;;



let rec find_lowest_add_expr expr = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ ->
    max_int
  | Output_variable (_, subscript) ->
    (match subscript with
    | SSVar _ -> 0
    | SAdd (_, z) -> z
    | _ -> raise (Solve_exc "non-linear rec should never get here"))
  | Pow (base, exp) ->
    let base_res = find_lowest_add_expr base in
    let exp_res = find_lowest_add_expr exp in
    min base_res exp_res
  | Times (left, right) ->
    let left_res = find_lowest_add_expr left in
    let right_res = find_lowest_add_expr right in
    min left_res right_res
  | Plus (left, right) ->
    let left_res = find_lowest_add_expr left in
    let right_res = find_lowest_add_expr right in
    min left_res right_res
  | Minus (left, right) ->
    let left_res = find_lowest_add_expr left in
    let right_res = find_lowest_add_expr right in
    min left_res right_res
  | Divide (left, right) ->
    let left_res = find_lowest_add_expr left in
    let right_res = find_lowest_add_expr right in
    min left_res right_res
  | Binomial (left, right) ->
    let left_res = find_lowest_add_expr left in
    let right_res = find_lowest_add_expr right in
    min left_res right_res
  | Log (_, expression) ->
    find_lowest_add_expr expression
  | Factorial expression ->
    find_lowest_add_expr expression
  | Product prodList ->
    let res_lst = List.map find_lowest_add_expr prodList in
    List.fold_left min max_int res_lst
  | Sum sumList ->
    let res_lst = List.map find_lowest_add_expr sumList in
    List.fold_left min max_int res_lst
  ;;


let find_lowest_add ineq = 
  match ineq with
  | Equals (left, right) ->
    min (find_lowest_add_expr left) (find_lowest_add_expr right)
  | Less (left, right) ->
    min (find_lowest_add_expr left) (find_lowest_add_expr right)
  | LessEq (left, right) ->
    min (find_lowest_add_expr left) (find_lowest_add_expr right)
  | Greater (left, right) ->
    min (find_lowest_add_expr left) (find_lowest_add_expr right)
  | GreaterEq (left, right) ->
    min (find_lowest_add_expr left) (find_lowest_add_expr right)
  ;; 




let rec shift_sub expr ovar_ident ivar_ident z =
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined ->
    expr
  | Output_variable (oident, subscript) when oident = ovar_ident ->
    (match subscript with
    | SSVar iident when ivar_ident = iident -> 
      Output_variable (oident, SAdd (iident, (-1*z)))
    | SAdd (iident, a) when ivar_ident = iident ->
      let b = a + (-1 * z) in
      if b = 0 then Output_variable (oident, SSVar iident)
      else Output_variable (oident, SAdd (iident, b))
    | _ -> raise (Solve_exc "this section is only for linear recurrences"))
  | Input_variable iident when iident = ivar_ident ->
    Sum[Input_variable iident; Rational (snd(Mpfr.init_set_si (-1*z) Mpfr.Near))]
  | Pow (base, exp) ->
    let base_res = shift_sub base ovar_ident ivar_ident z in
    let exp_res = shift_sub exp ovar_ident ivar_ident z in
    Pow (base_res, exp_res)
  | Times (left, right) ->
    let left_res = shift_sub left ovar_ident ivar_ident z in
    let right_res = shift_sub right ovar_ident ivar_ident z in
    Times (left_res, right_res)
  | Plus (left, right) ->
    let left_res = shift_sub left ovar_ident ivar_ident z in
    let right_res = shift_sub right ovar_ident ivar_ident z in
    Plus (left_res, right_res)
  | Minus (left, right) ->
    let left_res = shift_sub left ovar_ident ivar_ident z in
    let right_res = shift_sub right ovar_ident ivar_ident z in
    Minus (left_res, right_res)
  | Divide (left, right) ->
    let left_res = shift_sub left ovar_ident ivar_ident z in
    let right_res = shift_sub right ovar_ident ivar_ident z in
    Divide (left_res, right_res)
  | Binomial (left, right) ->
    let left_res = shift_sub left ovar_ident ivar_ident z in
    let right_res = shift_sub right ovar_ident ivar_ident z in
    Binomial (left_res, right_res)
  | Log (base, expression) ->
    Log (base, shift_sub expression ovar_ident ivar_ident z)
  | Factorial expression ->
    Factorial (shift_sub expression ovar_ident ivar_ident z)
  | Product prodList ->
    Product (List.map (fun x -> shift_sub x ovar_ident ivar_ident z) prodList)
  | Sum sumList ->
    Sum (List.map (fun x -> shift_sub x ovar_ident ivar_ident z) sumList)
  | _ ->
    raise (Solve_exc "OCRS is unable to solve multivariate recurrences")
  ;;

let shift ineq ovar_ident ivar_ident z = 
  match ineq with
  | Equals (left, right) ->
    Equals(shift_sub left ovar_ident ivar_ident z, shift_sub right ovar_ident ivar_ident z)
  | Less (left, right) ->
    Less(shift_sub left ovar_ident ivar_ident z, shift_sub right ovar_ident ivar_ident z)
  | LessEq (left, right) ->
    LessEq(shift_sub left ovar_ident ivar_ident z, shift_sub right ovar_ident ivar_ident z)
  | Greater (left, right) ->
    Greater(shift_sub left ovar_ident ivar_ident z, shift_sub right ovar_ident ivar_ident z)
  | GreaterEq (left, right) ->
    GreaterEq(shift_sub left ovar_ident ivar_ident z, shift_sub right ovar_ident ivar_ident z)
  ;;



let rec get_beta_expr expr ovar_ident ivar_ident = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ ->
    0
  | Output_variable (oident, subscript) when oident = ovar_ident ->
    (match subscript with
    | SSDiv (iident, beta) when ivar_ident = iident ->
      beta
    | _ -> 0)
  | Pow (base, exp) ->
    max (get_beta_expr base ovar_ident ivar_ident) (get_beta_expr exp ovar_ident ivar_ident)
  | Times (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Plus (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Minus (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Divide (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Binomial (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Log (_, expression) ->
    get_beta_expr expression ovar_ident ivar_ident
  | Factorial expression ->
    get_beta_expr expression ovar_ident ivar_ident
  | Product prodList ->
    let res_lis = List.map (fun x -> get_beta_expr x ovar_ident ivar_ident) prodList in
    List.fold_left max 0 res_lis
  | Sum sumList ->
    let res_lis = List.map (fun x -> get_beta_expr x ovar_ident ivar_ident) sumList in
    List.fold_left max 0 res_lis
  | _ ->
    raise (Solve_exc "OCRS is unable to solve multivariate recurrences")
  ;;

let get_beta ineq ovar_ident ivar_ident = 
  match ineq with
  | Equals (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Less (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | LessEq (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | Greater (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  | GreaterEq (left, right) ->
    max (get_beta_expr left ovar_ident ivar_ident) (get_beta_expr right ovar_ident ivar_ident)
  ;;



let rec substitute_expr expr old_term new_term = 
  if expr = old_term then new_term
  else
    (match expr with
    | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ | Output_variable _ ->
      expr
    | Pow (base, exp) ->
      Pow (substitute_expr base old_term new_term, substitute_expr exp old_term new_term)
    | Times (left, right) ->
      Times (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Plus (left, right) ->
      Plus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Minus (left, right) ->
      Minus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Divide (left, right) ->
      Divide (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Binomial (left, right) ->
      Binomial (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Log (base, expression) ->
      Log (base, substitute_expr expression old_term new_term)
    | Factorial expression ->
      Factorial (substitute_expr expression old_term new_term)
    | Product prodList ->
      Product (List.map (fun x -> substitute_expr x old_term new_term) prodList)
    | Sum sumList ->
      Sum (List.map (fun x -> substitute_expr x old_term new_term) sumList))
  ;;

let substitute ineq old_term new_term = 
  match ineq with
  | Equals (left, right) ->
    Equals(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Less (left, right) ->
    Less(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | LessEq (left, right) ->
    LessEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Greater (left, right) ->
    Greater(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | GreaterEq (left, right) ->
    GreaterEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  ;;


let rec solve_rec_recur ineq ovar_ident ivar_ident = 
  let beta = get_beta ineq ovar_ident ivar_ident in
  if beta <> 0 then
    let _ = Printf.printf "Subsituting a_k for %s_%s\n" ovar_ident ivar_ident in
    let new_rec = substitute ineq (Output_variable (ovar_ident, SSVar ivar_ident)) (Output_variable ("a", SSVar "k")) in
    let new_rec = substitute new_rec (Output_variable (ovar_ident, SSDiv (ivar_ident, beta))) (Output_variable ("a", SAdd("k", (-1)))) in
    let new_rec = substitute new_rec (Input_variable ivar_ident) (Pow(Rational (snd(Mpfr.init_set_si beta Mpfr.Near)), Input_variable "k")) in
    let _ = Printf.printf "Will Solve:\t\t %s\n" (Expr_helpers.inequation_to_string new_rec) in
    let res =  solve_rec_recur new_rec "a" "k" in
    let final_answer = substitute res (Base_case ("a", 0)) (Base_case (ovar_ident, 1)) in
    let final_answer = substitute final_answer (Output_variable ("a", SSVar "k")) (Output_variable (ovar_ident, SSVar ivar_ident)) in
    let final_answer = substitute final_answer (Input_variable "k") (Log(snd(Mpfr.init_set_si beta Mpfr.Near), Input_variable ivar_ident)) in
    let _ = Printf.printf "After Sub back:\t\t %s\n" (Expr_helpers.inequation_to_string final_answer) in
    let final_answer = Expr_simplifications.automatic_simplify_inequation final_answer in
    let _ = Printf.printf "Final answer:\t\t %s\n" (Expr_helpers.inequation_to_string final_answer) in
    final_answer
  else
    let z = find_lowest_add ineq in
    if z <> 0 then
      solve_rec_recur (shift ineq ovar_ident ivar_ident z) ovar_ident ivar_ident
    else
      solve_add_linear_rec ineq ovar_ident ivar_ident
  ;;


let solve_rec ineq = 
  let _ = Printf.printf "Input Expression:\t %s\n" (Expr_helpers.inequation_to_string ineq) in
  let simp_ineq = Expr_simplifications.automatic_simplify_inequation ineq in
  let identifier_res = find_ovar_ivar simp_ineq in
  let ovar_idents = fst identifier_res in
  let ivar_idents = snd identifier_res in
  if (List.length ovar_idents)>1 || (List.length ivar_idents)>1 then
    raise (Solve_exc "OCRS is unable to solve multivariate recurrences")
  else
    let ovar_ident = List.nth ovar_idents 0 in
    let ivar_ident = List.nth ivar_idents 0 in
    solve_rec_recur simp_ineq ovar_ident ivar_ident
  ;;


let solve_rec_str str = 
  try 
    let lexbuf = Lexing.from_string str in
    let result = Parser.main Lexer.token lexbuf in
    solve_rec result
  with e ->
    let _ = Printf.printf "%s%s\n" (Printexc.to_string e) (Printexc.get_backtrace ()) in
    Equals(Undefined, Undefined)
  ;;

