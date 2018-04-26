open Type_def

let kronecker a b =
  let m = Array.length a in
  let n = Array.length (Array.get a 0) in
  let p = Array.length b in
  let q = Array.length (Array.get b 0) in
  let res = Array.make_matrix (m*p) (n*q) (Mpq.init_set_si 0 1) in
  let _ =
    for i = 0 to m*p - 1 do
      for j = 0 to n*q - 1 do
        let prod = Mpq.init () in
        let _ = Mpq.mul prod a.(i/p).(j/q) b.(i mod p).(j mod q) in
        res.(i).(j) <- prod
      done
    done in
  res
  ;;


let get_coef_array_of_poly expr length =
  let res = Array.make length (Mpq.init_set_si 0 1) in
  let _ = (match expr with
    | OpRational rat -> 
      res.(0) <- rat
    | Q -> res.(1) <- (Mpq.init_set_si 1 1)
    | OpPow (Q, OpRational rat) ->
      let deg = Mpz.init () in
      let _ = Mpq.get_z deg rat in
      res.(Mpz.get_int deg) <- (Mpq.init_set_si 1 1)
    | OpProduct [OpRational coef; OpPow (Q, OpRational exp)] ->
      let deg_z = Mpz.init () in
      let _ = Mpq.get_z deg_z exp in
      res.(Mpz.get_int deg_z) <- coef
    | OpProduct [OpRational coef; Q] ->
      res.(1) <- coef
    | OpSum sum_list ->
      let get_pos_and_coef_of_term term = 
        (match term with
        | OpRational rat ->
          (rat, 0)
        | Q -> (Mpq.init_set_si 1 1, 1)
        | OpProduct [OpRational coef; Q] ->
          (coef, 1)
        | OpPow (Q, OpRational rat) ->
          let deg = Mpz.init () in
          let _ = Mpq.get_z deg rat in
          (Mpq.init_set_si 1 1, Mpz.get_int deg)
        | OpProduct [OpRational coef; OpPow (Q, OpRational exp)] ->
          let deg_z = Mpz.init () in
          let _ = Mpq.get_z deg_z exp in
          (coef, Mpz.get_int deg_z)
        | _ -> failwith "Input wasn't a polynomial")
      in
      let coef_loc_pair = List.map get_pos_and_coef_of_term sum_list in
      List.iter (fun x -> res.(snd x) <- fst x) coef_loc_pair
    | _ -> failwith "Input wasn't a modular polynomial"
  ) in
  res
  ;;

let get_companion_matrix coef_list = 
  let row_1 = Array.make (Array.length coef_list) (Mpq.init_set_si 0 1) in
  let _ = 
    for i = 0 to (Array.length coef_list) - 2 do
      let neg = Mpq.init () in
      let _ = Mpq.neg neg coef_list.((Array.length coef_list) - 2 - i) in
      row_1.(i) <- neg
    done
  in
  let _ = row_1.((Array.length coef_list) - 1) <- (Mpq.init_set_si 1 1) in
  let comp_mat = Array.make_matrix (Array.length row_1) (Array.length row_1) (Mpq.init_set_si 0 1) in
  let _ = comp_mat.(0) <- row_1 in
  let _ =
    for i = 1 to (Array.length comp_mat) - 2 do
      for j = 0 to (Array.length comp_mat) - 2 do
        if i - 1 = j then comp_mat.(i).(j) <- Mpq.init_set_si 1 1
      done
    done
  in
  let _ = comp_mat.((Array.length comp_mat)-1).((Array.length comp_mat)-1) <- Mpq.init_set_si 1 1 in
  comp_mat
  ;;

let simplify_inv_matrix matrix = 
  Array.map (fun x -> Array.map (fun y -> Op_transforms.simp_rat_expr (Op_transforms.make_rat_expr y)) x) matrix
  ;;

let inner_product a b = 
  let add_Mpq x y = 
    let res = Mpq.init () in
    let _ = Mpq.add res x y in
    res
  in
  let mul_Mpq x y = 
    let res = Mpq.init () in
    let _ = Mpq.mul res x y in
    res
  in
  let temp = Array.make (Array.length a) (Mpq.init_set_si 0 1) in
  let _ =
    for i = 0 to (Array.length temp) - 1 do
      temp.(i) <- mul_Mpq a.(i) b.(i)
    done
  in
  Array.fold_left add_Mpq (Mpq.init_set_si 0 1) temp 
  ;;

let get_init_vector first_row shift =
  let temp = Array.make (Array.length first_row) (Mpq.init_set_si 0 1) in
  let _ = temp.((Array.length temp) - 1) <- (Mpq.init_set_si 1 1) in
  let res = Array.make (Array.length first_row) (Mpq.init_set_si 0 1) in
  let _ = res.((Array.length temp) - 1) <- (Mpq.init_set_si 1 1) in
  let _ =
    for i = 1 to shift do
      let _ =
        for j = 0 to (Array.length first_row - 3) do
          res.((Array.length first_row)- 2 - j) <- res.((Array.length first_row) - 3 - j)
        done
      in
      let _ = res.(0) <- inner_product temp first_row in
      for j = 0 to (Array.length first_row) - 1 do
        temp.(j) <- res.(j)
      done
    done
  in
  res
  ;;

(** a and b are of the form q^n/(poly(q)) when the degree of the denom is greater then n *)
let unit_mult a b =
  let (a_num, a_denom) = Op_transforms.get_num_denom_of_term a in
  let (b_num, b_denom) = Op_transforms.get_num_denom_of_term b in
  let deg_a_denom = snd (Op_transforms.degree a_denom) in
  let deg_b_denom = snd (Op_transforms.degree b_denom) in
  let deg_a_denom_int = int_of_string (Mpq.to_string deg_a_denom) in
  let deg_b_denom_int = int_of_string (Mpq.to_string deg_b_denom) in
  let coef_list_a_denom = get_coef_array_of_poly a_denom (deg_a_denom_int + 1) in
  let coef_list_b_denom = get_coef_array_of_poly b_denom (deg_b_denom_int + 1) in
  let a_comp = get_companion_matrix coef_list_a_denom in
  let b_comp = get_companion_matrix coef_list_b_denom in
  let n = Array.length a_comp in
  let p = Array.length b_comp in
  let trans = kronecker a_comp b_comp in
  let (coef_a_num, deg_a_num) = Op_transforms.degree a_num in
  let (coef_b_num, deg_b_num) = Op_transforms.degree b_num in
  let deg_a_num_int = int_of_string (Mpq.to_string deg_a_num) in
  let deg_b_num_int = int_of_string (Mpq.to_string deg_b_num) in
  let a_init = [|get_init_vector (Array.get a_comp 0) deg_a_num_int|] in
  let b_init = [|get_init_vector (Array.get b_comp 0) deg_b_num_int|] in
  let init = Array.get (Mat_helpers.transpose_matrix (kronecker (Mat_helpers.transpose_matrix a_init) (Mat_helpers.transpose_matrix b_init))) 0 in
  let q_matrix = Array.make_matrix (Array.length trans) (Array.length trans) (OpRational (Mpq.init_set_si 0 1)) in
  let _ =
    for i = 0 to (Array.length q_matrix) - 1 do
      q_matrix.(i).(i) <- Q
    done
  in
  let op_trans = Array.map (Array.map (fun x -> OpRational x)) trans in
  let op_init = Array.map (fun x -> OpRational x) init in
  let new_matrix = Mat_functions.invert_matrix_fast (Mat_functions.sub_matrix q_matrix op_trans) in
  let simp_matrix = simplify_inv_matrix new_matrix in
  let vec = Mat_functions.multiply_scalar_through_vector op_init (OpMinus(Q, OpRational (Mpq.init_set_si 1 1))) in
  let op_calc_results = Mat_functions.matrix_times_vector simp_matrix vec in
  Op_simplifications.op_automatic_simplify (OpTimes(Array.get op_calc_results (n*p - p - 2), OpTimes(coef_a_num, coef_b_num)))
  ;;


let rec unit_mult_pair a b =
  if ((not (Op_transforms.contains_q a)) || (not (Op_transforms.contains_q b))) then (Op_simplifications.op_automatic_simplify (OpTimes (a, b)))
  else
  let a_expand = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand a) in
  let b_expand = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand b) in
  let pair_list x_list y_list = 
    List.flatten (List.map (fun x -> (List.map (fun y -> (x,y)) y_list)) x_list)
  in
  (match (a_expand, b_expand) with
  | (OpSum a_sum_list, OpSum b_sum_list) ->
    let expanded_list = pair_list a_sum_list b_sum_list in
    Op_simplifications.op_automatic_simplify (OpSum (List.map (fun pair -> unit_mult_pair (fst pair) (snd pair)) expanded_list))
  | (OpSum a_sum_list, _) ->
    let expanded_list = pair_list a_sum_list [b_expand] in
    Op_simplifications.op_automatic_simplify (OpSum (List.map (fun pair -> unit_mult_pair (fst pair) (snd pair)) expanded_list))
  | (_, OpSum b_sum_list) ->
    let expanded_list = pair_list [a_expand] b_sum_list in
    Op_simplifications.op_automatic_simplify (OpSum (List.map (fun pair -> unit_mult_pair (fst pair) (snd pair)) expanded_list))
  | _ -> (*Should be a rational function now *)
    unit_mult a_expand b_expand
  )
  ;;

let unit_mult_list op_calc_list = 
  match op_calc_list with
  | [] -> OpRational (Mpq.init_set_si 1 1) (* Should never happen *)
  | a :: [] -> a (* Also should never happen *)
  | a :: tl ->
    List.fold_left unit_mult_pair (List.nth op_calc_list 0) tl
  ;;
