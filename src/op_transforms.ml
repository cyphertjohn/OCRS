open Type_def
open Op_simplifications


let rec expand_product r s = 
  (*let q_minus1 = op_automatic_simplify (OpSum [Q; OpRational (Mpq.init_set_si (-1) 1)]) in*)
  match (r, s) with
  | (OpSum sumList, _) (*when (op_expr_order r q_minus1) <> 0*)-> (* maintain q-1 since they are frequent *)
    (match sumList with
    | [] -> failwith "Sum operand list was empty"
    | hd :: [] -> expand_product hd s
    | hd :: tail -> op_automatic_simplify (OpSum [expand_product hd s; expand_product (OpSum tail) s]))
  | (_, OpSum _) -> expand_product s r
  | _ -> op_automatic_simplify (OpProduct [r; s])
  ;;

let rec expand_power u n =
  match u with
  | OpSum sumList ->
    (match sumList with
    | [] -> failwith "Sum operandList was empty"
    | hd :: [] -> expand_power hd n
    | f :: tail ->
      let r = OpSum tail in
      let zero = Mpq.init_set_si 0 1 in
      let rec aux acc k = 
        if (Mpq.cmp k n) > 0 then OpSum acc
        else
          let c = Expr_simplifications.binomial n k in
          let n_minus_k = Mpq.init () in
          let k_plus1 = Mpq.init () in
          let _ = Mpq.add k_plus1 k (Mpq.init_set_si 1 1) in
          let _ = Mpq.sub n_minus_k n k in
          aux (acc @ [(expand_product (OpProduct [OpRational c; OpPow(f, (OpRational n_minus_k))]) (expand_power r k))]) k_plus1 in
      op_automatic_simplify (aux [(OpRational zero)] zero))
  | _ -> OpPow (u, OpRational n)
  ;;
    

let rec algebraic_expand expr = 
  match expr with
  | OpSum sumList ->
    (match sumList with
    | [] -> failwith "Sum Operand List was empty"
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> op_automatic_simplify (OpSum [algebraic_expand hd; algebraic_expand (OpSum tail)]))
  | OpProduct prodList ->
    (match prodList with
    | [] -> failwith "Product Operand List was empty"
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> op_automatic_simplify (expand_product (algebraic_expand hd) (algebraic_expand (OpProduct tail))))
  | OpPow (base, exp) ->
    (match exp with
    | OpRational rat when Expr_simplifications.is_int rat && (Mpq.cmp_si rat 2 1) >= 0 ->
      op_automatic_simplify (expand_power (algebraic_expand base) rat)
    | _ -> OpPow (base, exp))
  | _ -> expr
  ;;

let algebraic_expand_inequation ineq = 
  match ineq with
  | OpEquals(left, right) -> OpEquals(algebraic_expand left, algebraic_expand right)	(* temporary solution *)
  | OpGreater(left, right) -> OpGreater(algebraic_expand left, algebraic_expand right)
  | OpGreaterEq(left, right) -> OpGreaterEq(algebraic_expand left, algebraic_expand right)
  | OpLess(left, right) -> OpLess(algebraic_expand left, algebraic_expand right)
  | OpLessEq(left, right) -> OpLessEq(algebraic_expand left, algebraic_expand right)
  ;;


let rec contains_q expr=
  match expr with
  | OpPlus (left, right) ->
      (contains_q left) || (contains_q right)
  | OpMinus (left, right) ->
      (contains_q left) || (contains_q right)
  | OpTimes (left, right) ->
      (contains_q left) || (contains_q right)
  | OpDivide (left, right) ->
      (contains_q left) || (contains_q right)
  | OpProduct expr_list ->
      List.exists contains_q expr_list
  | OpSum expr_list ->
      List.exists contains_q expr_list
  | OpSymbolic_Constant _ ->
      false
  | OpBase_case (_, _) ->
      false
  | OpOutput_variable (ident , subscript) ->
       false
  | OpInput_variable str ->
      false
  | OpRational rat ->
      false
  | OpLog (_, expression) ->
      contains_q expression
  | OpPow (left, right) ->
      (contains_q left) || (contains_q right)
  | Q ->
      true
  | OpUndefined ->
      false
  ;;


let rec degree_monomial u =
  match u with
  | Q ->
    (OpRational (Mpq.init_set_si 1 1), Mpq.init_set_si 1 1)
  | OpPow(Q, OpRational rat) when (Mpq.cmp_si rat 1 1)>0 ->
    (OpRational (Mpq.init_set_si 1 1), rat)
  | OpProduct prodList ->
    let coef_deg_list = List.map degree_monomial prodList in
    if List.exists (fun x -> (fst x) = OpUndefined) coef_deg_list then (OpUndefined, Mpq.init_set_si 0 1)
    else 
      let max a b =
        let a_deg = snd a in
        let b_deg = snd b in
        let cmp_result = Mpq.cmp a_deg b_deg in
        if cmp_result < 0 then b 
        else a in
      let m = List.fold_left max (OpSymbolic_Constant "y", Mpq.init_set_si (-1) 1) coef_deg_list in
      (Op_simplifications.op_automatic_simplify (OpDivide(u, OpPow (Q, OpRational (snd m)))), (snd m))
  | _ ->
    if contains_q u then (OpUndefined, Mpq.init_set_si 0 1)
    else (u, Mpq.init_set_si 0 1)
  ;;

 
(* the degree of the polynomial u in q *)
let degree u = 
  let x = degree_monomial u in
  if fst x <> OpUndefined then x
  else (match u with
    | OpSum sumList ->
      let degreelist = List.map degree_monomial sumList in
      if List.exists (fun x1 -> fst x1 = OpUndefined) degreelist then (OpUndefined, Mpq.init_set_si 0 1)
      else 
        let max a b = 
          let a_deg = snd a in
          let b_deg = snd b in
          let cmp_result = Mpq.cmp a_deg b_deg in
          if cmp_result < 0 then b
          else a in
        List.fold_left max (OpSymbolic_Constant "y", Mpq.init_set_si (-1) 1) degreelist
    | _ -> (OpUndefined, Mpq.init_set_si 0 1))
  ;;

(* u and v are polynomials in q *)
let polynomial_division u v =
  let x = degree u in
  let y = degree v in
  let n = snd y in
  let lcv = fst y in
  let rec aux acc m r =
    let is_zero expr = 
      match expr with
      | OpRational rat when (Mpq.cmp_si rat 0 1)=0 -> true
      | _ -> false in
    if (Mpq.cmp m n)<0 || (is_zero r) then (acc, r)
    else 
      let lcr = fst (degree r) in
      let s = Op_simplifications.op_automatic_simplify (OpDivide(lcr, lcv)) in
      let new_acc = Op_simplifications.op_automatic_simplify (OpSum[acc; OpProduct[s; OpPow(Q, OpMinus(OpRational m, OpRational n))]]) in
      let new_r = Op_simplifications.op_automatic_simplify (algebraic_expand (Op_simplifications.op_automatic_simplify (OpMinus(OpMinus(r, OpProduct[lcr; OpPow(Q, OpRational m)]), OpProduct[OpMinus(v, OpProduct[lcv;OpPow(Q, OpRational n)]);s;OpPow(Q, OpMinus(OpRational m, OpRational n))])))) in
      let new_m = snd (degree new_r) in
      aux new_acc new_m new_r in
  aux (OpRational (Mpq.init_set_si 0 1)) (snd x) u
  ;;


let extended_euclidean u v =
  match (u, v) with
  | (OpRational rat1, OpRational rat2) when (Mpq.cmp_si rat1 0 1)=0 && (Mpq.cmp_si rat2 0 1)=0 ->
    [OpRational (Mpq.init_set_si 0 1); OpRational (Mpq.init_set_si 0 1); OpRational (Mpq.init_set_si 0 1)]
  | _ ->
    let rec aux u v app ap bpp bp =
      (match v with
      | OpRational rat when (Mpq.cmp_si rat 0 1)=0 -> [u; app; bpp;] 
      | _ ->
        let division_result = polynomial_division u v in
        let a = Op_simplifications.op_automatic_simplify (OpMinus (app, OpTimes(fst division_result, ap))) in
        let b = Op_simplifications.op_automatic_simplify (OpMinus (bpp, OpTimes(fst division_result, bp))) in
        let new_app = ap in
        let new_ap = a in
        let new_bpp = bp in
        let new_bp = b in
        let new_u = v in
        let new_v = snd division_result in
        aux new_u new_v new_app new_ap new_bpp new_bp) in
      let aux_result = aux u v (OpRational (Mpq.init_set_si 1 1)) (OpRational (Mpq.init_set_si 0 1)) (OpRational (Mpq.init_set_si 0 1)) (OpRational (Mpq.init_set_si 1 1)) in
      let c = fst (degree (List.nth aux_result 0)) in
      let app_res = algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide(List.nth aux_result 1, c))) in
      let bpp_res = algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide(List.nth aux_result 2, c))) in
      let u_res = algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide(List.nth aux_result 0, c))) in
      [u_res; app_res; bpp_res]
  ;;


let partial_fraction_1 u v1 v2 =
  let s = extended_euclidean v1 v2 in
  let a = List.nth s 1 in
  let b = List.nth s 2 in
  let u1_result = polynomial_division (algebraic_expand (Op_simplifications.op_automatic_simplify (OpProduct[b; u]))) v1 in
  let u2_result = polynomial_division (algebraic_expand (Op_simplifications.op_automatic_simplify (OpProduct[a; u]))) v2 in
  (snd u1_result, snd u2_result)
  ;;

let rec partial_fraction_2 u v =
  match v with
  | OpProduct prod_list ->
    let f = List.nth prod_list 0 in
    let r = Op_simplifications.op_automatic_simplify (OpDivide(v, f)) in
    if not(contains_q f) then Op_simplifications.op_automatic_simplify (OpProduct[OpDivide(OpRational (Mpq.init_set_si 1 1), f); (partial_fraction_2 u r)])
    else
      let s = partial_fraction_1 u (algebraic_expand f) (algebraic_expand r) in
      let u1 = fst s in
      let w = snd s in
      Op_simplifications.op_automatic_simplify (OpSum[OpDivide(u1, f); (partial_fraction_2 w r)])
  | _ ->
    Op_simplifications.op_automatic_simplify (OpDivide(u, v))
  ;;


let rec polynomial_expansion u v t = 
  match u with
  | OpRational rat when (Mpq.cmp_si rat 0 1)=0 ->
    u
  | _ ->
    let d = polynomial_division u v in
    let q = fst d in
    let r = snd d in
    algebraic_expand (OpSum[OpProduct[t; polynomial_expansion q v t]; r])
  ;;

let rec substitute expr a t =
  let simp_expr = Op_simplifications.op_automatic_simplify expr in
  let simp_a = Op_simplifications.op_automatic_simplify a in
  if (op_expr_order simp_expr simp_a) = 0 then t
  else
    (match simp_expr with
    | OpPlus (left, right) ->
      Op_simplifications.op_automatic_simplify (OpPlus (substitute left simp_a t, substitute right simp_a t))
    | OpMinus (left, right) ->
      Op_simplifications.op_automatic_simplify (OpMinus (substitute left simp_a t, substitute right simp_a t))
    | OpTimes (left, right) ->
      Op_simplifications.op_automatic_simplify (OpTimes (substitute left simp_a t, substitute right simp_a t))
    | OpDivide (left, right) ->
      Op_simplifications.op_automatic_simplify (OpDivide (substitute left simp_a t, substitute right simp_a t))
    | OpProduct expr_list ->
      Op_simplifications.op_automatic_simplify (OpProduct (List.map (fun x -> substitute x simp_a t) expr_list))
    | OpSum expr_list ->
      Op_simplifications.op_automatic_simplify (OpSum (List.map (fun x -> substitute x simp_a t) expr_list))
    | OpLog (b, expression) ->
      Op_simplifications.op_automatic_simplify (OpLog (b, substitute expression simp_a t))
    | OpPow (left, right) ->
      Op_simplifications.op_automatic_simplify (OpPow (substitute left simp_a t, substitute right simp_a t))
    | _ -> simp_expr)
  ;;


let partial_fraction_3 u v =
  let part_frac_result = partial_fraction_2 u v in
  let rec expand_sub expr = (* input to this function is in a form with only one polynomial in the denom *)
    (match expr with
    | OpSum sumList ->
      let test_list = OpSum (List.map expand_sub sumList) in 
      Op_simplifications.op_automatic_simplify test_list
    | OpProduct prodList ->
      let is_denom in_expr = 
        (match in_expr with
        | OpPow (base, OpRational exp) when (Mpq.cmp_si exp 0 1)<0 && Expr_simplifications.is_int exp ->
          true
        | _ ->
          false
        ) in
      let (denom, num) = List.partition (fun x -> is_denom x && contains_q x) prodList in
      let simp_num = Op_simplifications.op_automatic_simplify (OpProduct num) in
      let get_base_exp_of_denom denom = 
        (match denom with
        | OpPow (base, exp) ->
          (base, exp)
        | _ -> (OpUndefined, OpUndefined) (* should never get here *)
        ) in
      let (denom_base, denom_exp) = get_base_exp_of_denom (Op_simplifications.op_automatic_simplify (OpProduct denom)) in	(* denom will be a polynomial in q *)
      let new_num = polynomial_expansion simp_num denom_base (OpSymbolic_Constant "SPECIAL_INTERNAL_SYMBOL") in
      let new_expression = Op_simplifications.op_automatic_simplify (algebraic_expand (OpProduct [new_num; OpPow(OpSymbolic_Constant "SPECIAL_INTERNAL_SYMBOL", denom_exp)])) in
      substitute new_expression (OpSymbolic_Constant "SPECIAL_INTERNAL_SYMBOL") denom_base
    | _ -> expr
    ) in
  expand_sub part_frac_result
 ;;

(* input is a sum of rational expressions where all the denominators are factored*)
let rec partial_fraction expr =
  let simp_expr = Op_simplifications.op_automatic_simplify expr in
  match simp_expr with
  | OpSum sumList ->
    Op_simplifications.op_automatic_simplify (OpSum (List.map partial_fraction sumList))
  | OpProduct prodList ->
    let is_denom in_expr = 
      (match in_expr with
      | OpPow (base, OpRational exp) when (Mpq.cmp_si exp 0 1)<0 && Expr_simplifications.is_int exp ->
        true
      | _ ->
        false
      ) in
    let (denom, num) = List.partition is_denom prodList in (* might need to check if either list is empty *)
    let num_expr = Op_simplifications.op_automatic_simplify (OpProduct num) in
    let denom_expr = Op_simplifications.op_automatic_simplify (OpProduct denom) in
    let expanded_num = Op_simplifications.op_automatic_simplify (algebraic_expand (Op_simplifications.op_automatic_simplify num_expr)) in
    let factored_inverse_denom = Op_simplifications.op_automatic_simplify (OpPow(denom_expr, OpRational (Mpq.init_set_si (-1) 1))) in
    partial_fraction_3 expanded_num factored_inverse_denom
  | OpPow (base, OpRational exp) when (Mpq.cmp_si exp 0 1)<0 && Expr_simplifications.is_int exp ->
    let num = OpRational (Mpq.init_set_si 1 1) in
    let neg_exp = Mpq.init () in
    let _ = Mpq.neg neg_exp exp in
    partial_fraction_3 num (OpPow(base, OpRational neg_exp))
  | _ -> simp_expr
  ;;
