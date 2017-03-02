open Type_def

exception Op_simplifications_exc of string

let base expr = 
  match expr with
  | OpPow (base, exp) ->
      base
  | OpRational _ ->
      OpUndefined
  | _ ->
      expr
;;

let exponent expr = 
  match expr with
  | OpPow (base, exp) ->
      exp
  | OpRational _ ->
      OpUndefined
  | _ ->
      OpRational (Mpq.init_set_si 1 1)
;;

let term expr = 
  match expr with
  | OpProduct ((OpRational rat) :: tail :: []) ->
      tail
  | OpProduct ((OpRational rat) :: rest) ->
      OpProduct rest
  | OpProduct lis ->
      OpProduct lis
  | OpRational _ ->
      OpUndefined
  | _ ->
      expr
;;

let const expr = 
  match expr with
  | OpProduct ((OpRational rat) :: rest) ->
      OpRational rat
  | OpRational _ ->
      OpUndefined
  | _ ->
      OpRational (Mpq.init_set_si 1 1)
;;


(* input list size is >= 2 *)
let rec simplify_sum_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (OpSum p, OpSum q) ->	(* SPRDREC-2-1 *)
          merge_sums p q
      | (OpSum p, _) ->		(* SPRDREC-2-2 *)
          merge_sums p (u_2 :: [])
      | (_, OpSum q) ->		(* SPRDREC-2-3 *)
          merge_sums (u_1 :: []) q
      | (OpRational v_1, OpRational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpq.init () in
          let _ = Mpq.add result v_1 v_2 in
          (if (Mpq.cmp_si result 0 1) = 0 then
              []	(* don't know if this is allowed *)
           else (OpRational result) :: [] )
      | (OpRational v_1, _) when (Mpq.cmp_si v_1 0 1) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, OpRational v_2) when (Mpq.cmp_si v_2 0 1) = 0 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->
          let u_1_term = term u_1 in
          let u_1_const = const u_1 in
          let u_2_term = term u_2 in
          let u_2_const = const u_2 in
          if (op_expr_order u_1_term u_2_term = 0) then
              let s = simplify_sum (u_1_const :: u_2_const :: []) in (* SPRDREC-1-3 *)
              let p = simplify_product (s :: u_1_term :: []) in
              (match p with 
              | OpRational rat when (Mpq.cmp_si rat 0 1) = 0 -> []
              | _ -> (p :: []))
          else	if (op_expr_order u_2 u_1) < 0 then u_2 :: u_1 :: []		(* SPRDREC-1-4 *)
              
          else expr_list					(* SPRDREC-1-5 *)
      )
  | u_1 :: rest ->
      let w = simplify_sum_rec rest in
      (match u_1 with
      | OpSum p ->						(* SPRDREC-3-1 *)
          merge_sums p w
      | _ ->
          merge_sums (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | [] -> []

and merge_sums p q = 
  match (p, q) with
  | (_, []) -> p	(* MRSM-1 *)
  | ([], _) -> q	(* MRSM-2 *)
  | (p1 :: rest_p, q1 :: rest_q) ->
      let h = simplify_sum_rec (p1 :: q1 :: []) in
      (match h with
      | [] -> merge_sums rest_p rest_q	(* MRSM-3-1 *)
      | h1 :: [] -> h1 :: (merge_sums rest_p rest_q)	(* MRSM-3-2 *)
      | _ ->
           if h = (p1 :: q1 :: []) then List.append (p1 :: []) (merge_sums rest_p q)	(* MRSM-3-3 *)
           else if h = (q1 :: p1 :: []) then List.append (q1 :: []) (merge_sums p rest_q)	(* MRSM-3-4 *)
           else raise (Op_simplifications_exc "Error in merge_sums")
           )
and simplify_sum expr_list = 
  if (List.exists (fun el -> el = OpUndefined) expr_list) then
     OpUndefined
  else
     (match expr_list with
     | u_1 :: [] -> u_1		
     | _ ->
         let simp_list = simplify_sum_rec expr_list in 
         (match simp_list with 	
         | [] -> OpRational (Mpq.init_set_si 0 1)
         | v_1 :: [] -> v_1
         | _ -> OpSum simp_list
         )
      )
  
(* input list size is >= 2 *)
and simplify_product_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (OpProduct p, OpProduct q) ->	(* SPRDREC-2-1 *)
          merge_products p q
      | (OpProduct p, _) ->		(* SPRDREC-2-2 *)
          merge_products p (u_2 :: [])
      | (_, OpProduct q) ->		(* SPRDREC-2-3 *)
          merge_products (u_1 :: []) q
      | (OpRational v_1, OpRational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpq.init () in
          let _ = Mpq.mul result v_1 v_2 in
          (if (Mpq.cmp_si result 1 1) = 0 then
              []	(* don't know if this is allowed *)
           else (OpRational result) :: [] )
      | (OpRational v_1, _) when (Mpq.cmp_si v_1 1 1) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, OpRational v_2) when (Mpq.cmp_si v_2 1 1) = 0 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->							(* SPRDREC-1-3 *)
          let u_1base = base u_1 in
          let u_1exp = exponent u_1 in
          let u_2base = base u_2 in
          let u_2exp = exponent u_2 in
          if (op_expr_order u_1base u_2base) = 0 then
              let s = simplify_sum (u_1exp :: u_2exp :: []) in 
              let p = simplify_power u_1base s in
              (match p with 
              | OpRational rat when (Mpq.cmp_si rat 1 1) = 0 -> []
              | _ -> (p :: []))
          else if (op_expr_order u_2 u_1) < 0 then u_2 :: u_1 :: []	(* SPRDREC-1-4 *)
          else expr_list					(* SPRDREC-1-5 *)
      )
  | u_1 :: rest ->
      let w = simplify_product_rec rest in
      (match u_1 with
      | OpProduct p ->						(* SPRDREC-3-1 *)
          merge_products p w
      | _ ->
          merge_products (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | [] -> []
and merge_products p q = 
  match (p, q) with
  | (_, []) -> p	(* MRPD-1 *)
  | ([], _) -> q	(* MRPD-2 *)
  | (p1 :: rest_p, q1 :: rest_q) ->
      let h = simplify_product_rec (p1 :: q1 :: []) in
      (match h with
      | [] -> merge_products rest_p rest_q	(* MRPD-3-1 *)
      | h1 :: [] -> h1 :: (merge_products rest_p rest_q)	(* MRPD-3-2 *)
      | _ ->
           if h = (p1 :: q1 :: []) then List.append (p1 :: []) (merge_products rest_p q)	(* MRPD-3-3 *)
           else if h = (q1 :: p1 :: []) then List.append (q1 :: []) (merge_products p rest_q)	(* MRPD-3-4 *)
           else raise (Op_simplifications_exc "Error in merge_products")
      )
      
and simplify_product expr_list = 
  if (List.exists (fun el -> el = OpUndefined) expr_list) then	(* SPRD-1 *)
     OpUndefined
  else if (List.exists (fun el -> (match el with
                                   | OpRational value when (Mpq.cmp_si value 0 1) = 0->	(* SPRD-2 *)
                                       true
                                   | _ ->
                                       false)) expr_list) then OpRational (Mpq.init_set_si 0 1)
  else
     (match expr_list with
     | u_1 :: [] -> u_1		(* SPRD-3 *)
     | _ ->
         let simp_list = simplify_product_rec expr_list in 
         (match simp_list with 	(* SPRD-4 *)
         | [] -> OpRational (Mpq.init_set_si 1 1)
         | v_1 :: [] -> v_1
         | (OpSum sum_lis) :: (OpRational rat) :: [] | (OpRational rat) :: (OpSum sum_lis) :: [] ->
             let distributed_rat = List.map (fun x -> simplify_product [OpRational rat; x]) sum_lis in
             simplify_sum distributed_rat
         | _ -> OpProduct simp_list
         )
      )

(* input is expr and an Mpfr.t int *)
and simplify_integer_power base n =
  match (base, n) with
  | (OpRational v, _) ->	(* SINTPOW-1 *)
      if (Mpq.cmp_si n 1000000 1) < 0 then OpRational (Expr_simplifications.exp_by_squaring_int v n)
      else OpPow (base, OpRational n)
      (*simplify_RNE (OpPow (Float (float_of_int v)), Float n)*)      (* base is an int and exponent is an int float *)
  | (_, value) when (Mpq.cmp_si value 0 1) = 0 ->		(* SINTPOW-2 *)
      OpRational (Mpq.init_set_si 1 1)
  | (_, value) when (Mpq.cmp_si value 1 1) = 0 ->		(* SINTPOW-3 *)
       base
  | (OpPow (r, s), _) ->	(* SINTPOW-4 *)
      let p = simplify_product (s :: (OpRational n) :: []) in
      (match p with
      | OpRational p_int when Expr_simplifications.is_int p_int ->
          simplify_integer_power r p_int
      | _ ->
          OpPow (r, p)
      )
  | (OpTimes (left, right), _) ->				(*SINTPOW-5*)
      simplify_product ((simplify_integer_power left n) :: (simplify_integer_power right n) :: [])
  | (OpProduct expr_list, _) ->				(*SINTPOW-5*)
      simplify_product (List.map (fun expr_list_elem -> (simplify_integer_power expr_list_elem n)) expr_list)
  | _ ->
      OpPow (base, OpRational n)

(* simplify OpPow(base, exp) *)
and simplify_power base exp = 
  match (base, exp) with
  | (OpUndefined, _) | (_, OpUndefined) ->			(* SPOW-1 *)
      OpUndefined
  | (OpRational bas, exponent) when (Mpq.cmp_si bas 0 1) = 0 ->	(* SPOW-2 *)
      (match exponent with
      | OpRational value when (Mpq.cmp_si value 0 1) > 0 ->
          OpRational (Mpq.init_set_si 0 1)
      | _ ->
          OpUndefined
      )
  | (OpRational value, _) when (Mpq.cmp_si value 1 1) = 0 ->	(* SPOW-3 *)
      OpRational value
  | (_, OpRational value) when Expr_simplifications.is_int value ->	(* test value is an integer *)
      simplify_integer_power base value			(* SPOW-4 *)
  | _ ->
      OpPow (base, exp)					(* SPOW-5 *)
  ;;



let rec simplify_divide num denom = 
  match denom with
  | OpRational rat when (Mpq.cmp_si rat 0 1) = 0 ->
      OpUndefined
  | _ ->
      simplify_product (num :: (simplify_power denom (OpRational (Mpq.init_set_si (-1) 1))) :: [])
  ;;
  
let simplify_minus left right =
  simplify_sum (left :: (simplify_product ((OpRational (Mpq.init_set_si (-1) 1)) :: right :: [])) :: [])
  ;;
  
let simplify_log expression = 
  match expression with
  | OpRational rat when (Mpq.cmp_si rat 0 1) <= 0 ->
      OpUndefined
  (*| OpRational rat ->
      let result = Mpfr.init () in
      let _ = Mpfr.log2 result rat Mpfr.Near in
      OpRational result*)
  | _ ->
      OpLog expression
  ;;
  
  
  
(** Automatically simplify an expression bottom up *)
let rec op_automatic_simplify expr = 
  match expr with
  | OpRational _ | OpSymbolic_Constant _ | OpBase_case (_, _) | OpOutput_variable (_, _) | OpInput_variable _ | OpUndefined | Q ->
     expr
  | OpPow (base, exponent) ->
      let simplified_base = op_automatic_simplify base in
      let simplified_exp = op_automatic_simplify exponent in
          simplify_power simplified_base simplified_exp
  | OpTimes (left, right) ->
      let simplified_right = op_automatic_simplify right in
      let simplified_left = op_automatic_simplify left in
          simplify_product (simplified_left :: simplified_right :: [])		(* simplify product expects a list as input *)
  | OpProduct prod_list ->
      simplify_product (List.map op_automatic_simplify prod_list)
  | OpPlus (left, right) ->
      let simplified_right = op_automatic_simplify right in
      let simplified_left = op_automatic_simplify left in
          simplify_sum (simplified_left :: simplified_right :: [])		(* simplify sum expects a list as input *)
  | OpSum sum_list ->
      simplify_sum (List.map op_automatic_simplify sum_list)
  | OpDivide (num, denom) ->
      let simplified_num = op_automatic_simplify num in
      let simplified_denom = op_automatic_simplify denom in
          simplify_divide simplified_num simplified_denom
  | OpMinus (left, right) ->
      let simplified_left = op_automatic_simplify left in
      let simplified_right = op_automatic_simplify right in
          simplify_minus simplified_left simplified_right
  | OpLog expression ->
      simplify_log (op_automatic_simplify expression)
  ;;

let op_automatic_simplify_inequation inequation = 
  match inequation with
  | OpEquals (left, right) ->
      OpEquals (op_automatic_simplify left, op_automatic_simplify right)
  | OpGreaterEq (left, right) ->
      OpGreaterEq (op_automatic_simplify left, op_automatic_simplify right)
  | OpGreater (left, right) ->
      OpGreater (op_automatic_simplify left, op_automatic_simplify right)
  | OpLessEq (left, right) ->
      OpLessEq (op_automatic_simplify left, op_automatic_simplify right)
  | OpLess (left, right) ->
      OpLess (op_automatic_simplify left, op_automatic_simplify right)
  ;;
