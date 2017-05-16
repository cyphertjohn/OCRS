open Type_def

exception Simplification_exception of string

let base expr = 
  match expr with
  | Pow (base, exp) ->
      base
  | Rational _ ->
      Undefined
  | _ ->
      expr
;;

let exponent expr = 
  match expr with
  | Pow (base, exp) ->
      exp
  | Rational _ ->
      Undefined
  | _ ->
      Rational (Mpq.init_set_si 1 1)
;;

let term expr = 
  match expr with
  | Product ((Rational rat) :: tail :: []) ->
      tail
  | Product ((Rational rat) :: rest) ->
      Product rest
  | Product lis ->
      Product lis
  | Rational _ ->
      Undefined
  | _ ->
      expr
;;

let const expr = 
  match expr with
  | Product ((Rational rat) :: rest) ->
      Rational rat
  | Rational _ ->
      Undefined
  | _ ->
      Rational (Mpq.init_set_si 1 1)
;;

let is_int rat =
  let test_int = Mpz.init () in
  let _ = Mpq.get_den test_int rat in
  if (Mpz.cmp_si test_int 1) = 0 then true
  else false
  ;;


let exp_by_squaring_int x n =
  let rec exp_by_squaring2 y x n =
    if (Mpq.cmp_si n 0 1)<0 then
      let x_inv = Mpq.init () in
      let neg_n = Mpq.init () in
      let _ = Mpq.inv x_inv x in
      let _ = Mpq.neg neg_n n in
      exp_by_squaring2 y x_inv neg_n
    else if (Mpq.cmp_si n 0 1) = 0 then y
    else if (Mpq.cmp_si n 1 1) = 0 then
      let res = Mpq.init () in
      let _ = Mpq.mul res x y in res
    else
      let n_div2 = Mpq.init () in
      let _ = Mpq.div_2exp n_div2 n 1 in
      if (is_int n_div2) then
        let x_sqr = Mpq.init () in
        let _ = Mpq.mul x_sqr x x in
        exp_by_squaring2 y x_sqr n_div2
      else
        let x_by_y = Mpq.init () in
        let x_sqr = Mpq.init () in
        let n_minus_1 = Mpq.init () in
        let n_minus_1_div2 = Mpq.init () in
        let _ = Mpq.mul x_by_y x y in
        let _ = Mpq.mul x_sqr x x in
        let _ = Mpq.sub n_minus_1 n (Mpq.init_set_si 1 1) in
        let _ = Mpq.div_2exp n_minus_1_div2 n_minus_1 1 in
        exp_by_squaring2 x_by_y x_sqr n_minus_1_div2 in
  exp_by_squaring2 (Mpq.init_set_si 1 1) x n
  ;;

let rec factorial_int n = 
    if (Mpq.cmp_si n 0 1)=0 then (Mpq.init_set_si 1 1)
    else
      let n_minus_1 = Mpq.init () in
      let _ = Mpq.sub n_minus_1 n (Mpq.init_set_si 1 1) in
      let res = factorial_int n_minus_1 in
      let ans = Mpq.init () in
      let _ = Mpq.mul ans res n in
      ans;;

let binomial x y =
  let num = factorial_int x in
  let temp = Mpq.init () in
  let y_fact = factorial_int y in
  let _ = Mpq.sub temp x y in
  let temp_fact = factorial_int temp in
  let _ = Mpq.mul temp_fact temp_fact y_fact in
  let _ = Mpq.div num num temp_fact in
  num;;

(* input list size is >= 2 *)
let rec simplify_sum_rec expr_list = 
  (*let _ = print_endline ("simplify_sum_rec " ^ (Expr_helpers.expr_to_string (Sum expr_list))) in
  *)match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (Sum p, Sum q) ->	(* SPRDREC-2-1 *)
          merge_sums p q
      | (Sum p, _) ->		(* SPRDREC-2-2 *)
          merge_sums p (u_2 :: [])
      | (_, Sum q) ->		(* SPRDREC-2-3 *)
          merge_sums (u_1 :: []) q
      | (Rational v_1, Rational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpq.init () in
          let _ = Mpq.add result v_1 v_2 in
          (if (Mpq.cmp_si result 0 1) = 0 then
              []	(* don't know if this is allowed *)
           else (Rational result) :: [] )
      | (Rational v_1, _) when (Mpq.cmp_si v_1 0 1) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, Rational v_2) when (Mpq.cmp_si v_2 0 1) = 0 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->
          let u_1_term = term u_1 in
          let u_1_const = const u_1 in
          let u_2_term = term u_2 in
          let u_2_const = const u_2 in
          if (expr_order u_1_term u_2_term = 0) then
              let s = simplify_sum (u_1_const :: u_2_const :: []) in (* SPRDREC-1-3 *)
              let p = simplify_product (s :: u_1_term :: []) in
              (match p with 
              | Rational rat when (Mpq.cmp_si rat 0 1) = 0 -> []
              | _ -> (p :: []))
          else	if (expr_order u_2 u_1) < 0 then u_2 :: u_1 :: []		(* SPRDREC-1-4 *)
              
          else expr_list					(* SPRDREC-1-5 *)
      )
  | u_1 :: rest ->
      let w = simplify_sum_rec rest in
      (match u_1 with
      | Sum p ->						(* SPRDREC-3-1 *)
          merge_sums p w
      | _ ->
          merge_sums (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | _ ->
      raise (Simplification_exception "Error in simplify_sum_rec")

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
           else raise (Simplification_exception "Error in merge_sums")
      )
and simplify_sum expr_list = 
  if (List.exists (fun el -> el = Undefined) expr_list) then
     Undefined
  else
     (match expr_list with
     | u_1 :: [] -> u_1		
     | _ ->
         let simp_list = simplify_sum_rec expr_list in 
         (match simp_list with 	
         | [] -> Rational (Mpq.init_set_si 0 1)
         | v_1 :: [] -> v_1
         | _ -> Sum simp_list
         )
      )
  
(* input list size is >= 2 *)
and simplify_product_rec expr_list = 
  (*let _ = print_endline ("simplify_product_rec " ^ (Expr_helpers.expr_to_string (Product expr_list))) in
  *)match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (Product p, Product q) ->	(* SPRDREC-2-1 *)
          merge_products p q
      | (Product p, _) ->		(* SPRDREC-2-2 *)
          merge_products p (u_2 :: [])
      | (_, Product q) ->		(* SPRDREC-2-3 *)
          merge_products (u_1 :: []) q
      | (Rational v_1, Rational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpq.init () in
          let _ = Mpq.mul result v_1 v_2 in
          (if (Mpq.cmp_si result 1 1) = 0 then
              []	(* don't know if this is allowed *)
           else (Rational result) :: [] )
      | (Rational v_1, _) when (Mpq.cmp_si v_1 1 1) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, Rational v_2) when (Mpq.cmp_si v_2 1 1) = 0 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->							(* SPRDREC-1-3 *)
          let u_1base = base u_1 in
          let u_1exp = exponent u_1 in
          let u_2base = base u_2 in
          let u_2exp = exponent u_2 in
          if (expr_order u_1base u_2base) = 0 then
              let s = simplify_sum (u_1exp :: u_2exp :: []) in 
              (match s with
              | Sum (a :: b :: []) when u_1exp = a && u_2exp = b || u_2exp =  a && u_1exp = b ->
                expr_list
              | _ ->
                let p = simplify_power u_1base s in
                (match p with 
                | Rational rat when (Mpq.cmp_si rat 1 1) = 0 -> []
                | _ -> (p :: [])))
          else if (expr_order u_2 u_1) < 0 then u_2 :: u_1 :: []	(* SPRDREC-1-4 *)
          else expr_list					(* SPRDREC-1-5 *)
      )
  | u_1 :: rest ->
      let w = simplify_product_rec rest in
      (match u_1 with
      | Product p ->						(* SPRDREC-3-1 *)
          merge_products p w
      | _ ->
          merge_products (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | [] ->
      (Rational (Mpq.init_set_si 1 1)) :: []
      (*raise (Simplification_exception "Error in simplify_product_rec")*)
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
           else raise (Simplification_exception "Error in merge_sums")
      )
      
and simplify_product expr_list = 
  if (List.exists (fun el -> el = Undefined) expr_list) then	(* SPRD-1 *)
     Undefined
  else if (List.exists (fun el -> (match el with
                                   | Rational value when (Mpq.cmp_si value 0 1) = 0->	(* SPRD-2 *)
                                       true
                                   | _ ->
                                       false)) expr_list) then Rational (Mpq.init_set_si 0 1)
  else
     (match expr_list with
     | u_1 :: [] -> u_1		(* SPRD-3 *)
     | _ ->
         let simp_list = simplify_product_rec expr_list in 
         (match simp_list with 	(* SPRD-4 *)
         | [] -> Rational (Mpq.init_set_si 1 1)
         | v_1 :: [] -> v_1
         | (Sum sum_lis) :: (Rational rat) :: [] | (Rational rat) :: (Sum sum_lis) :: [] ->
             let distributed_rat = List.map (fun x -> simplify_product [Rational rat; x]) sum_lis in
             simplify_sum distributed_rat
         | _ -> Product simp_list
         )
      )

(* input is expr and an Mpq.t int *)
and simplify_integer_power base n =
  match (base, n) with
  | (Rational v, _) ->	(* SINTPOW-1 *)      
      if (Mpq.cmp_si n 1000000 1) < 0 then Rational (exp_by_squaring_int v n)
      else Pow (base, Rational n)
      (*simplify_RNE (Pow (Float (float_of_int v)), Float n)*)      (* base is an int and exponent is an int float *)
  | (_, value) when (Mpq.cmp_si value 0 1) = 0 ->		(* SINTPOW-2 *)
      Rational (Mpq.init_set_si 1 1)
  | (_, value) when (Mpq.cmp_si value 1 1) = 0 ->		(* SINTPOW-3 *)
       base
  | (Pow (r, s), _) ->	(* SINTPOW-4 *)
      let p = simplify_product (s :: (Rational n) :: []) in
      (match p with
      | Rational p_int when is_int p_int ->
          simplify_integer_power r p_int
      | _ ->
          simplify_power r p
      )
  | (Times (left, right), _) ->				(*SINTPOW-5*)
      simplify_product ((simplify_integer_power left n) :: (simplify_integer_power right n) :: [])
  | (Product expr_list, _) ->				(*SINTPOW-5*)
      simplify_product (List.map (fun expr_list_elem -> (simplify_integer_power expr_list_elem n)) expr_list)
  | _ ->
      Pow (base, Rational n)

(* simplify Pow(base, exp) *)
and simplify_power base exp = 
  (*let _ = print_endline ("simplify_power " ^ (Expr_helpers.expr_to_string (Pow (base, exp)))) in
  *)match (base, exp) with
  | (Undefined, _) | (_, Undefined) ->			(* SPOW-1 *)
      Undefined
  | (Rational bas, exponent) when (Mpq.cmp_si bas 0 1) = 0 ->	(* SPOW-2 *)
      (match exponent with
      | Rational value when (Mpq.cmp_si value 0 1) > 0 ->
          Rational (Mpq.init_set_si 0 1)
      | _ ->
          Undefined
      )
  | (Rational value, _) when (Mpq.cmp_si value 1 1) = 0 ->	(* SPOW-3 *)
      Rational value
  | (_, Rational value) when is_int value ->	(* test value is an integer *)
      simplify_integer_power base value			(* SPOW-4 *)
  | (_, Sum sumList) ->
      let aux exponent = 
        simplify_power base exponent in
      simplify_product (List.map aux sumList)
  | (Rational rat_base, Product prodList) ->
      (*find Rationals and logarithms *)
      let exp_const = const exp in
      let exp_var = term exp in
      (match exp_const with
        | Rational rat when (Mpq.cmp_si rat 1 1) <> 0  && is_int rat ->
          simplify_power (Rational (exp_by_squaring_int rat_base rat)) exp_var
        | _ -> (*add functionality to look for logs *)
          Pow (base, exp)
      )
  | (Rational bas, Log (lbase, lexpr)) ->
      if (Mpq.equal bas lbase) then lexpr
      else
        Pow(lexpr, Log(lbase, Rational bas))
      (*let new_exp = Mpfr.init () in
      let numerator = Mpfr.init () in
      let denominator = Mpfr.init () in
      let _ = Mpfr.log numerator bas Mpfr.Near in
      let _ = Mpfr.log denominator lbase Mpfr.Near in
      let _ = Mpfr.div new_exp numerator denominator Mpfr.Near in
      if Mpfr.integer_p new_exp then simplify_power lexpr (Rational new_exp)
      else Pow (base, exp)*)
  | _ ->
      Pow (base, exp)					(* SPOW-5 *)
  ;;



let rec simplify_divide num denom = 
  match denom with
  | Rational rat when (Mpq.cmp_si rat 0 1) = 0 ->
      Undefined
  | _ ->
      simplify_product (num :: (simplify_power denom (Rational (Mpq.init_set_si (-1) 1))) :: [])
  ;;
  
let simplify_minus left right =
  simplify_sum (left :: (simplify_product ((Rational (Mpq.init_set_si (-1) 1)) :: right :: [])) :: [])
  ;;
  
  
let simplify_factorial expression = 
  match expression with
  | Rational rat when (Mpq.cmp_si rat 0 1) < 0 ->
      Undefined
  | Rational rat when is_int rat ->
      Rational (factorial_int rat)
  | _ ->
      Factorial expression
  ;;
  
  

let simplify_binom top bottom = 
  match (top, bottom) with
  | (_, Rational rat) when (Mpq.cmp_si rat 0 1)=0 ->
    Rational (Mpq.init_set_si 1 1)		(*might need a stronger condition *)
  | (_, Rational rat) when (Mpq.cmp_si rat 1 1)=0 ->
    top
  | (Rational ratTop, Rational ratBot) when (Mpq.cmp ratTop ratBot)<0 ->
    Rational (Mpq.init_set_si 0 1)
  | (Rational ratTop, Rational ratBot) when (Mpq.cmp_si ratTop 0 1)>0 && (Mpq.cmp_si ratBot 0 1)>0 && is_int ratTop && is_int ratBot ->
    Rational (binomial ratTop ratBot)
  | _ -> Binomial (top, bottom)
  ;;
  
(** Automatically simplify an expression bottom up *)
let rec automatic_simplify expr = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case (_, _) | Output_variable (_, _) | Input_variable _ | Undefined | Pi | Arctan _ ->
     expr
  | Pow (base, exponent) ->
      let simplified_base = automatic_simplify base in
      let simplified_exp = automatic_simplify exponent in
          simplify_power simplified_base simplified_exp
  | Times (left, right) ->
      let simplified_right = automatic_simplify right in
      let simplified_left = automatic_simplify left in
          simplify_product (simplified_left :: simplified_right :: [])		(* simplify product expects a list as input *)
  | Product prod_list ->
      simplify_product (List.map automatic_simplify prod_list)
  | Plus (left, right) ->
      let simplified_right = automatic_simplify right in
      let simplified_left = automatic_simplify left in
          simplify_sum (simplified_left :: simplified_right :: [])		(* simplify sum expects a list as input *)
  | Sum sum_list ->
      simplify_sum (List.map automatic_simplify sum_list)
  | Divide (num, denom) ->
      let simplified_num = automatic_simplify num in
      let simplified_denom = automatic_simplify denom in
          simplify_divide simplified_num simplified_denom
  | Minus (left, right) ->
      let simplified_left = automatic_simplify left in
      let simplified_right = automatic_simplify right in
          simplify_minus simplified_left simplified_right
  | Log (base, expression) ->
      simplify_log base (automatic_simplify expression)
  | Binomial (top, bottom) ->
      let simplified_top = automatic_simplify top in
      let simplified_bottom = automatic_simplify bottom in
          simplify_binom simplified_top simplified_bottom
  | Factorial expression ->
      simplify_factorial (automatic_simplify expression)
  | IDivide _ -> (* update this later *)
      expr
  | Sin _ ->
      expr
  | Cos _ ->
      expr
  | Mod _ ->
      expr

and simplify_log base expression = 
  match expression with
  | Rational rat when (Mpq.cmp_si rat 0 1) <= 0 ->
      Undefined
  | Rational rat when Mpq.equal rat base ->
      Rational (Mpq.init_set_si 1 1)
  | Product prodList ->
      automatic_simplify (Sum (List.map (fun x -> (Log (base, x))) prodList))
  | Pow (exp_base, exponent) ->
      automatic_simplify (Product[exponent; (simplify_log base exp_base)])
  | _ ->
      Log (base, expression)
  ;;

let automatic_simplify_inequation inequation = 
  match inequation with
  | Equals (left, right) ->
      Equals (automatic_simplify left, automatic_simplify right)
  | GreaterEq (left, right) ->
      GreaterEq (automatic_simplify left, automatic_simplify right)
  | Greater (left, right) ->
      Greater (automatic_simplify left, automatic_simplify right)
  | LessEq (left, right) ->
      LessEq (automatic_simplify left, automatic_simplify right)
  | Less (left, right) ->
      Less (automatic_simplify left, automatic_simplify right)
  ;;
  
  
