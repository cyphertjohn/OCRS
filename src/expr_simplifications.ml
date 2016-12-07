open Type_def

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
      Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))
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
      Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))
;;


(* input list size is >= 2 *)
let rec simplify_sum_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (Sum p, Sum q) ->	(* SPRDREC-2-1 *)
          merge_sums p q
      | (Sum p, _) ->		(* SPRDREC-2-2 *)
          merge_sums p (u_2 :: [])
      | (_, Sum q) ->		(* SPRDREC-2-3 *)
          merge_sums (u_1 :: []) q
      | (Rational v_1, Rational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpfr.init () in
          let _ = Mpfr.add result v_1 v_2 Mpfr.Near in
          (if (Mpfr.cmp_si result 0) = 0 then
              []	(* don't know if this is allowed *)
           else (Rational result) :: [] )
      | (Rational v_1, _) when (Mpfr.cmp_si v_1 0) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, Rational v_2) when (Mpfr.cmp_si v_2 0) = 0 ->	(* SPRDREC-1-2-b *)
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
              | Rational rat when (Mpfr.cmp_si rat 0) = 0 -> []
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
      failwith "An Error has occured in simplify_product_rec"

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
           else failwith "Everything should be convered by the above cases"
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
         | [] -> Rational (snd (Mpfr.init_set_si 0 Mpfr.Near))
         | v_1 :: [] -> v_1
         | _ -> Sum simp_list
         )
      )
  
(* input list size is >= 2 *)
and simplify_product_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (Product p, Product q) ->	(* SPRDREC-2-1 *)
          merge_products p q
      | (Product p, _) ->		(* SPRDREC-2-2 *)
          merge_products p (u_2 :: [])
      | (_, Product q) ->		(* SPRDREC-2-3 *)
          merge_products (u_1 :: []) q
      | (Rational v_1, Rational v_2) ->	(* SPRDREC-1-1 *)
          let result = Mpfr.init () in
          let _ = Mpfr.mul result v_1 v_2 Mpfr.Near in
          (if (Mpfr.cmp_si result 1) = 0 then
              []	(* don't know if this is allowed *)
           else (Rational result) :: [] )
      | (Rational v_1, _) when (Mpfr.cmp_si v_1 1) = 0 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, Rational v_2) when (Mpfr.cmp_si v_2 1) = 0 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->							(* SPRDREC-1-3 *)
          let u_1base = base u_1 in
          let u_1exp = exponent u_1 in
          let u_2base = base u_2 in
          let u_2exp = exponent u_2 in
          if (expr_order u_1base u_2base) = 0 then
              let s = simplify_sum (u_1exp :: u_2exp :: []) in 
              let p = simplify_power u_1base s in
              (match p with 
              | Rational rat when (Mpfr.cmp_si rat 1) = 0 -> []
              | _ -> (p :: []))
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
  | _ ->
      failwith "An Error has occured in simplify_product_rec"
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
           else failwith "Everything should be convered by the above cases"
      )
      
and simplify_product expr_list = 
  if (List.exists (fun el -> el = Undefined) expr_list) then	(* SPRD-1 *)
     Undefined
  else if (List.exists (fun el -> (match el with
                                   | Rational value when (Mpfr.cmp_si value 0) = 0->	(* SPRD-2 *)
                                       true
                                   | _ ->
                                       false)) expr_list) then Rational (snd (Mpfr.init_set_si 0 Mpfr.Near))
  else
     (match expr_list with
     | u_1 :: [] -> u_1		(* SPRD-3 *)
     | _ ->
         let simp_list = simplify_product_rec expr_list in 
         (match simp_list with 	(* SPRD-4 *)
         | [] -> Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))
         | v_1 :: [] -> v_1
         | (Sum sum_lis) :: (Rational rat) :: [] | (Rational rat) :: (Sum sum_lis) :: [] ->
             let distributed_rat = List.map (fun x -> simplify_product [Rational rat; x]) sum_lis in
             simplify_sum distributed_rat
         | _ -> Product simp_list
         )
      )

(* input is expr and an Mpfr.t int *)
and simplify_integer_power base n =
  match (base, n) with
  | (Rational v, _) ->	(* SINTPOW-1 *)
      let result = Mpfr.init () in
      let _ = Mpfr.pow result v n Mpfr.Near in
      Rational result
      (*simplify_RNE (Pow (Float (float_of_int v)), Float n)*)      (* base is an int and exponent is an int float *)
  | (_, value) when (Mpfr.cmp_si value 0) = 0 ->		(* SINTPOW-2 *)
      Rational (snd (Mpfr.init_set_si 1 Mpfr.Near))
  | (_, value) when (Mpfr.cmp_si value 1) = 0 ->		(* SINTPOW-3 *)
       base
  | (Pow (r, s), _) ->	(* SINTPOW-4 *)
      let p = simplify_product (s :: (Rational n) :: []) in
      (match p with
      | Rational p_int when Mpfr.integer_p p_int ->
          simplify_integer_power r p_int
      | _ ->
          Pow (r, p)
      )
  | (Times (left, right), _) ->				(*SINTPOW-5*)
      simplify_product ((simplify_integer_power left n) :: (simplify_integer_power right n) :: [])
  | (Product expr_list, _) ->				(*SINTPOW-5*)
      simplify_product (List.map (fun expr_list_elem -> (simplify_integer_power expr_list_elem n)) expr_list)
  | _ ->
      Pow (base, Rational n)

(* simplify Pow(base, exp) *)
and simplify_power base exp = 
  match (base, exp) with
  | (Undefined, _) | (_, Undefined) ->			(* SPOW-1 *)
      Undefined
  | (Rational bas, exponent) when (Mpfr.cmp_si bas 0) = 0 ->	(* SPOW-2 *)
      (match exponent with
      | Rational value when (Mpfr.cmp_si value 0) > 0 ->
          Rational (snd (Mpfr.init_set_si 0 Mpfr.Near))
      | _ ->
          Undefined
      )
  | (Rational value, _) when (Mpfr.cmp_si value 1) = 0 ->	(* SPOW-3 *)
      Rational value
  | (_, Rational value) when (Mpfr.integer_p value) ->	(* test value is an integer *)
      simplify_integer_power base value			(* SPOW-4 *)
  | _ ->
      Pow (base, exp)					(* SPOW-5 *)
  ;;



let rec simplify_divide num denom = 
  match denom with
  | Rational rat when (Mpfr.cmp_si rat 0) = 0 ->
      Undefined
  | _ ->
      simplify_product (num :: (simplify_power denom (Rational (snd (Mpfr.init_set_si (-1) Mpfr.Near)))) :: [])
  ;;
  
let simplify_minus left right =
  simplify_sum (left :: (simplify_product ((Rational (snd (Mpfr.init_set_si (-1) Mpfr.Near))) :: right :: [])) :: [])
  ;;
  
let simplify_log expression = 
  match expression with
  | Rational rat when (Mpfr.cmp_si rat 0) <= 0 ->
      Undefined
  | Rational rat ->
      let result = Mpfr.init () in
      let _ = Mpfr.log2 result rat Mpfr.Near in
      Rational result
  | _ ->
      Log expression
  ;;
  
let simplify_factorial expression = 
  match expression with
  | Rational rat when (Mpfr.cmp_si rat 0) < 0 ->
      Undefined
  | Rational rat ->
      let result = Mpfr.init () in
      let _ = Mpfr.add_ui result rat 1 Mpfr.Near in
      let _ = Mpfr.gamma result result Mpfr.Near in
      Rational result
  | _ ->
      Factorial expression
  ;;
  
  

let simplify_binom top bottom = 
  match (top, bottom) with
  | (_, Rational rat) when (Mpfr.cmp_si rat 0)=0 ->
    Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))		(*might need a stronger condition *)
  | (_, Rational rat) when (Mpfr.cmp_si rat 1)=0 ->
    top
  | (Rational ratTop, Rational ratBot) when (Mpfr.cmp ratTop ratBot)<0 ->
    Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))
  | (Rational ratTop, Rational ratBot) when (Mpfr.cmp_si ratTop 0)>0 && (Mpfr.cmp_si ratBot 0)>0 && (Mpfr.integer_p ratTop) && (Mpfr.integer_p ratBot) ->
    let binomial x y = 
      let x_minus_y = Mpfr.init () in
      let result = Mpfr.init () in
      let y_temp = Mpfr.init () in
      let _ = Mpfr.sub x_minus_y x y Mpfr.Near in (* x_minus_y = x-y *)
      let _ = Mpfr.add_ui result x 1 Mpfr.Near in (* x = x+1 *)
      let _ = Mpfr.add_ui y_temp y 1 Mpfr.Near in (* y = y+1 *)
      let _ = Mpfr.add_ui x_minus_y x_minus_y 1 Mpfr.Near in
      let _ = Mpfr.gamma result result Mpfr.Near in (* x = x! *)
      let _ = Mpfr.gamma y_temp y_temp Mpfr.Near in (* y = y! *)
      let _ = Mpfr.gamma x_minus_y x_minus_y Mpfr.Near in (* x_minus_y = x_minus_y! *)
      let _ = Mpfr.mul y_temp y_temp x_minus_y Mpfr.Near in (* y = y * x_minus_y *)
      let _ = Mpfr.div result result y_temp Mpfr.Near in (* x = x/y *) result
    in Rational (binomial ratTop ratBot)
  | _ -> Binomial (top, bottom)
  ;;
  
(** Automatically simplify an expression bottom up *)
let rec automatic_simplify expr = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case (_, _) | Output_variable (_, _) | Input_variable _ | Undefined ->
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
  | Log expression ->
      simplify_log (automatic_simplify expression)
  | Binomial (top, bottom) ->
      let simplified_top = automatic_simplify top in
      let simplified_bottom = automatic_simplify bottom in
          simplify_binom simplified_top simplified_bottom
  | Factorial expression ->
      simplify_factorial (automatic_simplify expression)
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
  
  
