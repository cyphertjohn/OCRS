open Type_def
open Expr_simplifications

exception Expr_transform_exc of string

let rec expand_product r s = 
  match (r, s) with
  | (Sum sumList, _)->
    (match sumList with
    | [] -> raise (Expr_transform_exc "Sum operand list was empty")
    | hd :: [] -> expand_product hd s
    | hd :: tail -> automatic_simplify (Sum [expand_product hd s; expand_product (Sum tail) s]))
  | (_, Sum _) -> expand_product s r
  | _ -> automatic_simplify (Product [r; s])
  ;;

let rec expand_power u n =
  match u with
  | Sum sumList ->
    (match sumList with
    | [] -> raise (Expr_transform_exc "Sum operand list was empty")
    | hd :: [] -> expand_power hd n
    | f :: tail ->
      let r = Sum tail in
      let zero = Mpq.init_set_si 0 1 in
      let rec aux acc k = 
        if (Mpq.cmp k n) > 0 then Sum acc
        else
          let c = Expr_simplifications.binomial n k in
          let n_minus_k = Mpq.init () in
          let k_plus1 = Mpq.init () in
          let _ = Mpq.add k_plus1 k (Mpq.init_set_si 1 1) in
          let _ = Mpq.sub n_minus_k n k in
          aux (acc @ [(expand_product (Product [Rational c; Pow(f, (Rational n_minus_k))]) (expand_power r k))]) k_plus1 in
      automatic_simplify (aux [(Rational zero)] zero))
  | _ -> Pow (u, Rational n)
  ;;
  
  
  
let rec algebraic_expand expr = 
  match expr with
  | Sum sumList ->
    (match sumList with
    | [] -> raise (Expr_transform_exc "Sum operand list was empty")
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> automatic_simplify (Sum [algebraic_expand hd; algebraic_expand (Sum tail)]))
  | Product prodList ->
    (match prodList with
    | [] -> raise (Expr_transform_exc "Product operand list was empty")
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> automatic_simplify (expand_product (algebraic_expand hd) (algebraic_expand (Product tail))))
  | Pow (base, exp) ->
    (match exp with
    | Rational rat when Expr_simplifications.is_int rat && (Mpq.cmp_si rat 2 1) >= 0 ->
      automatic_simplify (expand_power (algebraic_expand base) rat)
    | _ -> Pow (base, exp))
  | _ -> expr
  ;;

let rec algebraic_expand_inequation ineq = 
  match ineq with
  | Equals(left, right) -> Equals(algebraic_expand left, algebraic_expand right)	(* temporary solution *)
  | Greater(left, right) -> Greater(algebraic_expand left, algebraic_expand right)
  | GreaterEq(left, right) -> GreaterEq(algebraic_expand left, algebraic_expand right)
  | Less(left, right) -> Less(algebraic_expand left, algebraic_expand right)
  | LessEq(left, right) -> LessEq(algebraic_expand left, algebraic_expand right)
  ;;

let rec inverse_binomial expr =
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case (_, _) | Output_variable (_, _) | Input_variable _ | Arctan _ | Pi | Undefined | Iif _ ->
     expr
  | Pow (base, exponent) ->
      automatic_simplify (Pow (inverse_binomial base, inverse_binomial exponent))
  | Times (left, right) ->
      automatic_simplify (Times (inverse_binomial left, inverse_binomial right))
  | Product prod_list ->
      automatic_simplify (Product (List.map inverse_binomial prod_list))
  | Plus (left, right) ->
      automatic_simplify (Plus (inverse_binomial left, inverse_binomial right))
  | Sum sum_list ->
      automatic_simplify (Sum (List.map inverse_binomial sum_list))
  | Divide (num, denom) ->
      automatic_simplify (Divide (inverse_binomial num, inverse_binomial denom))
  | Minus (left, right) ->
      automatic_simplify (Minus (inverse_binomial left, inverse_binomial right))
  | Log (base, expression) ->
      automatic_simplify (Log (base, (inverse_binomial expression)))
  | Binomial (top, bottom) ->
      (match (top, bottom) with
      | (_, Rational rat) when (Mpq.cmp_si rat 0 1)=0 ->
        Rational (Mpq.init_set_si 1 1)            (*might need a stronger condition *)
      | (_, Rational rat) when (Mpq.cmp_si rat 1 1)=0 ->
        top
      | (Rational ratTop, Rational ratBot) when (Mpq.cmp ratTop ratBot)<0 ->
        Rational (Mpq.init_set_si 0 1)
      | (Rational ratTop, Rational ratBot) when (Mpq.cmp_si ratTop 0 1)>0 && (Mpq.cmp_si ratBot 0 1)>0 && Expr_simplifications.is_int ratTop && Expr_simplifications.is_int ratBot ->
        Rational (binomial ratTop ratBot)
      | (Input_variable str, Rational rat) when (Mpq.cmp_si rat 0 1)>0 && Expr_simplifications.is_int rat ->
        let rat_minus_1 = Mpq.init () in
        let _ = Mpq.sub rat_minus_1 rat (Mpq.init_set_si 1 1) in
        let new_denom = Expr_simplifications.factorial_int rat in
        let rec build_list acc k =
          if (Mpq.cmp k rat_minus_1)>0 then acc
          else
            let k_plus_1 = Mpq.init() in
            let _ = Mpq.add k_plus_1 k (Mpq.init_set_si 1 1) in
            build_list (acc @ [Minus(Input_variable str, Rational k)]) k_plus_1 in
        algebraic_expand (automatic_simplify (Divide(Product (build_list [] (Mpq.init_set_si 0 1)), Rational new_denom)))
      | _ -> Binomial (top, bottom))
  | IDivide (numerator, denom) ->
      IDivide (inverse_binomial numerator, denom)
  | Sin inner_expr ->
      Sin (inverse_binomial inner_expr)
  | Cos inner_expr ->
      Cos (inverse_binomial inner_expr)
  | Mod (left, right) ->
      Mod (inverse_binomial left, inverse_binomial right)
  | Factorial expression ->
      automatic_simplify (Factorial (inverse_binomial expression))
  ;;

let inverse_binomial_ineq ineq = 
  match ineq with
  | Equals(left, right) -> Equals(inverse_binomial left, inverse_binomial right)	(* temporary solution *)
  | Greater(left, right) -> Greater(inverse_binomial left, inverse_binomial right)
  | GreaterEq(left, right) -> GreaterEq(inverse_binomial left, inverse_binomial right)
  | Less(left, right) -> Less(inverse_binomial left, inverse_binomial right)
  | LessEq(left, right) -> LessEq(inverse_binomial left, inverse_binomial right)
  ;;



(*

This section might be useful if trying to identify and factor out arbitrary linear terms

let rec get_gcd_of_linear_terms term_list = 
  let rational_list = List.map (fun x -> 
                                    (match x with
                                    | Product ((Rational rat) :: tail) -> Rational rat
                                    | _ -> Rational (snd(Mpfr.init_set_si 1 Mpfr.Near)))) term_list in
  let list_with_out_rational = 
  ;;

*)

(*
let rec contains_x expr x =
  if expr = x then true
  else
    (match expr with
    | Plus (left, right) ->
      (contains_x left x) || (contains_x right x)
    | Minus (left, right) ->
      (contains_x left x) || (contains_x right x)
    | Times (left, right) ->
      (contains_x left x) || (contains_x right x)
    | Divide (left, right) ->
      (contains_x left x) || (contains_x right x)
    | Product expr_list ->
      List.exists (fun y -> contains_x y x) expr_list
    | Sum expr_list ->
      List.exists (fun y -> contains_x y x) expr_list
    | Factorial expression ->
      contains_x expression x
    | Log (_, expression) ->
      contains_x expression x
    | Pow (left, right) ->
      (contains_x left x) || (contains_x right x)
    | Binomial (left, right) ->
      (contains_x left x) || (contains_x right x)
    | _ -> false)
  ;;


let rec degree_monomial u x =
  if u=x then (Rational (snd(Mpfr.init_set_si 1 Mpfr.Near)), snd(Mpfr.init_set_si 1 Mpfr.Near))
  else
    (match u with
    | Pow(x, Rational rat) when (Mpfr.cmp_si rat 1)>0 ->
      (Rational (snd(Mpfr.init_set_si 1 Mpfr.Near)), rat)
    | Product prodList ->
      let coef_deg_list = List.map (fun y -> degree_monomial y x) prodList in
      if List.exists (fun x -> (fst x) = Undefined) coef_deg_list then (Undefined, snd(Mpfr.init_set_si 0 Mpfr.Near))
      else
        let max a b =
          let a_deg = snd a in
          let b_deg = snd b in
          let cmp_result = Mpfr.cmp a_deg b_deg in
          if cmp_result < 0 then b
          else a in
        let m = List.fold_left max (Symbolic_Constant "y", snd(Mpfr.init_set_si (-1) Mpfr.Near)) coef_deg_list in
        (Expr_simplifications.automatic_simplify (Divide(u, Pow (x, Rational (snd m)))), (snd m))
    | _ ->
      if contains_x u x then (Undefined, snd(Mpfr.init_set_si 0 Mpfr.Near))
      else (u, snd(Mpfr.init_set_si 0 Mpfr.Near)))
  ;;


(* the degree of the polynomial u in y *)
let degree u y =
  let x = degree_monomial u y in
  if fst x <> Undefined then x
  else (match u with
    | Sum sumList ->
      let degreelist = List.map (fun a -> degree_monomial a y) sumList in
      if List.exists (fun x1 -> fst x1 = Undefined) degreelist then (Undefined, snd(Mpfr.init_set_si 0 Mpfr.Near))
      else
        let max a b =
          let a_deg = snd a in
          let b_deg = snd b in
          let cmp_result = Mpfr.cmp a_deg b_deg in
          if cmp_result < 0 then b
          else a in
        List.fold_left max (Symbolic_Constant "y", snd(Mpfr.init_set_si (-1) Mpfr.Near)) degreelist
    | _ -> (Undefined, snd (Mpfr.init_set_si 0 Mpfr.Near)))
  ;;

(* u and v are polynomials in a *)
let polynomial_division u v a =
  let x = degree u a in
  let y = degree v a in
  let n = snd y in
  let lcv = fst y in
  let rec aux acc m r =
    let is_zero expr =
      match expr with
      | Rational rat when (Mpfr.cmp_si rat 0)=0 -> true
      | _ -> false in
    if (Mpfr.cmp m n)<0 || (is_zero r) then (acc, r)
    else
      let lcr = fst (degree r a) in
      let s = Expr_simplifications.automatic_simplify (Divide(lcr, lcv)) in
      let new_acc = Expr_simplifications.automatic_simplify (Sum[acc; Product[s; Pow(a, Minus(Rational m, Rational n))]]) in
      let new_r = Expr_simplifications.automatic_simplify (algebraic_expand (Expr_simplifications.automatic_simplify (Minus(Minus(r, Product[lcr; Pow(a, Rational m)]), Product[Minus(v, Product[lcv;Pow(a, Rational n)]);s;Pow(a, Minus(Rational m, Rational n))])))) in
      let new_m = snd (degree new_r a) in
      aux new_acc new_m new_r in
  aux (Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))) (snd x) u
  ;;


let extended_euclidean u v x =
  match (u, v) with
  | (Rational rat1, Rational rat2) when (Mpfr.cmp_si rat1 0)=0 && (Mpfr.cmp_si rat2 0)=0 ->
    [Rational (snd(Mpfr.init_set_si 0 Mpfr.Near)); Rational (snd(Mpfr.init_set_si 0 Mpfr.Near)); Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))]
  | _ ->
    let rec aux u v app ap bpp bp =
      (match v with
      | Rational rat when (Mpfr.cmp_si rat 0)=0 -> [u; app; bpp;]
      | _ ->
        let division_result = polynomial_division u v x in
        let a = Expr_simplifications.automatic_simplify (Minus (app, Times(fst division_result, ap))) in
        let b = Expr_simplifications.automatic_simplify (Minus (bpp, Times(fst division_result, bp))) in
        let new_app = ap in
        let new_ap = a in
        let new_bpp = bp in
        let new_bp = b in
        let new_u = v in
        let new_v = snd division_result in
        aux new_u new_v new_app new_ap new_bpp new_bp) in
      let aux_result = aux u v (Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))) (Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))) (Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))) (Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))) in
      let c = fst (degree (List.nth aux_result 0) x) in
      let _ = print_endline ("u= " ^ (Expr_helpers.expr_to_string (List.nth aux_result 0))) in
      let _ = print_endline ("App= " ^ (Expr_helpers.expr_to_string (List.nth aux_result 1))) in
      let _ = print_endline ("Bpp= " ^ (Expr_helpers.expr_to_string (List.nth aux_result 2))) in
      let app_res = algebraic_expand (Expr_simplifications.automatic_simplify (Divide(List.nth aux_result 1, c))) in
      let bpp_res = algebraic_expand (Expr_simplifications.automatic_simplify (Divide(List.nth aux_result 2, c))) in
      let u_res = algebraic_expand (Expr_simplifications.automatic_simplify (Divide(List.nth aux_result 0, c))) in
      [u_res; app_res; bpp_res]
  ;;
*)
