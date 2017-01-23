open Type_def
open Expr_simplifications

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
  ;;

let rec expand_product r s = 
  match (r, s) with
  | (Sum sumList, _)->
    (match sumList with
    | [] -> failwith "Sum operand list was empty"
    | hd :: [] -> expand_product hd s
    | hd :: tail -> automatic_simplify (Sum [expand_product hd s; expand_product (Sum tail) s]))
  | (_, Sum _) -> expand_product s r
  | _ -> automatic_simplify (Product [r; s])
  ;;

let rec expand_power u n =
  match u with
  | Sum sumList ->
    (match sumList with
    | [] -> failwith "Sum operandList was empty"
    | hd :: [] -> expand_power hd n
    | f :: tail ->
      let r = Sum tail in
      let zero = snd (Mpfr.init_set_si 0 Mpfr.Near) in
      let rec aux acc k = 
        if (Mpfr.cmp k n) > 0 then Sum acc
        else
          let c = binomial n k in
          let n_minus_k = Mpfr.init () in
          let k_plus1 = Mpfr.init () in
          let _ = Mpfr.add_ui k_plus1 k 1 Mpfr.Near in
          let _ = Mpfr.sub n_minus_k n k Mpfr.Near in
          aux (acc @ [(expand_product (Product [Rational c; Pow(f, (Rational n_minus_k))]) (expand_power r k))]) k_plus1 in
      automatic_simplify (aux [(Rational zero)] zero))
  | _ -> Pow (u, Rational n)
  ;;
  
  
  
let rec algebraic_expand expr = 
  match expr with
  | Sum sumList ->
    (match sumList with
    | [] -> failwith "Sum Operand List was empty"
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> automatic_simplify (Sum [algebraic_expand hd; algebraic_expand (Sum tail)]))
  | Product prodList ->
    (match prodList with
    | [] -> failwith "Product Operand List was empty"
    | hd :: [] -> algebraic_expand hd
    | hd :: tail -> automatic_simplify (expand_product (algebraic_expand hd) (algebraic_expand (Product tail))))
  | Pow (base, exp) ->
    (match exp with
    | Rational rat when (Mpfr.integer_p rat) && (Mpfr.cmp_si rat 2) >= 0 ->
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
  | Rational _ | Symbolic_Constant _ | Base_case (_, _) | Output_variable (_, _) | Input_variable _ | Undefined ->
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
      | (_, Rational rat) when (Mpfr.cmp_si rat 0)=0 ->
        Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))            (*might need a stronger condition *)
      | (_, Rational rat) when (Mpfr.cmp_si rat 1)=0 ->
        top
      | (Rational ratTop, Rational ratBot) when (Mpfr.cmp ratTop ratBot)<0 ->
        Rational (snd(Mpfr.init_set_si 0 Mpfr.Near))
      | (Rational ratTop, Rational ratBot) when (Mpfr.cmp_si ratTop 0)>0 && (Mpfr.cmp_si ratBot 0)>0 && (Mpfr.integer_p ratTop) && (Mpfr.integer_p ratBot) ->
        Rational (binomial ratTop ratBot)
      | (Input_variable str, Rational rat) when (Mpfr.cmp_si rat 0)>0 && (Mpfr.integer_p rat) ->
        let rat_minus_1 = Mpfr.init () in
        let denom = Mpfr.init () in
        let _ = Mpfr.add_ui denom rat 1 Mpfr.Near in
        let _ = Mpfr.sub_ui rat_minus_1 rat 1 Mpfr.Near in
        let _ = Mpfr.gamma denom denom Mpfr.Near in
        let rec build_list acc k =
          if (Mpfr.cmp k rat_minus_1)>0 then acc
          else
            let k_plus_1 = Mpfr.init() in
            let _ = Mpfr.add_ui k_plus_1 k 1 Mpfr.Near in
            build_list (acc @ [Minus(Input_variable str, Rational k)]) k_plus_1 in
          algebraic_expand (automatic_simplify (Divide(Product (build_list [] (snd(Mpfr.init_set_si 0 Mpfr.Near))), Rational denom)))
      | _ -> Binomial (top, bottom))
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

