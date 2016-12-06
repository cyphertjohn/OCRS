open Type_def
open Op_simplifications

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
  let q_minus1 = op_automatic_simplify (OpSum [Q; OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))]) in
  match (r, s) with
  | (OpSum sumList, _) when (op_expr_order r q_minus1) <> 0->
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
      let zero = snd (Mpfr.init_set_si 0 Mpfr.Near) in
      let rec aux acc k = 
        if (Mpfr.cmp k n) > 0 then OpSum acc
        else
          let c = binomial n k in
          let n_minus_k = Mpfr.init () in
          let k_plus1 = Mpfr.init () in
          let _ = Mpfr.add_ui k_plus1 k 1 Mpfr.Near in
          let _ = Mpfr.sub n_minus_k n k Mpfr.Near in
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
    | OpRational rat when (Mpfr.integer_p rat) && (Mpfr.cmp_si rat 2) >= 0 ->
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
