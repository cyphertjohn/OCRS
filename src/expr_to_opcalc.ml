open Type_def

exception Expr_to_op_exc of string

let rec binomial_transform expr =
  match expr with
  | Pow(Input_variable ident, Rational rat) when Mpfr.integer_p rat && (Mpfr.cmp_si rat 0) > 0 ->
      let find_first_deg_elem deg = 
          let rec aux a b = 
              (if (Mpfr.cmp a b) > 0 then [] 
              else
                  let pow_res = Mpfr.init () in
                  let a_plus_1 = Mpfr.init () in 
                  let _ = Mpfr.pow pow_res a b Mpfr.Near in
                  let _ = Mpfr.add_ui a_plus_1 a 1 Mpfr.Near in
                  pow_res :: (aux a_plus_1 b)) in
          aux (snd(Mpfr.init_set_si 0 Mpfr.Near)) deg in
      let val_list = find_first_deg_elem rat in
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
          let _ = Mpfr.div result result y_temp Mpfr.Near in (* x = x/y *) result in
      let rec accumulate j k = 
          if (Mpfr.cmp j k) > 0 then (snd(Mpfr.init_set_si 0 Mpfr.Near))
          else( 
              let minus_one = snd (Mpfr.init_set_si (-1) Mpfr.Near) in
              let k_minus_j = Mpfr.init () in
              let _ = Mpfr.sub k_minus_j k j Mpfr.Near in
              let j_plus_1 = Mpfr.init () in
              let _ = Mpfr.add_ui j_plus_1 j 1 Mpfr.Near in
              let _ = Mpfr.pow minus_one minus_one k_minus_j Mpfr.Near in
              let binom = binomial k j in
              let f_j = List.nth val_list (int_of_float(Mpfr.to_float j)) in
              let result = Mpfr.init () in
              let _ = Mpfr.mul result minus_one f_j Mpfr.Near in
              let _ = Mpfr.mul result result binom Mpfr.Near in
              let acc = accumulate j_plus_1 k in
              let _ = Mpfr.add result result acc Mpfr.Near in
              result) in
      let rec build_sum_lis k deg = 
          if (Mpfr.cmp k deg) > 0 then []
          else(
              let k_plus_1 = Mpfr.init () in
              let _ = Mpfr.add_ui k_plus_1 k 1 Mpfr.Near in
              let zero = snd (Mpfr.init_set_si 0 Mpfr.Near) in
              Product [Binomial(Input_variable ident, Rational k); Rational (accumulate zero k)] :: (build_sum_lis k_plus_1 deg)
          ) in
      let zero = snd (Mpfr.init_set_si 0 Mpfr.Near) in
      Expr_simplifications.automatic_simplify (Sum (build_sum_lis zero rat))
      (* for k = 0 to deg do Product [Binomial(Input_variable ident, Rational k); Rational ((accumulate 0 k) * 1/k!)] *)

  | _ -> raise (Expr_to_op_exc "Error in Binomial Transform")
  ;;

(* need to check to make sure the transform is possible namely pointwise multiplication and pointwise divide *)

(* Also assumes all output variables are n or higher *)
let rec expr_to_opCalc expr =
  match expr with
  | Plus (left, right) ->							(* should not be called *)
      OpPlus(expr_to_opCalc left, expr_to_opCalc right)
  | Minus (left, right) ->							(* Minuses should be removed *)
      OpMinus(expr_to_opCalc left, expr_to_opCalc right)			(* this method should not be called *)
  | Times (left, right) ->							(* also should not be called *)
      OpTimes(expr_to_opCalc left, expr_to_opCalc right)
  | Divide (left, right) ->
      OpDivide (expr_to_opCalc left, expr_to_opCalc right)
  | Product expr_list ->
      let is_const expr =
        match expr with
        | Rational _ | Base_case _ | Symbolic_Constant _ ->
          true
        | _ -> false in
      let (const_list, var_list) = List.partition is_const expr_list in
      if (List.length const_list) <> 0 then OpProduct ((List.map expr_to_opCalc const_list) @ [expr_to_opCalc (Expr_simplifications.automatic_simplify (Product var_list))])
      else
        (match expr_list with
        | Pow (Rational k, Input_variable str) :: Binomial (Input_variable str1, Rational c) :: [] when str = str1->
          let const = Mpfr.init () in
          let c_plus_1 = Mpfr.init () in
          let _ = Mpfr.pow const k c Mpfr.Near in
          let _ = Mpfr.add_ui c_plus_1 c 1 Mpfr.Near in
          OpProduct [OpRational const; OpDivide(OpMinus (Q, OpRational (snd(Mpfr.init_set_si 1 Mpfr.Near))), OpPow (OpMinus(Q, OpRational k), OpRational c_plus_1))]
        | Pow (Rational k, Input_variable str1) :: Pow(Input_variable str, Rational rat) :: [] when str = str1 ->
          let new_expr = (Expr_transforms.algebraic_expand (Expr_simplifications.automatic_simplify (Product [binomial_transform (Pow (Input_variable str, Rational rat)); Pow(Rational k, Input_variable str)]))) in
          expr_to_opCalc new_expr
        | Pow (Rational k, Input_variable str) :: (Input_variable str1) :: [] when str = str1 ->
          OpProduct [OpRational k; OpDivide(OpMinus (Q, OpRational (snd(Mpfr.init_set_si 1 Mpfr.Near))), OpPow(OpMinus(Q, OpRational k), OpRational (snd(Mpfr.init_set_si 2 Mpfr.Near))))]
        | _ -> raise (Expr_to_op_exc "Can't transform non-linear product"))
  | Sum expr_list ->
      OpSum (List.map expr_to_opCalc expr_list)  					(* convert all list elem to strings concat with star *)
  | Symbolic_Constant ident ->
      OpSymbolic_Constant ident
  | Output_variable (ident, subscript) ->
      (match subscript with
       | SAdd (loop_counter, shift) when shift>0 ->
           if shift = 1 then (
               OpMinus (OpTimes (Q, OpOutput_variable (ident, SSVar loop_counter)), OpTimes (OpMinus (Q, OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))), OpBase_case(ident, 0)))
               )
           else (
               let expr_list = 
                   (let rec build_list mu m = 
                       if mu=(m-1) then OpProduct [OpPow (Q, OpRational (snd (Mpfr.init_set_si mu Mpfr.Near))); OpMinus (Q, OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))); OpBase_case (ident, (m-1-mu))] :: []
                       else OpProduct [OpPow (Q, OpRational (snd (Mpfr.init_set_si mu Mpfr.Near))); OpMinus (Q, OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))); OpBase_case (ident, (m-1-mu))] :: (build_list (mu+1) m)
                   in build_list 0 shift) in
               let right_summation = OpSum expr_list in
                   OpMinus (OpTimes (OpPow (Q, OpRational (snd (Mpfr.init_set_si shift Mpfr.Near))), OpOutput_variable (ident, SSVar loop_counter)), right_summation)
               )
       
       | SSVar loop_counter ->
           OpOutput_variable (ident, subscript)
       | _ ->
           raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
       )
  | Input_variable str ->
      expr_to_opCalc (Binomial(expr, (Rational (snd (Mpfr.init_set_si 1 Mpfr.Near)))))
  | Rational rat ->
      OpRational rat
  | Log (base, expression) ->
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
      (* don't know what to do here *)
  | Pow (left, right) ->
      (match (left, right) with
      | (_, Sum sumList) ->
          let aux exp = 
            Pow (left, exp) in
          expr_to_opCalc (Expr_simplifications.automatic_simplify (Product (List.map aux sumList)))
      | (Input_variable ident, Rational rat) when Mpfr.integer_p rat && (Mpfr.cmp_si rat 0)>0 ->
          expr_to_opCalc (binomial_transform expr)
      | (Rational rat, Input_variable ident) ->
          OpDivide(OpMinus(Q, OpRational (snd(Mpfr.init_set_si 1 Mpfr.Near))), OpMinus(Q, OpRational rat))
      | _ -> 
          let expand_result = Expr_transforms.algebraic_expand expr in
          if expand_result <> expr then expr_to_opCalc expand_result
          else raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr))))
  | Binomial (top, bottom) ->
      (match (top, bottom) with
          | (Input_variable ident, Rational k) when (Mpfr.integer_p k) ->	(* if the binomial is of the form n choose k, where k is a constant int *)
              let _ = Mpfr.neg k k Mpfr.Near in
              OpPow (OpMinus (Q, OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))), OpRational k)		(* appropriate transformation *)
          | _ ->
              raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
      )
  | Base_case (ident, index) ->
      OpBase_case (ident, index)
  | Factorial child ->
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Undefined ->
      OpUndefined
  ;;


let rec inequation_to_opCalc inequation =
  match inequation with
  | Equals (left, right) ->
      OpEquals (expr_to_opCalc left, expr_to_opCalc right)
  | LessEq (left, right) ->
      OpLessEq (expr_to_opCalc left, expr_to_opCalc right)
  | Less (left, right) ->
      OpLess (expr_to_opCalc left, expr_to_opCalc right)
  | GreaterEq (left, right) ->
      OpGreaterEq (expr_to_opCalc left, expr_to_opCalc right)
  | Greater (left, right) ->
      OpGreater (expr_to_opCalc left, expr_to_opCalc right)
  ;;

