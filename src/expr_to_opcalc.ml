open Type_def

exception Expr_to_op_exc of string

let rec binomial_transform expr =
  match expr with
  | Pow(Input_variable ident, Rational rat) when Expr_simplifications.is_int rat && (Mpq.cmp_si rat 0 1) > 0 ->
      let find_first_deg_elem deg = 
          let rec aux a b = 
              (if (Mpq.cmp a b) > 0 then [] 
              else
                  let pow_res = Expr_simplifications.exp_by_squaring_int a b in
                  let a_plus_1 = Mpq.init () in 
                  let _ = Mpq.add a_plus_1 a (Mpq.init_set_si 1 1) in
                  pow_res :: (aux a_plus_1 b)) in
          aux (Mpq.init_set_si 0 1) deg in
      let val_list = find_first_deg_elem rat in
      let rec accumulate j k = 
          if (Mpq.cmp j k) > 0 then (Mpq.init_set_si 0 1)
          else( 
              let minus_one = (Mpq.init_set_si (-1) 1) in
              let k_minus_j = Mpq.init () in
              let _ = Mpq.sub k_minus_j k j in
              let j_plus_1 = Mpq.init () in
              let _ = Mpq.add j_plus_1 j (Mpq.init_set_si 1 1) in
              let sign = Expr_simplifications.exp_by_squaring_int minus_one k_minus_j in
              let binom = Expr_simplifications.binomial k j in
              let f_j = List.nth val_list (int_of_float(Mpq.to_float j)) in
              let result = Mpq.init () in
              let _ = Mpq.mul result sign f_j in
              let _ = Mpq.mul result result binom in
              let acc = accumulate j_plus_1 k in
              let _ = Mpq.add result result acc in
              result) in
      let rec build_sum_lis k deg = 
          if (Mpq.cmp k deg) > 0 then []
          else(
              let k_plus_1 = Mpq.init () in
              let _ = Mpq.add k_plus_1 k (Mpq.init_set_si 1 1) in
              let zero = Mpq.init_set_si 0 1 in
              Product [Binomial(Input_variable ident, Rational k); Rational (accumulate zero k)] :: (build_sum_lis k_plus_1 deg)
          ) in
      let zero = Mpq.init_set_si 0 1 in
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
      let (const_list, var_list) = List.partition Expr_helpers.is_const expr_list in
      if (List.length const_list) <> 0 then OpProduct ((List.map expr_to_opCalc const_list) @ [expr_to_opCalc (Expr_simplifications.automatic_simplify (Product var_list))])
      else
        (match expr_list with
        | Pow (Rational k, Input_variable str) :: Binomial (Input_variable str1, Rational c) :: [] when str = str1 && Expr_simplifications.is_int c->
          let const = Expr_simplifications.exp_by_squaring_int k c in
          let c_plus_1 = Mpq.init () in
          let _ = Mpq.add c_plus_1 c (Mpq.init_set_si 1 1) in
          OpProduct [OpRational const; OpDivide(OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpPow (OpMinus(Q, OpRational k), OpRational c_plus_1))]
        | Pow (Symbolic_Constant sym, Input_variable str) :: Binomial (Input_variable str1, Rational c) :: [] when str = str1->
          let c_plus_1 = Mpq.init () in
          let _ = Mpq.add c_plus_1 c (Mpq.init_set_si 1 1) in
          OpProduct [OpPow(OpSymbolic_Constant sym, OpRational c); OpDivide(OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpPow (OpMinus(Q, OpSymbolic_Constant sym), OpRational c_plus_1))]
        | Pow (Rational k, Input_variable str1) :: Pow(Input_variable str, Rational rat) :: [] when str = str1 ->
          let new_expr = (Expr_transforms.algebraic_expand (Expr_simplifications.automatic_simplify (Product [binomial_transform (Pow (Input_variable str, Rational rat)); Pow(Rational k, Input_variable str)]))) in
          expr_to_opCalc new_expr
        | Pow (Rational k, Input_variable str) :: (Input_variable str1) :: [] when str = str1 ->
          OpProduct [OpRational k; OpDivide(OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpPow(OpMinus(Q, OpRational k), OpRational (Mpq.init_set_si 2 1)))]
        | Pow (Symbolic_Constant sym, Input_variable str) :: (Input_variable str1) :: [] when str = str1 ->
          OpProduct [OpSymbolic_Constant sym; OpDivide(OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpPow(OpMinus(Q, OpSymbolic_Constant sym), OpRational (Mpq.init_set_si 2 1)))]
        | Pow (Symbolic_Constant sym, Input_variable str1) :: Pow(Input_variable str, Rational rat) :: [] when str = str1 ->
          let new_expr = (Expr_transforms.algebraic_expand (Expr_simplifications.automatic_simplify (Product [binomial_transform (Pow (Input_variable str, Rational rat)); Pow(Symbolic_Constant sym, Input_variable str)]))) in
          expr_to_opCalc new_expr
        | _ -> raise (Expr_to_op_exc "Can't transform non-linear product"))
  | Sum expr_list ->
      OpSum (List.map expr_to_opCalc expr_list)  					(* convert all list elem to strings concat with star *)
  | Symbolic_Constant ident ->
      OpSymbolic_Constant ident
  | Output_variable (ident, subscript) ->
      (match subscript with
       | SAdd (loop_counter, shift) when shift>0 ->
           if shift = 1 then (
               OpMinus (OpTimes (Q, OpOutput_variable (ident, SSVar loop_counter)), OpTimes (OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpBase_case(ident, 0)))
               )
           else (
               let expr_list = 
                   (let rec build_list mu m = 
                       if mu=(m-1) then OpProduct [OpPow (Q, OpRational (Mpq.init_set_si mu 1)); OpMinus (Q, OpRational (Mpq.init_set_si 1 1)); OpBase_case (ident, (m-1-mu))] :: []
                       else OpProduct [OpPow (Q, OpRational (Mpq.init_set_si mu 1)); OpMinus (Q, OpRational (Mpq.init_set_si 1 1)); OpBase_case (ident, (m-1-mu))] :: (build_list (mu+1) m)
                   in build_list 0 shift) in
               let right_summation = OpSum expr_list in
                   OpMinus (OpTimes (OpPow (Q, OpRational (Mpq.init_set_si shift 1)), OpOutput_variable (ident, SSVar loop_counter)), right_summation)
               )
       
       | SSVar loop_counter ->
           OpOutput_variable (ident, subscript)
       | _ ->
           raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
       )
  | Input_variable str ->
      expr_to_opCalc (Binomial(expr, (Rational (Mpq.init_set_si 1 1))))
  | Rational rat ->
      OpRational rat
  | Log (base, expression) ->
      if (Expr_helpers.is_const expression) then (OpLog (base, expr_to_opCalc expression))
      else (raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr))))
      (* don't know what to do here *)
  | Pow (left, right) ->
      if Expr_helpers.is_const left && Expr_helpers.is_const right then OpPow (expr_to_opCalc left, expr_to_opCalc right)
      else
        (match (left, right) with
        | (_, Sum sumList) ->
          let aux exp = 
            Pow (left, exp) in
          expr_to_opCalc (Expr_simplifications.automatic_simplify (Product (List.map aux sumList)))
        | (Input_variable ident, Rational rat) when Expr_simplifications.is_int rat && (Mpq.cmp_si rat 0 1)>0 ->
          expr_to_opCalc (binomial_transform expr)
        | (Rational rat, Input_variable ident) ->
          OpDivide(OpMinus(Q, OpRational (Mpq.init_set_si 1 1)), OpMinus(Q, OpRational rat))
        | (Symbolic_Constant ident, Input_variable ivar_ident) -> 
          OpDivide(OpMinus(Q, OpRational (Mpq.init_set_si 1 1)), OpMinus(Q, OpSymbolic_Constant ident))
        | _ -> 
          let expand_result = Expr_transforms.algebraic_expand expr in
          if expand_result <> expr then expr_to_opCalc expand_result
          else raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr))))
  | Binomial (top, bottom) ->
      (match (top, bottom) with
          | (Input_variable ident, Rational k) when (Expr_simplifications.is_int k) ->	(* if the binomial is of the form n choose k, where k is a constant int *)
              let _ = Mpq.neg k k in
              OpPow (OpMinus (Q, OpRational (Mpq.init_set_si 1 1)), OpRational k)		(* appropriate transformation *)
          | _ ->
              raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
      )
  | Base_case (ident, index) ->
      OpBase_case (ident, index)
  | Factorial child ->
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Undefined ->
      OpUndefined
  | IDivide (num, denom) when Expr_helpers.is_const num ->
      SymIDivide (expr_to_opCalc num, denom)
  | IDivide (Input_variable ident, denom) ->
      if Expr_simplifications.is_int denom then
        OpDivide(OpRational (Mpq.init_set_si 1 1), OpMinus(OpPow(Q, OpRational denom), OpRational (Mpq.init_set_si 1 1)))
      else raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | IDivide _ -> (* can do more here *)
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Sin _ -> (*(Product prod_list) ->*) (* haven't done this part yet *)
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Cos _ ->
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Arctan (value) ->
      OpArctan (value)
  | Mod (left, right) ->
      raise (Expr_to_op_exc ("Error transforming " ^ (Expr_helpers.expr_to_string expr)))
  | Pi ->
      OpPi
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

