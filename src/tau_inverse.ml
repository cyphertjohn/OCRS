open Type_def

exception Tau_inverse_exc of string

let is_const op_expr = 
  match op_expr with
  | OpRational _ | OpBase_case _ | OpSymbolic_Constant _ ->
      true
  | _ -> false
  ;;


let rec complete_tiling op_expr = 
  match op_expr with
  | OpPow (OpSum [OpRational rat; Q], OpRational neg_k) when (Mpfr.cmp_si rat (-1))=0 && (Mpfr.cmp_si neg_k 0)<0 && (Mpfr.integer_p neg_k) ->
      true
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      true
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 0)<0 && (Mpfr.integer_p rat2) ->
      true
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      true
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 0)<0 && (Mpfr.integer_p rat2) ->
      true
  | OpPow (OpSum [OpRational neg_k; Q], OpRational rat1) when (Mpfr.cmp_si rat1 (-1))=0 ->
      true
  | OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c) when (Mpfr.integer_p neg_c) && (Mpfr.cmp_si neg_c 0) < 0 ->
      true
  | OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c) when (Mpfr.integer_p neg_c) && (Mpfr.cmp_si neg_c 0) < 0 && (Mpfr.cmp_si neg_one (-1))=0 ->
      true
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational b; OpProduct[OpRational a; Q]], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      true
  | OpProduct [OpSum [OpRational neg_one_a; Q]; OpPow(OpSum[Q; OpProduct[OpRational neg_one_b; OpSymbolic_Constant a]], OpRational neg_one_c)] when (Mpfr.cmp_si neg_one_a (-1))=0
&& (Mpfr.cmp_si neg_one_b (-1))=0 && (Mpfr.cmp_si neg_one_c (-1))=0 ->
      true
  | OpPow(OpSum[Q; OpProduct[OpRational neg_one_a; OpSymbolic_Constant a]], OpRational neg_one_b) when (Mpfr.cmp_si neg_one_a (-1))=0 && (Mpfr.cmp_si neg_one_b (-1))=0 ->
      true
  | OpSum expr_list ->
      List.for_all complete_tiling expr_list
  | OpRational rat -> true
  | OpSymbolic_Constant str (* probably some other things *) -> true
  | OpBase_case (str, integer) -> true
  | OpPow(left, right) when not (Op_transforms.contains_q left) && not (Op_transforms.contains_q right) -> true
  | OpProduct expr_list ->
      let (term, const_list) = List.partition Op_transforms.contains_q expr_list in 
      if (List.length const_list) <> 0 then complete_tiling (Op_simplifications.op_automatic_simplify (OpProduct term))
      else false
  | _ ->false (* might be too strong *)



let rec tau_inverse op_expr input_ident = 
  match op_expr with
  | OpPow (OpSum [OpRational rat; Q], OpRational neg_k) when (Mpfr.cmp_si rat (-1))=0 && (Mpfr.cmp_si neg_k 0)<0 && (Mpfr.integer_p neg_k) ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in
      Binomial (Input_variable input_ident, Rational k)
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in
      Pow (Rational k, Input_variable input_ident)
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 0)<0 && (Mpfr.integer_p rat2) ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in
      let neg_c = Mpfr.init () in
      let c = Mpfr.init () in
      let _ = Mpfr.add_ui neg_c rat2 1 Mpfr.Near in
      let _ = Mpfr.neg c neg_c Mpfr.Near in
      Product [Binomial (Input_variable input_ident, Rational c); Pow(Rational k, Sum[Rational neg_c; Input_variable input_ident])]
  
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in
      Pow (Rational k, Input_variable input_ident)
  
  | OpProduct [OpSum [OpRational neg_one_a; Q]; OpPow(OpSum[Q; OpProduct[OpRational neg_one_b; OpSymbolic_Constant a]], OpRational neg_one_c)] when (Mpfr.cmp_si neg_one_a (-1))=0 && (Mpfr.cmp_si neg_one_b (-1))=0 && (Mpfr.cmp_si neg_one_c (-1))=0 ->
      Pow (Symbolic_Constant a, Input_variable input_ident)
  | OpPow(OpSum[Q; OpProduct[OpRational neg_one_a; OpSymbolic_Constant a]], OpRational neg_one_b) when (Mpfr.cmp_si neg_one_a (-1))=0 && (Mpfr.cmp_si neg_one_b (-1))=0 ->
      Product[Sum[Pow(Symbolic_Constant a, Input_variable input_ident); Rational neg_one_a]; Pow(Sum[Symbolic_Constant a; Rational neg_one_a], Rational neg_one_a)]
 
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_b; OpProduct[OpRational a; Q]], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 (-1))=0 ->
      let k = Mpfr.init () in
      let b = Mpfr.init () in
      let _ = Mpfr.neg b neg_b Mpfr.Near in
      let _ = Mpfr.div k b a Mpfr.Near in
      let a_inv = Mpfr.init () in
      let _ = Mpfr.pow_si a_inv a (-1) Mpfr.Near in
      Product [Rational a_inv; Pow (Rational k, Input_variable input_ident)]

  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpfr.cmp_si rat1 (-1))=0 && (Mpfr.cmp_si rat2 0)<0 && (Mpfr.integer_p rat2) ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in
      let neg_c = Mpfr.init () in
      let c = Mpfr.init () in
      let _ = Mpfr.add_ui neg_c rat2 1 Mpfr.Near in
      let _ = Mpfr.neg c neg_c Mpfr.Near in
      Product [Binomial (Input_variable input_ident, Rational c); Pow(Rational k, Sum[Rational neg_c; Input_variable input_ident])]

  | OpPow (OpSum [OpRational neg_k; Q], OpRational rat1) when (Mpfr.cmp_si rat1 (-1))=0 ->
      let k = Mpfr.init () in
      let _ = Mpfr.neg k neg_k Mpfr.Near in	(* should automatically simplify these expressions before sending out *)
      Product [Sum [Rational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); Pow(Rational k , Input_variable input_ident)]; Pow(Sum [Rational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); Rational k], Rational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]
  | OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c) when (Mpfr.integer_p neg_c) && (Mpfr.cmp_si neg_c 0)<0 ->
      let a = Mpfr.init () in
      let c = Mpfr.init () in
      (*let a_plus_1 = Mpfr.init () in
      let c_plus_1 = Mpfr.init () in*)
      let neg_c_plus_1 = Mpfr.init () in
      let a_minus_1 = Mpfr.init () in
      let c_minus_1 = Mpfr.init () in
      let _ = Mpfr.neg a neg_a Mpfr.Near in
      let _ = Mpfr.neg c neg_c Mpfr.Near in
      (*let _ = Mpfr.add_ui a_plus_1 a 1 Mpfr.Near in
      let _ = Mpfr.add_ui c_plus_1 c 1 Mpfr.Near in*)
      let _ = Mpfr.add_ui neg_c_plus_1 neg_c 1 Mpfr.Near in
      let _ = Mpfr.sub_ui a_minus_1 a 1 Mpfr.Near in
      let _ = Mpfr.sub_ui c_minus_1 c 1 Mpfr.Near in
      Divide(Minus(Times(Binomial(Input_variable input_ident, Rational c_minus_1), Pow(Rational a, Sum[Input_variable input_ident; Rational neg_c_plus_1])), tau_inverse (OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c_plus_1)) input_ident), Rational a_minus_1)
  | OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c) when (Mpfr.integer_p neg_c) && (Mpfr.cmp_si neg_c 0) < 0 && (Mpfr.cmp_si neg_one (-1))=0 ->
      let c = Mpfr.init () in
      (*let a_plus_1 = Mpfr.init () in
      let c_plus_1 = Mpfr.init () in*)
      let neg_c_plus_1 = Mpfr.init () in
      let c_minus_1 = Mpfr.init () in
      let _ = Mpfr.neg c neg_c Mpfr.Near in
      (*let _ = Mpfr.add_ui a_plus_1 a 1 Mpfr.Near in
      let _ = Mpfr.add_ui c_plus_1 c 1 Mpfr.Near in*)
      let _ = Mpfr.add_ui neg_c_plus_1 neg_c 1 Mpfr.Near in
      let _ = Mpfr.sub_ui c_minus_1 c 1 Mpfr.Near in
      Divide(Minus(Times(Binomial(Input_variable input_ident, Rational c_minus_1), Pow(Symbolic_Constant a, Sum[Input_variable input_ident; Rational neg_c_plus_1])), tau_inverse (OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c_plus_1)) input_ident), Minus(Symbolic_Constant a, Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))))
  | OpSum expr_list ->
      if complete_tiling op_expr then Sum (List.map (fun x -> tau_inverse x input_ident) expr_list)
      else 
        let first_term_cant_solve = List.nth (List.filter (fun x -> not (complete_tiling x)) expr_list) 0 in
        raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string first_term_cant_solve)))
  | OpRational rat -> Rational rat
  | OpSymbolic_Constant str (* probably some other things *) -> Symbolic_Constant str
  | OpBase_case (str, integer) -> Base_case (str, integer)
  | OpProduct expr_list ->
      let (term, const_list) = List.partition Op_transforms.contains_q expr_list in
      if (List.length const_list) <> 0 then Product (List.append (List.map (fun x -> tau_inverse x input_ident) const_list) ((tau_inverse (Op_simplifications.op_automatic_simplify (OpProduct term)) input_ident) :: []))
      else raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string op_expr))) (* need to do some transformations *)
  | OpPow (base, exp) when (not (Op_transforms.contains_q base)) && (not (Op_transforms.contains_q exp)) ->
      Pow (tau_inverse base input_ident, tau_inverse exp input_ident)
  | _ -> raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string op_expr)))


let tau_inverse_inequation expr input_ident =
    match expr with
    | OpEquals (OpOutput_variable(ident, subscript), right) ->
        Equals (Output_variable(ident, subscript), (tau_inverse right input_ident))
    | OpGreaterEq (OpOutput_variable(ident, subscript), right) ->
        GreaterEq (Output_variable(ident, subscript), (tau_inverse right input_ident))
    | OpGreater (OpOutput_variable(ident, subscript), right) ->
        Greater (Output_variable(ident, subscript), (tau_inverse right input_ident))
    | OpLessEq (OpOutput_variable(ident, subscript), right) ->
        LessEq (Output_variable(ident, subscript), (tau_inverse right input_ident))
    | OpLess (OpOutput_variable(ident, subscript), right) ->
        Less (Output_variable(ident, subscript), (tau_inverse right input_ident))
    | _ -> raise (Tau_inverse_exc ("The inequation wasn't solved"))
    ;;

