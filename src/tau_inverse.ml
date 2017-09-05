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
  | OpPow (OpSum [OpRational rat; Q], OpRational neg_k) when (Mpq.cmp_si rat (-1) 1)=0 && (Mpq.cmp_si neg_k 0 1)<0 && Expr_simplifications.is_int neg_k ->
      true
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      true
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 0 1)<0 && Expr_simplifications.is_int rat2 ->
      true
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      true
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 0 1)<0 && Expr_simplifications.is_int rat2 ->
      true
  | OpPow (OpSum [OpRational neg_k; Q], OpRational rat1) when (Mpq.cmp_si rat1 (-1) 1)=0 ->
      true
  | OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c) when Expr_simplifications.is_int neg_c && (Mpq.cmp_si neg_c 0 1) < 0 ->
      true
  | OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c) when Expr_simplifications.is_int neg_c && (Mpq.cmp_si neg_c 0 1) < 0 && (Mpq.cmp_si neg_one (-1) 1)=0 ->
      true
  | OpPow(OpSum [OpRational b; OpProduct[OpRational a; Q]], OpRational c) when Expr_simplifications.is_int c ->
      let b_over_a = Mpq.init() in
      let _ = Mpq.div b_over_a b a in
      complete_tiling (OpPow(OpSum[OpRational b_over_a; Q], OpRational c))
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational b; OpProduct[OpRational a; Q]], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      true
  | OpProduct [OpSum [OpRational neg_one_a; Q]; OpPow(OpSum[Q; OpProduct[OpRational neg_one_b; OpSymbolic_Constant a]], OpRational neg_one_c)] when (Mpq.cmp_si neg_one_a (-1) 1)=0
&& (Mpq.cmp_si neg_one_b (-1) 1)=0 && (Mpq.cmp_si neg_one_c (-1) 1)=0 ->
      true
  | OpPow(OpSum[Q; OpProduct[OpRational neg_one_a; OpSymbolic_Constant a]], OpRational neg_one_b) when (Mpq.cmp_si neg_one_a (-1) 1)=0 && (Mpq.cmp_si neg_one_b (-1) 1)=0 ->
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
  | OpLog (b, expression) ->
      if Op_transforms.contains_q expression then false
      else true
  | _ ->false (* might be too strong *)



let rec tau_inverse op_expr input_ident = 
  match op_expr with
  | OpPow (OpSum [OpRational rat; Q], OpRational neg_k) when (Mpq.cmp_si rat (-1) 1)=0 && (Mpq.cmp_si neg_k 0 1)<0 && Expr_simplifications.is_int neg_k ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in
      Binomial (Input_variable input_ident, Rational k)
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in
      Pow (Rational k, Input_variable input_ident)
  | OpProduct [OpPow (OpSum [OpRational neg_k; Q], OpRational rat2); OpSum [OpRational rat1; Q]] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 0 1)<0 && Expr_simplifications.is_int rat2 ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in
      let neg_c = Mpq.init () in
      let c = Mpq.init () in
      let _ = Mpq.add neg_c rat2 (Mpq.init_set_si 1 1) in
      let _ = Mpq.neg c neg_c in
      Product [Binomial (Input_variable input_ident, Rational c); Pow(Rational k, Sum[Rational neg_c; Input_variable input_ident])]
  
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in
      Pow (Rational k, Input_variable input_ident)
  
  | OpProduct [OpSum [OpRational neg_one_a; Q]; OpPow(OpSum[Q; OpProduct[OpRational neg_one_b; OpSymbolic_Constant a]], OpRational neg_one_c)] when (Mpq.cmp_si neg_one_a (-1) 1)=0 && (Mpq.cmp_si neg_one_b (-1) 1)=0 && (Mpq.cmp_si neg_one_c (-1) 1)=0 ->
      Pow (Symbolic_Constant a, Input_variable input_ident)
  | OpPow(OpSum[Q; OpProduct[OpRational neg_one_a; OpSymbolic_Constant a]], OpRational neg_one_b) when (Mpq.cmp_si neg_one_a (-1) 1)=0 && (Mpq.cmp_si neg_one_b (-1) 1)=0 ->
      Product[Sum[Pow(Symbolic_Constant a, Input_variable input_ident); Rational neg_one_a]; Pow(Sum[Symbolic_Constant a; Rational neg_one_a], Rational neg_one_a)]
 
  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_b; OpProduct[OpRational a; Q]], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 (-1) 1)=0 ->
      let k = Mpq.init () in
      let b = Mpq.init () in
      let _ = Mpq.neg b neg_b in
      let _ = Mpq.div k b a in
      let a_inv = Mpq.init () in
      let _ = Mpq.inv a_inv a in
      Product [Rational a_inv; Pow (Rational k, Input_variable input_ident)]

  | OpProduct [OpSum [OpRational rat1; Q]; OpPow (OpSum [OpRational neg_k; Q], OpRational rat2)] when (Mpq.cmp_si rat1 (-1) 1)=0 && (Mpq.cmp_si rat2 0 1)<0 && Expr_simplifications.is_int rat2 ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in
      let neg_c = Mpq.init () in
      let c = Mpq.init () in
      let _ = Mpq.add neg_c rat2 (Mpq.init_set_si 1 1) in
      let _ = Mpq.neg c neg_c in
      Product [Binomial (Input_variable input_ident, Rational c); Pow(Rational k, Sum[Rational neg_c; Input_variable input_ident])]

  | OpPow (OpSum [OpRational neg_k; Q], OpRational rat1) when (Mpq.cmp_si rat1 (-1) 1)=0 ->
      let k = Mpq.init () in
      let _ = Mpq.neg k neg_k in	(* should automatically simplify these expressions before sending out *)
      Product [Sum [Rational (Mpq.init_set_si (-1) 1); Pow(Rational k , Input_variable input_ident)]; Pow(Sum [Rational (Mpq.init_set_si (-1) 1); Rational k], Rational (Mpq.init_set_si (-1) 1))]
  | OpPow(OpSum [OpRational b; OpProduct[OpRational a; Q]], OpRational c) when Expr_simplifications.is_int c ->
      let a_to_c = Expr_simplifications.exp_by_squaring_int a c in
      let b_over_a = Mpq.init() in
      let _ = Mpq.div b_over_a b a in
      Product[Rational a_to_c; tau_inverse (OpPow(OpSum[OpRational b_over_a; Q], OpRational c)) input_ident]

  | OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c) when Expr_simplifications.is_int neg_c && (Mpq.cmp_si neg_c 0 1)<0 ->
      let a = Mpq.init () in
      let c = Mpq.init () in
      (*let a_plus_1 = Mpfr.init () in
      let c_plus_1 = Mpfr.init () in*)
      let neg_c_plus_1 = Mpq.init () in
      let a_minus_1 = Mpq.init () in
      let c_minus_1 = Mpq.init () in
      let _ = Mpq.neg a neg_a in
      let _ = Mpq.neg c neg_c in
      (*let _ = Mpfr.add_ui a_plus_1 a 1 Mpfr.Near in
      let _ = Mpfr.add_ui c_plus_1 c 1 Mpfr.Near in*)
      let _ = Mpq.add neg_c_plus_1 neg_c (Mpq.init_set_si 1 1) in
      let _ = Mpq.sub a_minus_1 a (Mpq.init_set_si 1 1) in
      let _ = Mpq.sub c_minus_1 c (Mpq.init_set_si 1 1) in
      Divide(Minus(Times(Binomial(Input_variable input_ident, Rational c_minus_1), Pow(Rational a, Sum[Input_variable input_ident; Rational neg_c_plus_1])), tau_inverse (OpPow(OpSum [OpRational neg_a; Q], OpRational neg_c_plus_1)) input_ident), Rational a_minus_1)
  | OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c) when Expr_simplifications.is_int neg_c && (Mpq.cmp_si neg_c 0 1) < 0 && (Mpq.cmp_si neg_one (-1) 1)=0 ->
      let c = Mpq.init () in
      (*let a_plus_1 = Mpfr.init () in
      let c_plus_1 = Mpfr.init () in*)
      let neg_c_plus_1 = Mpq.init () in
      let c_minus_1 = Mpq.init () in
      let _ = Mpq.neg c neg_c in
      (*let _ = Mpfr.add_ui a_plus_1 a 1 Mpfr.Near in
      let _ = Mpfr.add_ui c_plus_1 c 1 Mpfr.Near in*)
      let _ = Mpq.add neg_c_plus_1 neg_c (Mpq.init_set_si 1 1) in
      let _ = Mpq.sub c_minus_1 c (Mpq.init_set_si 1 1) in
      Divide(Minus(Times(Binomial(Input_variable input_ident, Rational c_minus_1), Pow(Symbolic_Constant a, Sum[Input_variable input_ident; Rational neg_c_plus_1])), tau_inverse (OpPow(OpSum [Q; OpProduct[OpRational neg_one; OpSymbolic_Constant a]], OpRational neg_c_plus_1)) input_ident), Minus(Symbolic_Constant a, Rational (Mpq.init_set_si 1 1)))
  | OpSum expr_list ->
      Sum (List.map (fun x -> tau_inverse x input_ident) expr_list)
      (*if complete_tiling op_expr then Sum (List.map (fun x -> tau_inverse x input_ident) expr_list)
      else 
        let first_term_cant_solve = List.nth (List.filter (fun x -> not (complete_tiling x)) expr_list) 0 in
        raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string first_term_cant_solve)))*)
  | OpRational rat -> Rational rat
  | OpSymbolic_Constant str (* probably some other things *) -> Symbolic_Constant str
  | OpBase_case (str, integer) -> Base_case (str, integer)
  | OpProduct expr_list ->
      let (term, const_list) = List.partition Op_transforms.contains_q expr_list in
      if (List.length const_list) <> 0 then Product (List.append (List.map (fun x -> tau_inverse x input_ident) const_list) ((tau_inverse (Op_simplifications.op_automatic_simplify (OpProduct term)) input_ident) :: []))
      else (
        let is_shift_op op_expression =
          (match op_expression with
          | OpPow (Q, OpRational exp) ->
            let den = Mpz.init () in
            let _ = Mpq.get_den den exp in
            if (Mpz.cmp_si den 1) = 0 then true
            else false
          | Q -> true
          | _ -> false
          ) in
        let (shift, rest) = List.partition is_shift_op expr_list in
        (match shift with
        | OpPow (Q, OpRational exp) :: [] ->
          let num = Mpz.init () in
          let _ = Mpq.get_num num exp in
          let num_int = (int_of_string (Mpz.to_string num)) * (-1) in
          Shift (num_int, tau_inverse (Op_simplifications.op_automatic_simplify (OpProduct rest)) input_ident)
        | Q :: [] -> Shift (-1, tau_inverse (Op_simplifications.op_automatic_simplify (OpProduct rest)) input_ident)
        | [] -> Iif (Expr_helpers.op_expr_to_string op_expr, SSVar input_ident)
        | _ -> raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string op_expr)))
        )
      )
      (*raise (Tau_inverse_exc ("OCRS is unable to transform " ^ (Expr_helpers.op_expr_to_string op_expr))) (* need to do some transformations *)*)
  | OpPow (base, exp) when (not (Op_transforms.contains_q base)) && (not (Op_transforms.contains_q exp)) ->
      Pow (tau_inverse base input_ident, tau_inverse exp input_ident)
  | OpLog (b, expression) when (not (Op_transforms.contains_q expression))->
      Log (b, tau_inverse expression input_ident)
  | _ ->
      (match op_expr with
      | OpPow (Q, OpRational exp) ->
        let num = Mpz.init () in
        let _ = Mpq.get_num num exp in
        let num_int = (int_of_string (Mpz.to_string num)) * (-1) in
        Shift(num_int, Rational (Mpq.init_set_si 1 1))
      | Q ->
        Shift(-1, Rational (Mpq.init_set_si 1 1))
      | _ -> 
        Iif(Expr_helpers.op_expr_to_string op_expr, SSVar input_ident)
      ) 
  ;;

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

