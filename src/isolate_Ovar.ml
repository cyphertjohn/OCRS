open Type_def
open Op_simplifications

exception Isolating_exc of string

let rec contains_Ovar expr identifier =
  match expr with
  | OpPlus (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | OpMinus (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | OpTimes (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | OpDivide (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | OpProduct expr_list ->
      List.exists (fun x -> contains_Ovar x identifier) expr_list
  | OpSum expr_list ->
      List.exists (fun x -> contains_Ovar x identifier) expr_list
  | OpOutput_variable (ident , subscript) ->
      if ident = identifier then true
      else false
  | OpLog (b, expression) ->
      contains_Ovar expression identifier
  | OpPow (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | OpUndefined | OpSymbolic_Constant _ | OpBase_case _ | OpInput_variable _ | Q | SymBinom _ | SymIDivide _ | SymSin _ | SymCos _ | OpArctan _ | OpRational _ | SymMod _ | OpPi ->
      false
  ;;

let rec move_Ovar_left left right identifier = 
  match (left, right) with
  | (OpSum left_list, OpSum right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum left_list; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]]) in	(* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum right_list; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (OpSum left_list, _) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) (right :: []) in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum left_list; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum [right]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (_, OpSum right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) (left :: []) in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 0 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum [left]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum right_list; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum non_ovar_left]; OpProduct [OpRational (Mpq.init_set_si (-1) 1); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (OpProduct left_list, OpProduct right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct left_list; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct right_list; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | (OpProduct left_list, _) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) (right :: []) in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct left_list; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct [right]; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | (_, OpProduct right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) (left :: []) in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (Mpq.init_set_si 1 1)] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct [left]; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct right_list; OpPow (OpProduct ovar_right, OpRational (Mpq.init_set_si (-1) 1)); OpPow (OpProduct non_ovar_left, OpRational (Mpq.init_set_si (-1) 1))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | _ -> raise (Isolating_exc "OCRS was unable to solve the operation calculus inequation for the Output_variable")
  ;;

let factor_ovar sum_list ident input_ident =
  let is_appropriate_product expr = (match expr with
                                    | OpProduct prod_list -> 
                                        (List.exists (fun x ->( contains_Ovar x ident)) prod_list)
                                    | OpOutput_variable (identifier, SSVar in_ident) when identifier = ident && in_ident = input_ident -> true
                                    | _ -> false) in
  if (List.for_all is_appropriate_product sum_list) then OpProduct [OpOutput_variable (ident, SSVar input_ident); OpSum (List.map (fun x -> op_automatic_simplify (OpProduct [OpPow(OpOutput_variable (ident, SSVar input_ident), OpRational (Mpq.init_set_si (-1) 1)); x])) sum_list)]
  else raise (Isolating_exc ("OCRS was unable to factor " ^ (Expr_helpers.op_expr_to_string (OpSum sum_list))))
  ;;


let sum_contains_non_Ovar expr ident = 
  match expr with
  | OpSum sumList ->
    let (_, non_ovar_list) = List.partition (fun x -> contains_Ovar x ident) sumList in
    if List.length non_ovar_list = 0 then false
    else true
  | _ -> false
  ;;

let rec solve_for_Ovar_pair left right ident input_ident = 
  if (contains_Ovar left ident) && (contains_Ovar right ident) || (sum_contains_non_Ovar left ident) then
    let (new_left, new_right) = move_Ovar_left left right ident in   (* TODO this technique will not work in the case of inequalities, becuase the direction needs to flip *)
    solve_for_Ovar_pair new_left new_right ident input_ident
  else
    (match left with
    | OpOutput_variable (identifier, SSVar _) when identifier = ident ->
      (left, right)
    | OpProduct prod_list when (List.length (List.filter (fun x -> contains_Ovar x ident) prod_list)) = 1 ->
      let (ovar, non_ovar) = List.partition (fun x -> contains_Ovar x ident) prod_list in
      let non_ovar_inv = OpPow(OpProduct non_ovar, OpRational (Mpq.init_set_si (-1) 1)) in
      solve_for_Ovar_pair (op_automatic_simplify (OpProduct (List.append prod_list [non_ovar_inv]))) (op_automatic_simplify (OpProduct (right :: non_ovar_inv :: []))) ident input_ident
    | OpProduct _ -> raise (Isolating_exc ("OCRS is unable to solve " ^ (Expr_helpers.op_inequation_to_string (OpEquals (left, right)))))
    | OpSum sum_list when List.for_all (fun x -> contains_Ovar x ident) sum_list ->
      let new_left = factor_ovar sum_list ident input_ident in
      

      solve_for_Ovar_pair new_left right ident input_ident
    | OpSum _ ->
      raise (Isolating_exc ("OCRS is unable to solve " ^ (Expr_helpers.op_inequation_to_string (OpEquals (left, right)))))
    | _ -> raise (Isolating_exc ("OCRS is unable to solve " ^ (Expr_helpers.op_inequation_to_string (OpEquals (left, right)))))
    )


let solve_for_Ovar op_inequation ident input_ident = 
  match op_inequation with
  | OpEquals (left, right) ->
    let res = solve_for_Ovar_pair left right ident input_ident in
    OpEquals (fst res, snd res)
  | OpGreaterEq (left, right) ->
    let res = solve_for_Ovar_pair left right ident input_ident in
    OpGreaterEq (fst res, snd res)
  | OpGreater (left, right) ->
    let res = solve_for_Ovar_pair left right ident input_ident in
    OpGreater (fst res, snd res)
  | OpLess (left, right) ->
    let res = solve_for_Ovar_pair left right ident input_ident in
    OpLess (fst res, snd res)
  | OpLessEq (left, right) ->
    let res = solve_for_Ovar_pair left right ident input_ident in
    OpLessEq (fst res, snd res)
