open Type_def
open Op_simplifications

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
  | OpSymbolic_Constant _ ->
      false
  | OpBase_case (_, _) ->
      false
  | OpOutput_variable (ident , subscript) ->
      if ident = identifier then true
      else false
  | OpInput_variable str ->
      false
  | OpRational rat ->
      false
  | OpLog expression ->
      contains_Ovar expression identifier
  | OpPow (left, right) ->
      (contains_Ovar left identifier) || (contains_Ovar right identifier)
  | Q ->
      false
  | OpUndefined ->
      false
  ;;

let rec move_Ovar_left left right identifier = 
  match (left, right) with
  | (OpSum left_list, OpSum right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum left_list; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]]) in	(* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum right_list; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (OpSum left_list, _) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) (right :: []) in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum left_list; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum [right]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (_, OpSum right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) (left :: []) in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 0 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpSum [OpSum [left]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpSum [OpSum right_list; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum non_ovar_left]; OpProduct [OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); OpSum ovar_right]]) in
      (new_left_simp, new_right_simp)
  | (OpProduct left_list, OpProduct right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct left_list; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct right_list; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | (OpProduct left_list, _) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) left_list in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) (right :: []) in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct left_list; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct [right]; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | (_, OpProduct right_list) ->
      let (_, non_ovar_left_temp) = List.partition (fun x -> contains_Ovar x identifier) (left :: []) in
      let (ovar_right_temp, _) = List.partition (fun x -> contains_Ovar x identifier) right_list in
      let non_ovar_left = (if (List.length non_ovar_left_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else non_ovar_left_temp) in
      let ovar_right = (if (List.length ovar_right_temp) = 0 then [OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))] else ovar_right_temp) in
      let new_left_simp = op_automatic_simplify (OpProduct [OpProduct [left]; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      let new_right_simp = op_automatic_simplify (OpProduct [OpProduct right_list; OpPow (OpProduct ovar_right, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); OpPow (OpProduct non_ovar_left, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near)))]) in (* sanity check: non_ovar_left should cancel *)
      (new_left_simp, new_right_simp)
  | _ -> failwith "haven't done any other types of transforms"
  ;;

let factor_ovar sum_list ident input_ident =
  let is_appropriate_product expr = (match expr with
                                    | OpProduct prod_list -> 
                                        (List.exists (fun x ->( contains_Ovar x ident)) prod_list)
                                    | OpOutput_variable (identifier, SSVar in_ident) when identifier = ident && in_ident = input_ident -> true
                                    | _ -> false) in
  (if (List.for_all is_appropriate_product sum_list) then OpProduct [OpOutput_variable (ident, SSVar input_ident); OpSum (List.map (fun x -> op_automatic_simplify (OpProduct [OpPow(OpOutput_variable (ident, SSVar input_ident), OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))); x])) sum_list)]
  else failwith "haven't implemented this yet")
  ;;

let rec solve_for_Ovar op_inequation ident input_ident = 
  match op_inequation with
  | OpEquals (left, right) ->
      (if (contains_Ovar left ident) && (contains_Ovar right ident) then
          let (new_left, new_right) = move_Ovar_left left right ident in   (* TODO this technique will not work in the case of inequalities, becuase the direction needs to flip *)
          solve_for_Ovar (OpEquals (new_left, new_right)) ident input_ident
      else
          (match left with
          | OpOutput_variable (identifier, SSVar _) when identifier = ident ->
              OpEquals (left, right)
          | OpProduct prod_list when (List.length (List.filter (fun x -> contains_Ovar x ident) prod_list)) = 1 ->
              let (ovar, non_ovar) = List.partition (fun x -> contains_Ovar x ident) prod_list in
              let non_ovar_inv = OpPow(OpProduct non_ovar, OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))) in
              solve_for_Ovar (op_automatic_simplify_inequation (OpEquals(OpProduct (List.append prod_list [non_ovar_inv]), OpProduct (right :: non_ovar_inv :: [])))) ident input_ident
          | OpProduct _ -> failwith "don't think this should happen"

          | OpSum sum_list when List.for_all (fun x -> contains_Ovar x ident) sum_list ->
              let new_left = factor_ovar sum_list ident input_ident in
              solve_for_Ovar (OpEquals (new_left, right)) ident input_ident
          | OpSum _ ->
              failwith "don't think we should ever get here"
          | _ -> failwith "haven't implemented solving for other functions"
          ))
  | _ -> failwith "Only handle equals right now"
