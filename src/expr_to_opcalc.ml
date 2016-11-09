open Type_def


(* need to check to make sure the transform is possible namely pointwise multiplication and pointwise divide *)

(* This function is incomplete!!! doesn't tranform other functions such as polynomials
   Also assumes all output variables are n or higher *)
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
      OpProduct (List.map expr_to_opCalc expr_list)  					(* convert all list elem to strings concat with star *)
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
           (* input in incorrect form panic *)
	   failwith "input was in incorrect form"
       )
  | Input_variable str ->
      expr_to_opCalc (Binomial(expr, (Rational (snd (Mpfr.init_set_si 1 Mpfr.Near)))))
  | Rational rat ->
      OpRational rat
  | Log expression ->
      failwith "haven't done this part yet"
      (* don't know what to do here *)
  | Pow (left, right) ->
      failwith "haven't done this part yet"
      (* don't know what to do here either *)
  | Binomial (top, bottom) ->
      (match (top, bottom) with
          | (Input_variable ident, Rational k) when (Mpfr.integer_p k) ->	(* if the binomial is of the form n choose k, where k is a constant int *)
              let _ = Mpfr.neg k k Mpfr.Near in
              OpPow (OpMinus (Q, OpRational (snd (Mpfr.init_set_si 1 Mpfr.Near))), OpRational k)		(* appropriate transformation *)
          | _ ->
      	      failwith "Bad binomial input"
      )
  | Base_case (ident, index) ->
      OpBase_case (ident, index)
  | Factorial child ->
      failwith "haven't done this part yet"
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

