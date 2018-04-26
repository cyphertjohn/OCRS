open Type_def

let rec subscript_to_string e = 
  match e with
  | SAdd (left, right) ->
    "{" ^ left ^ " + " ^ (string_of_int right) ^ "}"
  | SSDiv (str, index) ->
    "{" ^ str ^ "/" ^ (string_of_int index) ^ "}"
  | SSVar ident ->
    ident
  ;;

(* convert an expression to a string *)
let rec expr_to_string e =
  match e with
  | Plus (left, right) ->
      "(" ^ expr_to_string left ^ " + " ^ expr_to_string right ^ ")"
  | Minus (left, right) ->
      "(" ^ expr_to_string left ^ " - " ^ expr_to_string right ^ ")"
  | Times (left, right) ->
      "("  ^ expr_to_string left ^ " * " ^ expr_to_string right ^ ")"
  | Divide (left, right) ->
      "(" ^ expr_to_string left ^ " / " ^ expr_to_string right ^ ")"
  | Product expr_list ->
      "(" ^ (String.concat " * " (List.map expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with star *)
  | Sum expr_list ->
      "(" ^ (String.concat " + " (List.map expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with + *)
  | Symbolic_Constant ident ->
      ident
  | Base_case (ident, index) ->
      ident ^ "_" ^ (string_of_int index)
  | Output_variable (ident , subscript) ->
      ident ^ "_" ^ (subscript_to_string subscript)
  | Input_variable str ->
      str
  | Rational rat ->
      Mpq.to_string rat
  | Log (base, expression) ->
      "log" ^ (Mpq.to_string base) ^ "(" ^ expr_to_string expression ^ ")"
  | Pow (left, right) ->
      expr_to_string left ^ " ^ " ^ expr_to_string right			(* Since Power has top precedence don't think need parens *)
  | Binomial (top, bottom) ->
      "(" ^ expr_to_string top ^ " choose " ^ expr_to_string bottom ^ ")"
  | Factorial child ->
      (expr_to_string child) ^ "!"
  | IDivide (numerator, denom) ->
      "floor(" ^ expr_to_string numerator ^ " / " ^ Mpq.to_string denom ^ ")"
  | Sin inner_expr -> 
      "sin(" ^ expr_to_string inner_expr ^ ")"
  | Cos inner_expr -> 
      "cos(" ^ expr_to_string inner_expr ^ ")"
  | Arctan rat ->
      "arctan(" ^ Mpq.to_string rat ^ ")"
  | Mod (left, right) ->
      "(" ^ expr_to_string left ^ " mod " ^ expr_to_string right ^ ")"
  | Pi ->
      "pi"
  | Iif (op_expr_str, subscript) ->
    "f{"^ op_expr_str ^ "}(" ^ subscript_to_string subscript ^")"
  | Shift (shift_v, expression) ->
    if shift_v < 0 then "LeftShift(" ^ (string_of_int (shift_v * -1)) ^ ", " ^ (expr_to_string expression) ^ ")"
    else "RightShift(" ^ (string_of_int shift_v) ^ ", " ^ (expr_to_string expression) ^ ")"
  | Undefined ->
      "UNDEFINED"
  ;;

(* convert an inequation to a string *)
let inequation_to_string e =
  match e with
  | Equals (left, right) ->
      expr_to_string left ^ " == " ^ expr_to_string right
  | LessEq (left, right) ->
      expr_to_string left ^ " <= " ^ expr_to_string right
  | Less (left, right) ->
      expr_to_string left ^ " < " ^ expr_to_string right
  | GreaterEq (left, right) ->
      expr_to_string left ^ " >= " ^ expr_to_string right
  | Greater (left, right) ->
      expr_to_string left ^ " > " ^  expr_to_string right
  ;;


let rec get_right_left_constr ineqs =
  match ineqs with
  | [] -> ([], [], [])
  | ineq :: tl ->
    (match ineq with
    | Equals (left, right) ->
      let (lefts, rights, constrs) = get_right_left_constr tl in
      (left :: lefts, right :: rights, "==" :: constrs)
    | Less (left, right) ->
      let (lefts, rights, constrs) = get_right_left_constr tl in
      (left :: lefts, right :: rights, "<" :: constrs)
    | LessEq (left, right) ->
      let (lefts, rights, constrs) = get_right_left_constr tl in
      (left :: lefts, right :: rights, "<=" :: constrs)
    | Greater (left, right) ->
      let (lefts, rights, constrs) = get_right_left_constr tl in
      (left :: lefts, right :: rights, ">" :: constrs)
    | GreaterEq (left, right) ->
      let (lefts, rights, constrs) = get_right_left_constr tl in
      (left :: lefts, right :: rights, ">=" :: constrs)
    )
  ;;

let intervals_to_strings intervals ivar =
  let bounds_to_strings inter = 
    (match inter with
    | Bounded (lower, upper) -> (string_of_int lower, string_of_int upper)
    | BoundBelow (lower) -> (string_of_int lower, "inf")
    ) in
  let (lowers, uppers) = List.split (List.map bounds_to_strings intervals) in
  let lower_lens = List.map String.length lowers in
  let upper_lens = List.map String.length uppers in
  let length_of_biggest_lower = List.fold_left max 0 lower_lens in
  let length_of_biggest_upper = List.fold_left max 0 upper_lens in
  let lower_format_string = Scanf.format_from_string ("%-" ^ (string_of_int length_of_biggest_lower) ^ "s") "%s" in
  let upper_format_string = Scanf.format_from_string ("%" ^ (string_of_int length_of_biggest_upper) ^ "s") "%s" in
  let lower_strs_formatted = List.map (fun x -> Printf.sprintf lower_format_string x) lowers in
  let upper_strs_formatted = List.map (fun x -> Printf.sprintf upper_format_string x) uppers in
  List.map2 (fun a b -> (a ^ " <= " ^ ivar ^ " <= " ^ b)) lower_strs_formatted upper_strs_formatted
  ;;

let piece_to_string piece = 
  match piece with
  | PieceWiseIneq (ivar, intervals_ineqs) ->
    let (intervals, ineqs) = List.split intervals_ineqs in
    let (lefts, rights, constrs) = get_right_left_constr ineqs in
    let left_strs = List.map expr_to_string lefts in
    let right_strs = List.map expr_to_string rights in
    let inter_strs = intervals_to_strings intervals ivar in
    let lefts_and_constrs = List.map2 (fun a b -> a ^ " " ^ b) left_strs constrs in
   (* let len_of_left_and_constr = List.fold_left max 0 (List.map String.length lefts_and_constrs) in
    *)
    let build_piece_part left_constr_str right_str inter_str =
      "{ " ^ inter_str ^ "    =>    " ^ left_constr_str ^ " " ^ right_str ^ " }"
    in
    let rec get_strings lefts_constrs r_strs int_strs = 
      (match (lefts_constrs, r_strs, int_strs) with
      | ([],[],[]) -> []
      | (left_constr_str :: ltl, right_str :: rtl, inter_str :: itl) -> (build_piece_part left_constr_str right_str inter_str) :: (get_strings ltl rtl itl)
      | _ -> failwith "this case shouldn't happen"
      )
    in
    let lines = get_strings lefts_and_constrs right_strs inter_strs in
    String.concat "\n" lines
  ;;


(*
  | PieceWise pieceList ->
    let interval_expr_to_string interval_expr = 
      let interval = fst interval_expr in
      let expr_str = expr_to_string (snd interval_expr) in
      let lower_str = string_of_int (fst interval) in
      let upper_str = if (snd interval) = (-1) then "inf" else (string_of_int (snd interval)) in
      expr_str ^ " if " ^  lower_str ^ " <= n <= " ^ upper_str
    in
    "{" ^ (String.concat " : " (List.map interval_expr_to_string pieceList)) ^ "}" 
*)

let rec op_expr_to_string e =
  match e with
  | OpPlus (left, right) ->
      "(" ^ op_expr_to_string left ^ " + " ^ op_expr_to_string right ^ ")"
  | OpMinus (left, right) ->
      "(" ^ op_expr_to_string left ^ " - " ^ op_expr_to_string right ^ ")"
  | OpTimes (left, right) ->
      "("  ^ op_expr_to_string left ^ " * " ^ op_expr_to_string right ^ ")"
  | OpDivide (left, right) ->
      "(" ^ op_expr_to_string left ^ " / " ^ op_expr_to_string right ^ ")"
  | OpProduct expr_list ->
      "(" ^ (String.concat " * " (List.map op_expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with star *)
  | OpSum expr_list ->
      "(" ^ (String.concat " + " (List.map op_expr_to_string expr_list)) ^ ")"     (* convert all list elem to strings concat with + *)
  | OpSymbolic_Constant ident ->
      ident
  | OpBase_case (ident, index) ->
      ident ^ "_" ^ (string_of_int index)
  | OpOutput_variable (ident , subscript) ->
      ident ^ "_" ^ (subscript_to_string subscript)
  | OpInput_variable str ->
      str
  | OpRational rat ->
      Mpq.to_string rat
  | OpLog (b, expression) ->
      "Oplog" ^ (Mpq.to_string b) ^ "(" ^ op_expr_to_string expression ^ ")"
  | OpPow (left, right) ->
      op_expr_to_string left ^ " ^ " ^ op_expr_to_string right                        (* Since Power has top precedence don't think need parens *)
  | Q ->
      "q"
  | OpUndefined ->
      "OPUNDEFINED"
  | SymBinom (top, bottom) ->
      "(" ^ op_expr_to_string top ^ " choose " ^ op_expr_to_string bottom ^ ")"
  | SymIDivide (numerator, denom) ->
      "floor(" ^ op_expr_to_string numerator ^ " / " ^ Mpq.to_string denom ^ ")"
  | SymSin inner_expr -> 
      "sin(" ^ op_expr_to_string inner_expr ^ ")"
  | SymCos inner_expr -> 
      "cos(" ^ op_expr_to_string inner_expr ^ ")"
  | OpArctan rat ->
      "arctan(" ^ Mpq.to_string rat ^ ")"
  | SymMod (left, right) ->
      "(" ^ op_expr_to_string left ^ " mod " ^ op_expr_to_string right ^ ")"
  | OpPi ->
      "pi"
  ;;

(* convert an inequation to a string *)
let op_inequation_to_string e =
  match e with
  | OpEquals (left, right) ->
      op_expr_to_string left ^ " == " ^ op_expr_to_string right
  | OpLessEq (left, right) ->
      op_expr_to_string left ^ " <= " ^ op_expr_to_string right
  | OpLess (left, right) ->
      op_expr_to_string left ^ " < " ^ op_expr_to_string right
  | OpGreaterEq (left, right) ->
      op_expr_to_string left ^ " >= " ^ op_expr_to_string right
  | OpGreater (left, right) ->
      op_expr_to_string left ^ " > " ^ op_expr_to_string right
  ;;


let rec op_expr_to_string_IR e =
  match e with
  | OpPlus (left, right) ->
      "OpPlus (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpMinus (left, right) ->
      "OpMinus (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpTimes (left, right) ->
      "OpTimes (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpDivide (left, right) ->
      "OpDivide (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpProduct expr_list ->
      "OpProduct [" ^ (String.concat "; " (List.map op_expr_to_string_IR expr_list))^ "]"
  | OpSum expr_list ->
      "OpSum [" ^ (String.concat "; " (List.map op_expr_to_string_IR expr_list))^ "]"
  | OpSymbolic_Constant ident ->
      "OpSymbolic_Constant (" ^ ident ^ ")"
  | OpBase_case (ident, index) ->
      "OpBase_case (" ^ ident ^ ", " ^ string_of_int index ^ ")"
  | OpOutput_variable (ident , subscript) ->
      "OpOutput_variable (" ^ ident ^ ", " ^ (subscript_to_string subscript) ^ ")"
  | OpInput_variable str ->
      "OpInput_variable (" ^ str ^ ")"
  | OpRational rat ->
      "OpRational (" ^ (Mpq.to_string rat) ^ ")"
  | OpLog (b, expression) ->
      "OpLog" ^ (Mpq.to_string b) ^ "(" ^ (op_expr_to_string_IR expression)^ ")"
  | OpPow (left, right) ->
      "OpPow (" ^ (op_expr_to_string_IR left) ^ ", " ^ (op_expr_to_string_IR right) ^ ")"
  | Q ->
      "Q"
  | OpUndefined ->
      "OPUNDEFINED"
  | SymBinom (top, bottom) ->
      "SymBinom (" ^ op_expr_to_string_IR top ^ ", " ^ op_expr_to_string_IR bottom ^ ")"
  | SymIDivide (numerator, denom) ->
      "SymIDivide (" ^ op_expr_to_string_IR numerator ^ ", " ^ Mpq.to_string denom ^ ")"
  | SymSin inner_expr -> 
      "SymSin (" ^ op_expr_to_string_IR inner_expr ^ ")"
  | SymCos inner_expr -> 
      "SymCos (" ^ op_expr_to_string_IR inner_expr ^ ")"
  | OpArctan rat ->
      "OpArctan (" ^ Mpq.to_string rat ^ ")"
  | SymMod (left, right) ->
      "SymMod (" ^ op_expr_to_string left ^ ", " ^ op_expr_to_string right ^ ")"
  | OpPi ->
      "OpPi"
  ;;

(* convert an inequation to a string *)
let op_inequation_to_string_IR e =
  match e with
  | OpEquals (left, right) ->
      "OpEquals (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpLessEq (left, right) ->
      "OpLessEq (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpLess (left, right) ->
      "OpLess (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpGreaterEq (left, right) ->
      "OpGreaterEq (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  | OpGreater (left, right) ->
      "OpGreater (" ^ op_expr_to_string_IR left ^ ", " ^ op_expr_to_string_IR right ^ ")"
  ;;


let rec subscript_to_string_IR s = 
  match s with
  | SSVar ident -> "SSVar (" ^ ident ^ ")"
  | SSDiv (ident, beta) -> "SSDiv (" ^ ident ^ ", " ^ (string_of_int beta) ^ ")"
  | SAdd (ident, beta) -> "SAdd (" ^ ident ^ ", " ^ (string_of_int beta) ^ ")"

let rec expr_to_string_IR e =
  match e with
  | Plus (left, right) ->
      "Plus (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Minus (left, right) ->
      "Minus (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Times (left, right) ->
      "Times (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Divide (left, right) ->
      "Divide (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Product expr_list ->
      "Product [" ^ (String.concat "; " (List.map expr_to_string_IR expr_list))^ "]"
  | Sum expr_list ->
      "Sum [" ^ (String.concat "; " (List.map expr_to_string_IR expr_list))^ "]"
  | Symbolic_Constant ident ->
      "Symbolic_Constant (" ^ ident ^ ")"
  | Base_case (ident, index) ->
      "Base_case (" ^ ident ^ ", " ^ string_of_int index ^ ")"
  | Output_variable (ident , subscript) ->
      "Output_variable (" ^ ident ^ ", " ^ (subscript_to_string_IR subscript) ^ ")"
  | Input_variable str ->
      "Input_variable (" ^ str ^ ")"
  | Rational rat ->
      "Rational (" ^ (Mpq.to_string rat) ^ ")"
  | Binomial (top, bottom) ->
      "Binomial (" ^ expr_to_string_IR top ^ ", " ^ expr_to_string_IR bottom ^ ")"
  | Factorial child ->
      "Factorial (" ^ (expr_to_string_IR child) ^ ")"
  | Log (base, expression) ->
      "Log (" ^ (Mpq.to_string base) ^ ", " ^ (expr_to_string_IR expression)^ ")"
  | Pow (left, right) ->
      "Pow (" ^ (expr_to_string_IR left) ^ ", " ^ (expr_to_string_IR right) ^ ")"
  | Undefined ->
      "UNDEFINED"
  | IDivide (numerator, denom) ->
      "IDivide (" ^ expr_to_string_IR numerator ^ ", " ^ Mpq.to_string denom ^ ")"
  | Sin inner_expr -> 
      "Sin (" ^ expr_to_string_IR inner_expr ^ ")"
  | Cos inner_expr -> 
      "Cos (" ^ expr_to_string_IR inner_expr ^ ")"
  | Arctan rat ->
      "Arctan (" ^ Mpq.to_string rat ^ ")"
  | Mod (left, right) ->
      "Mod (" ^ expr_to_string left ^ ", " ^ expr_to_string right ^ ")"
  | Iif (op_expr_str, subscript) ->
      "Iif (" ^ op_expr_str ^ ", " ^ (subscript_to_string_IR subscript) ^ ")"
  | Shift (shift_v, expression) ->
    if shift_v < 0 then "LeftShift(" ^ (string_of_int (shift_v * -1)) ^ ", " ^ (expr_to_string expression) ^ ")"
    else "RightShift(" ^ (string_of_int shift_v) ^ ", " ^ (expr_to_string expression) ^ ")"
  | Pi ->
      "Pi"
  ;;

(* convert an inequation to a string *)
let inequation_to_string_IR e =
  match e with
  | Equals (left, right) ->
      "Equals (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | LessEq (left, right) ->
      "LessEq (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Less (left, right) ->
      "Less (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | GreaterEq (left, right) ->
      "GreaterEq (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  | Greater (left, right) ->
      "Greater (" ^ expr_to_string_IR left ^ ", " ^ expr_to_string_IR right ^ ")"
  ;;

let rec is_const expr ivar_ident =
  match expr with
  | Rational _ | Base_case _ | Symbolic_Constant _ | Pi | Arctan _ ->
    true
  | Output_variable _ | Input_variable _ | Undefined -> false
  | Pow (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Times (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Product prod_list ->
    List.for_all (fun x -> is_const x ivar_ident) prod_list
  | Plus (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Sum sum_list ->
    List.for_all (fun x -> is_const x ivar_ident) sum_list
  | Divide (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Minus (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Log (base, expression) ->
    is_const expression ivar_ident
  | Binomial (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Factorial expression ->
    is_const expression ivar_ident
  | IDivide (num, _) ->
    is_const num ivar_ident
  | Sin inner_expr ->
    is_const inner_expr ivar_ident
  | Cos inner_expr ->
    is_const inner_expr ivar_ident
  | Mod (left, right) ->
    (is_const left ivar_ident) && (is_const right ivar_ident)
  | Shift (_, expression) -> is_const expression ivar_ident
  | Iif (_, sub) ->
    (match sub with
    | SAdd (ident, _) when ident = ivar_ident -> false
    | SSVar ident when ident = ivar_ident -> false
    | _ -> true
    )
  ;;


let rec substitute_expr expr old_term new_term = 
  if expr = old_term then new_term
  else
    (match expr with
    | Rational _ | Symbolic_Constant _ | Base_case _ | Undefined | Input_variable _ | Output_variable _ | Arctan _ | Pi ->
      expr
    | Pow (base, exp) ->
      Pow (substitute_expr base old_term new_term, substitute_expr exp old_term new_term)
    | Times (left, right) ->
      Times (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Plus (left, right) ->
      Plus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Minus (left, right) ->
      Minus (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Divide (left, right) ->
      Divide (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Binomial (left, right) ->
      Binomial (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Log (base, expression) ->
      Log (base, substitute_expr expression old_term new_term)
    | Factorial expression ->
      Factorial (substitute_expr expression old_term new_term)
    | Product prodList ->
      Product (List.map (fun x -> substitute_expr x old_term new_term) prodList)
    | Sum sumList ->
      Sum (List.map (fun x -> substitute_expr x old_term new_term) sumList)
    | IDivide (numerator, denom) ->
      IDivide (substitute_expr numerator old_term new_term, denom)
    | Sin inner_expr ->
      Sin (substitute_expr inner_expr old_term new_term)
    | Cos inner_expr ->
      Cos (substitute_expr inner_expr old_term new_term)
    | Mod (left, right) ->
      Mod (substitute_expr left old_term new_term, substitute_expr right old_term new_term)
    | Shift (shift_v, inner_expr) ->
      Shift (shift_v, substitute_expr inner_expr old_term new_term)
    | Iif (opCalcString, subscript) ->
      let new_term_as_subscript expression = 
        let simp_expression = Expr_simplifications.automatic_simplify expression in
        (match simp_expression with
        | Sum ((Rational add_term) :: (Input_variable ident) :: []) | Sum ((Input_variable ident) :: (Rational add_term) :: []) | Sum ((Rational add_term) :: (Symbolic_Constant ident) :: []) | Sum ((Symbolic_Constant ident) :: (Rational add_term) :: []) ->
          let (num, denom) = (Mpz.init (), Mpz.init ()) in
          let _ = Mpq.get_num num add_term in
          let num_int = Mpz.get_int num in
          let _ = Mpq.get_den denom add_term in
          if (Mpz.cmp_si denom 1) = 0 then SAdd (ident, num_int)
          else failwith "trying to shift by a non-integral value"
        | Input_variable ident | Symbolic_Constant ident -> SSVar ident
        | _ -> failwith "this expression can't be turned into a subscript"
        )        
      in
      (match subscript with
      | SAdd (identifier, add_int) ->
        let (sub_as_sym, sub_as_input) = (Expr_simplifications.automatic_simplify (Plus(Symbolic_Constant identifier, Rational (Mpq.init_set_si add_int 1))), Expr_simplifications.automatic_simplify (Plus(Input_variable identifier, Rational (Mpq.init_set_si add_int 1)))) in
        if expr_order sub_as_sym old_term = 0 || expr_order sub_as_input old_term = 0 then (
          let new_sub = new_term_as_subscript new_term in
          Iif (opCalcString, new_sub)
        ) else (
          if expr_order (Input_variable identifier) old_term = 0 || expr_order (Symbolic_Constant identifier) old_term = 0 then (
            let new_sub = new_term_as_subscript new_term in
            (match new_sub with
            | SAdd (new_ident, add_v) -> Iif (opCalcString, (SAdd (new_ident, add_v + add_int)))
            | SSVar new_ident -> Iif (opCalcString, (SAdd (new_ident, add_int)))
            | _ -> failwith "this will never happen"
            )
          ) else expr
        )
      | SSVar identifier ->
        let (sub_as_sym, sub_as_input) = (Symbolic_Constant identifier, Input_variable identifier) in
        if expr_order sub_as_sym old_term = 0 || expr_order sub_as_input old_term = 0 then (
          let new_sub = new_term_as_subscript new_term in
          Iif (opCalcString, new_sub)
        ) else expr
      | SSDiv _ -> failwith "this case is not applied to IIFs"
      )
    )
  ;;


let substitute ineq old_term new_term = 
  match ineq with
  | Equals (left, right) ->
    Equals(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Less (left, right) ->
    Less(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | LessEq (left, right) ->
    LessEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | Greater (left, right) ->
    Greater(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  | GreaterEq (left, right) ->
    GreaterEq(substitute_expr left old_term new_term, substitute_expr right old_term new_term)
  ;;


let rec remove_dup lst = 
  match lst with
  | [] -> []
  | h::t -> h::(remove_dup (List.filter (fun x -> x<>h) t))
  ;;

let rec find_ovar_ivar_expr expr = 
  match expr with
  | Rational _ | Symbolic_Constant _ | Base_case _ | Arctan _ | Pi | Iif _ | Undefined ->
    ([], [])
  | Output_variable (ovar_ident, subscript) ->
    (match subscript with 
    | SAdd (ivar_ident, _) | SSDiv (ivar_ident, _) -> (ovar_ident :: [], ivar_ident :: [])
    | SSVar ivar_ident -> (ovar_ident :: [], ivar_ident :: []))
  | Input_variable ivar_ident -> ([], ivar_ident :: [])
  | Pow (base, exp) ->
    let base_res = find_ovar_ivar_expr base in
    let exp_res = find_ovar_ivar_expr exp in
    (remove_dup ((fst base_res) @ (fst exp_res)), remove_dup ((snd base_res) @ (snd exp_res)))
  | Times (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | Plus (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | Product prodList ->
    let list_res = List.map find_ovar_ivar_expr prodList in
    let rec aux lst acc = 
      (match lst with
      | [] -> acc
      | (ovar, ivar) :: [] -> (remove_dup ((fst acc) @ ovar), remove_dup ((snd acc) @ ivar))
      | hd :: tl -> 
        let new_acc = ((fst acc) @ (fst hd), (snd acc) @ (snd hd)) in
        aux tl new_acc) in
    aux list_res ([], []) 
  | Sum sumList ->
    let list_res = List.map find_ovar_ivar_expr sumList in
    let rec aux lst acc = 
      (match lst with
      | [] -> acc
      | (ovar, ivar) :: [] -> (remove_dup ((fst acc) @ ovar), remove_dup ((snd acc) @ ivar))
      | hd :: tl -> 
        let new_acc = ((fst acc) @ (fst hd), (snd acc) @ (snd hd)) in
        aux tl new_acc) in
    aux list_res ([], [])
  | Divide (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | Minus (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | Log (_, expr) ->
    find_ovar_ivar_expr expr
  | Factorial expr ->
    find_ovar_ivar_expr expr
  | Binomial (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | IDivide (numerator, _) ->
    find_ovar_ivar_expr numerator
  | Sin inner_expr ->
    find_ovar_ivar_expr inner_expr
  | Cos inner_expr ->
    find_ovar_ivar_expr inner_expr
  | Mod (left, right) ->
    let left_res = find_ovar_ivar_expr left in
    let right_res = find_ovar_ivar_expr right in
    (remove_dup ((fst left_res) @ (fst right_res)), remove_dup ((snd left_res) @ (snd right_res)))
  | Shift (shift_v, expression) ->
    find_ovar_ivar_expr expression
  ;;
      
let find_ovar_ivar ineq = 
  (match ineq with
  | Equals (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | Less (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | LessEq (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | Greater (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list)))
  | GreaterEq (left, right) ->
    let left_list = find_ovar_ivar_expr left in
    let right_list = find_ovar_ivar_expr right in
    (remove_dup ((fst left_list) @ (fst right_list)), remove_dup ((snd left_list) @ (snd right_list))))
  ;;
  
