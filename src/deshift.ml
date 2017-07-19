open Type_def

let rec remove_left_shifts expr = 
  match expr with
  | Symbolic_Constant _ | Base_case _ | Output_variable _ | Input_variable _ | Rational _ | Arctan _ | Pi | Iif _ | Undefined -> 
    expr
  | Plus (left, right) ->
    Plus (remove_left_shifts left, remove_left_shifts right)
  | Minus (left, right) ->
    Minus (remove_left_shifts left, remove_left_shifts right)
  | Times (left, right) ->
    Times (remove_left_shifts left, remove_left_shifts right)
  | Divide (left, right) -> 
    Divide (remove_left_shifts left, remove_left_shifts right)
  | Product prodList ->
    Product (List.map remove_left_shifts prodList)
  | Sum sumList ->
    Sum (List.map remove_left_shifts sumList)
  | Log (b, expression) ->
    Log (b, remove_left_shifts expression)
  | Pow (base, exp) ->
    Pow (remove_left_shifts base, remove_left_shifts exp)
  | Binomial (left, right) ->
    Binomial (remove_left_shifts left, remove_left_shifts right)
  | IDivide (expression, integer) ->
    IDivide (remove_left_shifts expression, integer)
  | Sin (expression) ->
    Sin (remove_left_shifts expression)
  | Cos (expression) ->
    Cos (remove_left_shifts expression)
  | Mod (left, right) ->
    Mod (remove_left_shifts left, remove_left_shifts right)
  | Factorial (expression) ->
    Factorial (remove_left_shifts expression)
  | Shift (shift_v, Iif (str, subscript)) ->
    let new_subscript = 
      (match subscript with
      | SAdd (ident, value) -> SAdd (ident, value + 1)
      | SSVar (ident) -> SAdd (ident, 1)
      | _ -> failwith "Can't shift a SSDidv"
      )
    in
    Iif (str, new_subscript)
  | Shift (shift_v, inner_expr) when shift_v < 0 ->
    (*
    Expr_simplifications.automatic_simplify (Expr_helpers.substitute inner_expr )*)
    failwith "Potentially shifting a bad sequence"  
  | _ -> expr
  ;;

let sort_and_remove_duplicates l = 
  let rec remove_dups lst = 
    (match lst with
    | [] -> []
    | h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t))) in
  List.sort compare (remove_dups l)
  ;;


let rec get_break_points expr = 
  match expr with                                                                        
  | Symbolic_Constant _ | Base_case _ | Output_variable _ | Input_variable _ | Rational _ | Arctan _ | Pi | Iif _ | Undefined ->  
    []  
  | Plus (left, right) -> 
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | Minus (left, right) ->
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | Times (left, right) ->                                                               
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | Divide (left, right) -> 
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | Product prodList ->
    let break_points = List.map get_break_points prodList in
    sort_and_remove_duplicates (List.concat break_points)
  | Sum sumList ->
    let break_points = List.map get_break_points sumList in
    sort_and_remove_duplicates (List.concat break_points)
  | Log (b, expression) ->
    get_break_points expression
  | Pow (base, exp) ->
    sort_and_remove_duplicates ((get_break_points base) @ (get_break_points exp))
  | Binomial (left, right) ->
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | IDivide (expression, integer) ->    
    get_break_points expression
  | Sin (expression) ->
    get_break_points expression
  | Cos (expression) ->                 
    get_break_points expression
  | Mod (left, right) ->
    sort_and_remove_duplicates ((get_break_points left) @ (get_break_points right))
  | Factorial (expression) ->
    get_break_points expression
  | Shift (shift_v, inner_expr) ->
    sort_and_remove_duplicates ([shift_v] @ (get_break_points inner_expr))
  ;;

let deshift left_expr right_expr const input_ident =
  let no_left_shifts = remove_left_shifts right_expr in
  let break_points = get_break_points no_left_shifts in
(*  if (List.length break_points) = 0 then (
    match const with
    | "=" -> Equals(left_expr, no_left_shifts)
    | "<=" -> LessEq(left_expr, no_left_shifts)
    | "<" -> Less(left_expr, no_left_shifts)
    | ">=" -> GreaterEq(left_expr, no_left_shifts)
    | ">" -> Greater(left_expr, no_left_shifts)
    | _ -> failwith "there are no other cases"
  ) else ( *)
    let get_intervals int_list = 
      let rec aux acc lst curr = 
        (match lst with
        | [] -> (curr, -1) :: acc
        | hd :: tl -> aux ((curr, hd - 1) :: acc) tl hd
        ) in
      List.rev (aux [] int_list 0) in
    let intervals = get_intervals break_points in
    let rec remove_shifts expr interval = 
      (match expr with
      | Symbolic_Constant _ | Base_case _ | Output_variable _ | Input_variable _ | Rational _ | Arctan _ | Pi | Iif _ | Undefined ->
        expr
      | Plus (left, right) ->
        Plus (remove_shifts left interval, remove_shifts right interval)
      | Minus (left, right) ->
        Minus (remove_shifts left interval, remove_shifts right interval)
      | Times (left, right) ->
        Times (remove_shifts left interval, remove_shifts right interval)
      | Divide (left, right) ->
        Divide (remove_shifts left interval, remove_shifts right interval)
      | Product prodList ->
        Product (List.map (fun x -> remove_shifts x interval) prodList)
      | Sum sumList ->
        Sum (List.map (fun x -> remove_shifts x interval) sumList)
      | Log (b, expression) ->
        Log (b, remove_shifts expression interval)
      | Pow (base, exp) ->
        Pow (remove_shifts base interval, remove_shifts exp interval)
      | Binomial (left, right) ->
        Binomial (remove_shifts left interval, remove_shifts right interval)
      | IDivide (expression, integer) ->
        IDivide (remove_shifts expression interval, integer)
      | Sin (expression) ->
        Sin (remove_shifts expression interval)
      | Cos (expression) ->
        Cos (remove_shifts expression interval)
      | Mod (left, right) ->
        Mod (remove_shifts left interval, remove_shifts right interval)
      | Factorial (expression) ->
        Factorial (remove_shifts expression interval)
      | Shift (shift_v, inner_expr) ->
        let inner_expr = remove_shifts inner_expr interval in
        if (shift_v > snd interval) && (snd interval) <> (-1) then Rational (Mpq.init_set_si 0 1)
        else (
          let new_term = Expr_simplifications.automatic_simplify (Plus(Input_variable input_ident, Times(Rational (Mpq.init_set_si (-1) 1), Rational (Mpq.init_set_si shift_v 1)))) in
          Expr_helpers.substitute_expr inner_expr (Input_variable input_ident) new_term
        )
      )
    in
    let new_funcs = List.map (fun x -> Expr_simplifications.automatic_simplify (remove_shifts no_left_shifts x)) intervals in
    let rec get_intervals_type inter = 
      (match inter with
      | [] -> []
      | hd :: tl -> 
        let new_hd = (match hd with
                     | (lower, upper) when upper = (-1) -> BoundBelow (lower) 
                     | (lower, upper) -> Bounded (lower, upper)
                     ) in
        new_hd :: (get_intervals_type tl)
      ) in
    let new_intervals = get_intervals_type intervals in
    let (_, ivars) = Expr_helpers.find_ovar_ivar_expr left_expr in
    if (List.length ivars <> 1) then (
      let _ = List.iter print_endline ivars in
      failwith "this function depends on multiple variables"
    ) else (
      let ivar = List.nth ivars 0 in
      (match const with
        | "=" -> 
          let new_ineqs = List.map (fun x -> Equals(left_expr, x)) new_funcs in
          PieceWise (ivar, (List.combine new_intervals new_ineqs))
        | "<=" ->
          let new_ineqs = List.map (fun x -> LessEq(left_expr, x)) new_funcs in
          PieceWise (ivar, (List.combine new_intervals new_ineqs))
        | "<" -> 
          let new_ineqs = List.map (fun x -> Less(left_expr, x)) new_funcs in
          PieceWise (ivar, (List.combine new_intervals new_ineqs))
        | ">=" ->
          let new_ineqs = List.map (fun x -> GreaterEq(left_expr, x)) new_funcs in
          PieceWise (ivar, (List.combine new_intervals new_ineqs))
        | ">" -> 
          let new_ineqs = List.map (fun x -> Greater(left_expr, x)) new_funcs in
          PieceWise (ivar, (List.combine new_intervals new_ineqs))
        | _ -> failwith "there are no other cases"
      )
    )
  ;;

let deshift_ineq ineq = 
  let (_, ivars) = Expr_helpers.find_ovar_ivar ineq in
  if (List.length ivars) <> 1 then failwith "deshifting multivariate"
  else (
    let input_ident = List.nth ivars 0 in
    (match ineq with
    | Equals (left, right) ->
      deshift left right "=" input_ident
    | LessEq (left, right) ->
      deshift left right "<=" input_ident
    | Less (left, right) ->
      deshift left right "<" input_ident
    | GreaterEq (left, right) ->
      deshift left right ">=" input_ident
    | Greater (left, right) ->
      deshift left right ">" input_ident
    )
  )
  ;;
