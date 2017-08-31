(** This module contains functions to take in a piece-wise function and add shifts to it to create a single expression *)
open Type_def

(** Shift an expression where the string is within the two integers to the expression *)
let shift_expr unsimp_expr lower upper identifier =
  let expr = Expr_simplifications.automatic_simplify unsimp_expr in
  if lower = 0 then (
    if upper = -1 then expr
    else (
      Expr_simplifications.automatic_simplify (Minus (expr, Shift(upper + 1, Expr_helpers.substitute_expr expr (Input_variable identifier) (Expr_simplifications.automatic_simplify (Plus (Input_variable identifier, Rational (Mpq.init_set_si (upper+1) 1)))))))
    )
  ) else (
    if upper = -1 then Expr_simplifications.automatic_simplify (Shift(lower, Expr_helpers.substitute_expr expr (Input_variable identifier) (Expr_simplifications.automatic_simplify (Plus (Input_variable identifier, Rational (Mpq.init_set_si lower 1))))))
    else (
      let left = Shift(lower, Expr_helpers.substitute_expr expr (Input_variable identifier) (Expr_simplifications.automatic_simplify (Plus (Input_variable identifier, Rational (Mpq.init_set_si lower 1))))) in
      let right = Shift(upper + 1, Expr_helpers.substitute_expr expr (Input_variable identifier) (Expr_simplifications.automatic_simplify (Plus (Input_variable identifier, Rational (Mpq.init_set_si (upper + 1) 1))))) in 
      Expr_simplifications.automatic_simplify (Minus(left, right))
    )
  )
  ;;

(** Take an interval and produce a piar. Infinity is represented by -1. *)
let interval_to_pair interv = 
  match interv with
  | Bounded (lo, hi) -> (lo, hi)
  | BoundBelow value -> (value, -1)
  ;;

(** Shift a piece-wise expression *)
let shift_piece_expr piecewise =
  match piecewise with
  | PieceWiseExpr (identifier, inter_expr_list) ->
    let (intervals, exprs) = List.split inter_expr_list in
    let inter_pairs = List.map interval_to_pair intervals in
    let new_exprs = List.map2 (fun a b -> shift_expr a (fst b) (snd b) identifier) exprs inter_pairs in
    Expr_simplifications.automatic_simplify (Sum new_exprs)
  ;;

(** Shift a piece-wise inequation *)
let shift_piece_ineq piecewise =
  match piecewise with
  | PieceWiseIneq (identifier, inter_ineq_list) ->
    let (intervals, ineqs) = List.split inter_ineq_list in
    let inter_pairs = List.map interval_to_pair intervals in
    let (lefts, rights, constrs) = Expr_helpers.get_right_left_constr ineqs in
    let new_exprs = List.map2 (fun a b -> shift_expr a (fst b) (snd b) identifier) rights inter_pairs in
    let new_right = Expr_simplifications.automatic_simplify (Sum new_exprs) in
    (match (List.nth constrs 0) with
    | "==" -> Equals(List.nth lefts 0, new_right)
    | "<" -> Less(List.nth lefts 0, new_right)
    | "<=" -> LessEq(List.nth lefts 0, new_right)
    | ">" -> Greater(List.nth lefts 0, new_right)
    | ">=" -> GreaterEq(List.nth lefts 0, new_right)
    | _ -> failwith "all cases will have been covered"
    )
  ;;

