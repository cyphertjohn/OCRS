(** This module contains some basic useful operations for dealing with matrix expressions, and matrices *)
open Type_def

(** This function takes an ovec and returns a array of expressions, by applying the subscript of the ovec to each string of the ovec *)
let apply_subscript_to_ovec ovec = 
  match ovec with
  | Ovec (idents, subscript) ->
    Array.map (fun x -> Output_variable(x, subscript)) idents
  ;;

(** Same as the previous function except for op_expressions *)
let apply_subscript_to_ovec_op ovec = 
  match ovec with
  | Ovec (idents, subscript) ->
    Array.map (fun x -> OpOutput_variable(x, subscript)) idents
  ;;


(** Transpose a matrix *)
let transpose_matrix matrix = 
  let m = Array.length matrix in
  if m = 0 then matrix
  else (
    let n = Array.length (matrix.(0)) in
    if n = 0 then matrix
    else (
      let answer = Array.make_matrix n m matrix.(0).(0) in
      let _ =
        for i = 0 to (m - 1) do
          for j = 0 to (n -1) do
            answer.(j).(i) <- (matrix.(i).(j))
          done
        done in
      answer
    )
  )
  ;;

(** Produce a formatted string representing the matrix recurrence *)
let mat_rec_to_string primed matrix unprimed add constr = 
  let primed_str = Array.map Expr_helpers.expr_to_string (apply_subscript_to_ovec primed) in
  let unprimed_str = Array.map Expr_helpers.expr_to_string (apply_subscript_to_ovec unprimed) in
  let add_str = Array.map Expr_helpers.expr_to_string add in
  let matrix_str = Array.map (fun x -> Array.map Mpq.to_string x) matrix in
  let length_of_biggest_primed = Array.fold_left (fun a b -> max a (String.length b)) 0 primed_str in
  let length_of_biggest_unprimed = Array.fold_left (fun a b -> max a (String.length b)) 0 unprimed_str in
  let length_of_biggest_add = Array.fold_left (fun a b -> max a (String.length b)) 0 add_str in
  let cols = transpose_matrix matrix_str in
  let lens = Array.map (fun x -> Array.fold_left (fun a b -> max a (String.length b)) 0 x) cols in
  let string_rows = Array.make (Array.length matrix_str) "" in
  
  let lens_with_format = Array.map (fun x -> Scanf.format_from_string ("%" ^ (string_of_int x) ^ "s") "%s") lens in
  let const_form = Scanf.format_from_string ("%" ^ (string_of_int (String.length constr) ^ "s")) "%s" in
  let _ =
    for i = 0 to (Array.length matrix_str) - 1 do
      let str_row = Array.make 7 "" in
      let primed_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_primed ^ "s |") "%s" in
      let _ = Array.set str_row 0 (Printf.sprintf primed_form (Array.get primed_str i)) in
      let _ =
        if i = ((Array.length matrix_str)/2) then
          Array.set str_row 1 (Printf.sprintf const_form constr)
        else
          Array.set str_row 1 (Printf.sprintf const_form "")
        in
      let lens_with_format_list = Array.to_list lens_with_format in
      let row_lis = Array.to_list (Array.get matrix_str i) in
      let matrix_row = List.map2 (fun form value -> Printf.sprintf (form) value) lens_with_format_list row_lis in
      let matrix_row_str = String.concat " " matrix_row in
      let _ = Array.set str_row 2 ("| " ^ matrix_row_str ^ " |") in
      let _ =
        if i = ((Array.length matrix_str)/2) then
          Array.set str_row 3 (Printf.sprintf ("%1s") "*")
        else
          Array.set str_row 3 (Printf.sprintf ("%1s") "")
      in
      let unprimed_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_unprimed ^ "s |") "%s" in
      let _ = Array.set str_row 4 (Printf.sprintf unprimed_form (Array.get unprimed_str i)) in
      let _ =
        if i = ((Array.length matrix_str)/2) then
          Array.set str_row 5 (Printf.sprintf ("%1s") "+")
        else
          Array.set str_row 5 (Printf.sprintf ("%1s") "")
      in
      let add_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_add ^ "s |") "%s" in
      let _ = Array.set str_row 6 (Printf.sprintf add_form (Array.get add_str i)) in
      Array.set string_rows i (String.concat " " (Array.to_list str_row))
    done in
  String.concat "\n" (Array.to_list string_rows)
  ;;

(** Produce a formatted string representing the matrix recurrence *)
let matrix_rec_to_string mat_rec = 
  match mat_rec with
 | VEquals(primed, matrix, unprimed, add) ->
   mat_rec_to_string primed matrix unprimed add "=="
 | VLess(primed, matrix, unprimed, add) ->
   mat_rec_to_string primed matrix unprimed add "<"
 | VLessEq(primed, matrix, unprimed, add) ->
   mat_rec_to_string primed matrix unprimed add "<="
 | VGreater(primed, matrix, unprimed, add) ->
   mat_rec_to_string primed matrix unprimed add ">"
 | VGreaterEq(primed, matrix, unprimed, add) ->
   mat_rec_to_string primed matrix unprimed add ">="
 ;;

(** Produce a string showing the intermediate representation of an ovec *)
let ovec_to_string_IR ovec = 
  match ovec with
  | Ovec (idents, subscript) ->
    "Ovec ([|" ^ (String.concat "; " (Array.to_list idents)) ^ "|], " ^ Expr_helpers.subscript_to_string_IR subscript ^ ")"
  ;;

(** Produce a string showing the intermediate representation of an matrix *)
let mat_to_string_IR matrix = 
  let matrix_str = Array.map (fun x -> Array.map Mpq.to_string x) matrix in
  let row_str = Array.map (fun x -> "[|" ^ (String.concat "; " (Array.to_list x)) ^ "|]") matrix_str in
  "[|" ^ (String.concat "; " (Array.to_list row_str)) ^ "|]"
  ;;

(** Produce a string showing the intermediate representation of an expression array *)
let expr_array_to_string_IR expr_arr = 
  "[|" ^ (String.concat "; " (Array.to_list (Array.map Expr_helpers.expr_to_string_IR expr_arr))) ^ "|]"
  ;;

(** Produce a string showing the intermediate representation of a matrix recurrence *)
let matrix_rec_to_string_IR mat_rec =
  match mat_rec with
 | VEquals(primed, matrix, _, add) ->
   "VEquals (" ^ (ovec_to_string_IR primed) ^ ", " ^ (mat_to_string_IR matrix) ^ ", " ^ (expr_array_to_string_IR add) ^ ")"
 | VLess(primed, matrix, _, add) ->
   "VLess (" ^ (ovec_to_string_IR primed) ^ ", " ^ (mat_to_string_IR matrix) ^ ", " ^ (expr_array_to_string_IR add) ^ ")"
 | VLessEq(primed, matrix, _, add) ->
   "VLessEq (" ^ (ovec_to_string_IR primed) ^ ", " ^ (mat_to_string_IR matrix) ^ ", " ^ (expr_array_to_string_IR add) ^ ")"
 | VGreater(primed, matrix, _, add) ->
   "VGreater (" ^ (ovec_to_string_IR primed) ^ ", " ^ (mat_to_string_IR matrix) ^ ", " ^ (expr_array_to_string_IR add) ^ ")"
 | VGreaterEq(primed, matrix, _, add) ->
   "VGreaterEq (" ^ (ovec_to_string_IR primed) ^ ", " ^ (mat_to_string_IR matrix) ^ ", " ^ (expr_array_to_string_IR add) ^ ")"
 ;;

