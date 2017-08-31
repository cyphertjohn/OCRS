open Type_def;;


let x1 = Equals(Output_variable("y", SAdd("n", 1)), Plus(Output_variable("y", SSVar "n"), Rational (Mpq.init_set_si 1 1)));;

let y1 = Equals(Output_variable("y", SAdd("n", 1)), Times (Output_variable("y", SSVar "n"), Rational (Mpq.init_set_si 2 1)));;

let x8 = Equals(Output_variable("y", SAdd("n", 1)), Plus (Output_variable("y", SSVar "n"), Plus(Pow (Input_variable "n", Rational (Mpq.init_set_si 4 1)), Pow (Input_variable "n", Rational (Mpq.init_set_si 3 1)))));;

let x9 = Equals(Output_variable("y", SAdd("n", 1)), Plus (Output_variable("y", SSVar "n"), Pow (Plus(Input_variable "n", Rational (Mpq.init_set_si 1 1)), Rational (Mpq.init_set_si 4 1))));;

let big_test = Equals(Output_variable("y", SAdd("n", 1)), Sum [Times(Rational (Mpq.init_set_si 2 1), Output_variable("y", SSVar "n")); Pow(Input_variable "n", Rational (Mpq.init_set_si 2 1)); Pow(Rational (Mpq.init_set_si 3 1), Input_variable "n")]);;

let x2 = Equals(Output_variable("y", SAdd("n", 1)), Times(Rational (Mpq.init_set_si 1 2), Output_variable("y", SSVar "n")));;

let will_it_work = Equals(Output_variable("y", SAdd("n", 1)), Plus(Times (Rational (Mpq.init_set_si 2 1), Output_variable("y", SSVar "n")), Pow(Rational (Mpq.init_set_si 2 1), Input_variable "n")));;

let x3 = Equals(Output_variable("y", SAdd("n", 1)), Plus(Output_variable("y", SSVar "n"), Pow(Rational (Mpq.init_set_si 2 1), Sum[Input_variable "n"; Rational (Mpq.init_set_si 1 1)])));;

let x4 = Equals(Output_variable("y", SAdd("n", 1)), Plus(Times(Rational (Mpq.init_set_si 2 1), Output_variable("y", SSVar "n")), Pow(Pow(Rational (Mpq.init_set_si 2 1), Plus(Input_variable "n", Rational (Mpq.init_set_si 1 1))), Rational (Mpq.init_set_si 2 1))));;


let x5 = Equals(Output_variable("y", SAdd("n", 2)), Plus(Output_variable("y", SAdd("n", (1))), Input_variable "n"));;

let x6 = Equals(Output_variable("y", SSVar "n"), Plus(Output_variable("y", SSDiv("n", 2)), Rational (Mpq.init_set_si 1 1)));;

let x7 = Equals(Output_variable("y", SSVar "n"), Plus(Times(Rational (Mpq.init_set_si 2 1), Output_variable("y", SSDiv("n", 2))), Input_variable "n"));;

let x11 = Equals(Output_variable("y", SSVar "n"), Plus(Times(Rational (Mpq.init_set_si 2 1), Output_variable("y", SSDiv("n", 2))), Pow(Input_variable "n", Rational (Mpq.init_set_si 2 1))));;


let x12 = Equals(Output_variable("y", SSVar "n"), Plus(Times(Rational (Mpq.init_set_si 3 1), Output_variable("y", SSDiv("n", 2))), Input_variable "n"));;

let x13 = "y_{n+1} = 3 * y_n + n^2 * 2^n, n";;

let x14 = "y_{n+1} = 2 * y_n + n^2 * 2^n, n";;

let parse str = 
  let lexbuf = Lexing.from_string str in
  Parser.main Lexer.token lexbuf;;

let z1 = "x_{n+1} = x_n + 1, n";;
let z2 = "y_{n+1} = y_n + x_n + 1, n";;
let z3 = "z_{n+1} = z_n + x_n + y_n +1, n";;

let new_test_list = [parse z1; parse z2; parse z3];;

let test_list = [x1; x8; x9; y1; x2; big_test; will_it_work; x3; x4; x5; x6; x7; x11; x12];;

List.iter (fun x -> let _ = Ocrs.solve_rec x true in print_endline "") test_list;;

Ocrs.solve_rec_str x13;;
print_endline "";;

Ocrs.solve_rec_str x14;;
print_endline "";;

Ocrs.solve_rec_str "z_{n+1} = z_n + y_0 + x_0, n";;
print_endline "";;

let res_list = Ocrs.solve_rec_list new_test_list;;
let print_list lis = List.iter (fun x -> print_endline (Expr_helpers.inequation_to_string x)) lis;;
let print_res_list lis = List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) lis;;
let _ = print_list new_test_list;;
let _ = print_res_list res_list;;
print_endline "";;
print_endline "";;

print_endline "";;
Ocrs.solve_rec_str "y_{k+1} >= y_k + a, k";;

print_endline "";;
Ocrs.solve_rec_str "y_{n+1}-a*y_n = n, n";;


print_endline "";;
let binary_search_term = Sum[Output_variable ("hi", SSVar "n"); Product[Rational (Mpq.init_set_si (-1) 1); Output_variable ("lo", SSVar "n")]];;
let second_test_list = [(binary_search_term, parse "r_{n+1} = (1/2)*r_n, n"); (Output_variable("x", SSVar "n"), parse z1); (Output_variable("y", SSVar "n"), parse z2); (Output_variable("z", SSVar "n"), parse z3)];;
let res_second_test_list = Ocrs.solve_rec_list_pair second_test_list;;
print_res_list res_second_test_list;;
print_endline "";;


let test_list = [(Output_variable("x", SSVar "n"), Equals(Output_variable("x", SAdd ("n", 1)), Plus(Output_variable("x", SSVar "n"), Rational (Mpq.init_set_si 1 1)))); (Output_variable("y", SSVar "n"),  Equals(Output_variable("y", SAdd ("n", 1)), Plus(Output_variable("x", SSVar "n"), Output_variable("y", SSVar "n"))))];;

let res = Ocrs.solve_rec_list_pair test_list;;
print_res_list res;;
print_endline "";;


Ocrs.solve_rec_str "y_{n+1} = a*y_n + (b*n^2 + c*n + d)*e^n, n";;
print_endline "";;

Ocrs.solve_rec_str "y_{n+1} = a*y_n + (b*n^2 + c*n + d)*e^2, n";;
print_endline "";;



let symbolic_log = Equals(Output_variable("x", SAdd ("n", 1)), Sum[Output_variable("x", SSVar "n"); Log(Mpq.init_set_si 2 1, Symbolic_Constant "y")]);;
Ocrs.solve_rec symbolic_log true;;
print_endline "";; 



let one = Mpq.init_set_si 1 1;;
let one_copy = Mpq.init_set_si 1 1;;
let minus_2 = Mpq.init_set_si (-2) 1;;
let four = Mpq.init_set_si 4 1;;

let matrix_test_1 = VEquals (Ovec ([|"x"; "y"|], SAdd("n", 1)), [|[|one; one_copy|];[|minus_2; four|]|], Ovec ([|"x"; "y"|], SSVar "n"), [|Input_variable "n"; Rational (Mpq.init_set_si 1 1)|]);;


print_endline "";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test_1);;
let result = Ocrs.solve_mat_rec matrix_test_1 false;;
print_endline "";;



List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;

let matrix_test = VEquals (Ovec ([|"x"|], SAdd("n", 1)), [|[|four|]|], Ovec ([|"x"|], SSVar "n"), [|Input_variable "n"|]);;

print_endline "";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test);;
let result = Ocrs.solve_mat_rec matrix_test false;;
print_endline "";;
List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;


let matrix_test_2 = VEquals (Ovec ([|"x"; "y"; "z"|], SAdd("n", 1)), [|[|(Mpq.init_set_si 5 1); Mpq.init_set_si 2 1; Mpq.init_set_si (-2) 1;|];[|Mpq.init_set_si 2 1; Mpq.init_set_si 5 1;Mpq.init_set_si (-2) 1|];[|Mpq.init_set_si (-2) 1; Mpq.init_set_si (-2) 1; Mpq.init_set_si 5 1|]|], Ovec ([|"x"; "y"; "z"|], SSVar "n"), [|Rational (Mpq.init_set_si 1 1); Times((Pow(Rational (Mpq.init_set_si 3 1), Input_variable "n")),Pow(Input_variable "n", Rational (Mpq.init_set_si 2 1))); Pow(Rational (Mpq.init_set_si 2 1), Input_variable "n")|]);;

print_endline "";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test_2);;
let result = Ocrs.solve_mat_rec matrix_test_2 true;;
print_endline "";;
List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;



let one = Mpq.init_set_si 1 1;;
let one_copy = Mpq.init_set_si 1 1;;
let minus_2 = Mpq.init_set_si (-2) 1;;
let four = Mpq.init_set_si 4 1;;



let matrix_test_1 = VEquals (Ovec ([|"x"; "y"|], SAdd("n", 1)), [|[|one; one_copy|];[|minus_2; four|]|], Ovec ([|"x"; "y"|], SSVar "n"), [|Rational (Mpq.init_set_si 0 1); Rational (Mpq.init_set_si 1 1)|]);;


print_endline "";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test_1);;
let result = Ocrs.solve_mat_rec matrix_test_1 true;;
print_endline "";;



List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;







let matrix_test_1 = VEquals (Ovec ([|"x"; "y"|], SAdd("n", 1)), [|[|one; one_copy|];[|Mpq.init_set_si (-9) 1; Mpq.init_set_si 1 1|]|], Ovec ([|"x"; "y"|], SSVar "n"), [|Rational (Mpq.init_set_si 0 1); Rational (Mpq.init_set_si 0 1)|]);;


print_endline "";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test_1);;
let result = Ocrs.solve_mat_rec matrix_test_1 true;;
print_endline "";;



List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;




let qqify = Array.map (Array.map (fun x -> Mpq.init_set_si x 1))
let matrix_test_fib =
  VEquals (Ovec ([|"a"; "b"; "c"; "d"; "e"; "f"; "g"|], SAdd("n", 1)),
           qqify [|
             [| 1; 0; 1; 0; 0; 0; 0 |];
             [| 0; 1; 0; 1; 0; 0; 0 |];
             [| 1; 0; 0; 0; 0; 0; 0 |];
             [| 0; 1; 0; 0; 0; 0; 0 |];
             [| 0; 0; 0; 0; 1; 0; 0 |];
             [| 0; 0; 0; 0; 0; 1; 0 |];
             [| 0; 0; 0; 0; 0; 1; 0 |];
           |],
           Ovec ([|"a"; "b"; "c"; "d"; "e"; "f"; "g"|], SSVar "n"),
           (Array.map (fun x -> Rational (Mpq.init_set_si x 1))
              [| 0; 0; 0; 0; 1; -1; -1 |]));;
 
print_endline "\nFIB";;
print_endline (Mat_helpers.matrix_rec_to_string matrix_test_fib);;
let result = Ocrs.solve_mat_rec matrix_test_fib false;;
print_endline "";;

List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;


print_endline "";;
let ex_with_iif = Sum [Base_case ("g", 0); Product [Base_case ("f", 0); Iif ("q ^ -1", SSVar "n")]; Product [Rational (Mpq.init_set_si (-1) 1); Base_case ("g", 0); Iif ("q ^ -1", SSVar "n")]; Product [Rational (Mpq.init_set_si (-1) 1); Input_variable ("n")]];;

let new_mat_test = VEquals (Ovec ([|"y"|], SAdd("n", 1)), [|[|Mpq.init_set_si 1 1|]|], Ovec ([|"y"|], SSVar "n"), [|ex_with_iif|]);;
print_endline (Mat_helpers.matrix_rec_to_string new_mat_test);;
let result = Ocrs.solve_mat_rec new_mat_test true;;
List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;
print_endline "";;


let new_rec_test = Equals(Output_variable ("y", SAdd("n", 1)), Plus(Output_variable ("y", SSVar "n"), ex_with_iif));;

let result = Ocrs.solve_rec new_rec_test true;;
print_endline (Expr_helpers.piece_to_string result);;

print_endline "";;
print_endline "";;


let first_part = Minus(Symbolic_Constant "g_0", Input_variable "n");;
let second_part = Minus(Symbolic_Constant "f_0", Input_variable "n");;

let piece_wise_expr_1 = PieceWiseExpr ("n", [(Bounded (0,0), first_part); (BoundBelow 1, second_part)]);;


let new_expr = Pow(Input_variable "n", Rational (Mpq.init_set_si 2 1));;

let piece_wise_expr_2 = PieceWiseExpr ("n", [(BoundBelow 0, new_expr)]);;

let new_rec_test_piece = PVEquals (Ovec ([|"x";"y"|], SAdd("n", 1)), [|[|Mpq.init_set_si 2 1;Mpq.init_set_si 0 1|];[|Mpq.init_set_si 0 1;Mpq.init_set_si 1 1|]|], Ovec ([|"x";"y"|], SSVar "n"), [|piece_wise_expr_1; piece_wise_expr_2|]);;

let result = Ocrs.solve_mat_rec_piece new_rec_test_piece true;;

List.iter (fun x -> print_endline (Expr_helpers.piece_to_string x)) result;;



