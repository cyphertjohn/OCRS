open Type_def;;

(*
let x = Sum [Product [Rational (snd (Mpfr.init_set_si 2 Mpfr.Near)); Pow(Symbolic_Constant "x", Rational (Mpq.init_set_si 3 1))]; Product [Pow(Symbolic_Constant "x", Rational (snd (Mpfr.init_set_si 2 Mpfr.Near))) ; Symbolic_Constant "x"]];;

let y = Product [Divide (Rational (Mpq.init_set_si 1 1), Symbolic_Constant "a"); Symbolic_Constant "b"; Symbolic_Constant "a"];;

let z = Minus (Symbolic_Constant "x", Symbolic_Constant "x");;

let x1 = Times (Divide (Symbolic_Constant "x", Symbolic_Constant "y"), Divide (Symbolic_Constant "y", Symbolic_Constant "x"));;

let x2 = Times (Rational (snd (Mpfr.init_set_si 2 Mpfr.Near)), Plus(Symbolic_Constant "x", Symbolic_Constant "y"));;

let x3 = Plus(Plus(Symbolic_Constant "a", Symbolic_Constant "b"), Times (Rational (Mpq.init_set_si (-1) 1), Plus(Symbolic_Constant "a", Symbolic_Constant "b")));;

let x4 = Times( Rational (Mpq.init_set_si 3 1), Sum [Times (Rational (Mpq.init_set_si 2 1), Symbolic_Constant "x") ; Symbolic_Constant "y"]);;

let x5 = Times(Rational (Mpq.init_set_si 3 1), Times (Rational (Mpq.init_set_si 2 1), Sum [Symbolic_Constant "x" ; Symbolic_Constant "y"]));;

let x6 = Divide(Minus(Symbolic_Constant "y", Symbolic_Constant "y"), Sum [Pow (Symbolic_Constant "x", Rational (Mpq.init_set_si 2 1)); Symbolic_Constant "x"; Product [Rational (Mpq.init_set_si (-1) 1); Symbolic_Constant "x"; Sum [Symbolic_Constant "x"; Rational (Mpq.init_set_si 1 1)]]]);;

let x7 = Divide(Minus(Symbolic_Constant "y", Symbolic_Constant "y"), Minus (Symbolic_Constant "y", Symbolic_Constant "y"));;

let x9 = Sum [Symbolic_Constant "x"; Product [Rational (snd(Mpfr.init_set_si (-2) Mpfr.Near)); Symbolic_Constant "x"]];;

let lis = [x;y;z;x1; x2; x3; x4; x5; x6; x7; x9];;

List.iter (fun x -> begin print_endline (expr_to_string x); print_endline (expr_to_string (Expr_simplifications.automatic_simplify x)); print_endline "" end) lis;;


let testing = OpProduct [OpSum [OpSymbolic_Constant "x"; OpRational (Mpq.init_set_si 2 1)]; OpSum [OpSymbolic_Constant "x"; OpRational (snd(Mpfr.init_set_si (1) Mpfr.Near))]];;


print_endline (op_expr_to_string (Op_simplifications.op_automatic_simplify testing));;
print_endline (op_expr_to_string (Op_transforms.algebraic_expand testing));;
print_endline ("");;
*)
(*
let test = Log( Mpq.init_set_si 2 1, Pow(Rational (Mpq.init_set_si 2 1), Sum[Times(Rational (Mpq.init_set_si 3 1), Input_variable "n"); Rational (Mpq.init_set_si 1 1)]));;

let pow_test = Pow(Rational (Mpq.init_set_si 2 1), Sum[Input_variable "n"; Rational (Mpq.init_set_si 3 1)]);;

let pow_test2 = Sum[Product[Rational (Mpq.init_set_si 4 1); Pow(Rational (Mpq.init_set_si 2 1), Sum[Log(Mpq.init_set_si 2 1, Sum[Input_variable "n"; Rational(Mpq.init_set_si 1 1)]); Rational (Mpq.init_set_si (-1) 1)])]; Rational (snd(Mpfr.init_set_si (-4) Mpfr.Near)); Product[Rational(Mpq.init_set_si (-1) 1); Sum[Log(Mpq.init_set_si 2 1, Sum[Input_variable "n"; Rational (Mpq.init_set_si 1 1)]); Rational (Mpq.init_set_si (-1) 1)]]];;

let log_test = Sum[Pow(Rational (Mpq.init_set_si 2 1), Log(Mpq.init_set_si 2 1, Input_variable "n")); Product[Rational (Mpq.init_set_si 2 1); Pow(Rational (Mpq.init_set_si 2 1), Product[Rational(Mpq.init_set_si 2 1); Log(Mpq.init_set_si 2 1, Input_variable "n")])]];;

print_endline (expr_to_string test);;
print_endline (expr_to_string (Expr_simplifications.automatic_simplify test));;

print_endline (expr_to_string pow_test);;
print_endline (expr_to_string (Expr_simplifications.automatic_simplify pow_test));;

print_endline (expr_to_string pow_test2);;
print_endline (expr_to_string (Expr_simplifications.automatic_simplify pow_test2));;

print_endline (expr_to_string log_test);;
print_endline (expr_to_string (Expr_simplifications.automatic_simplify log_test));;
*)











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
let _ = print_list new_test_list;;
let _ = print_list res_list;;
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
print_list res_second_test_list;;
print_endline "";;


let test_list = [(Output_variable("x", SSVar "n"), Equals(Output_variable("x", SAdd ("n", 1)), Plus(Output_variable("x", SSVar "n"), Rational (Mpq.init_set_si 1 1)))); (Output_variable("y", SSVar "n"),  Equals(Output_variable("y", SAdd ("n", 1)), Plus(Output_variable("x", SSVar "n"), Output_variable("y", SSVar "n"))))];;

let res = Ocrs.solve_rec_list_pair test_list;;
print_list res;;
print_endline "";;


Ocrs.solve_rec_str "y_{n+1} = a*y_n + (b*n^2 + c*n + d)*e^n, n";;
print_endline "";;

Ocrs.solve_rec_str "y_{n+1} = a*y_n + (b*n^2 + c*n + d)*e^2, n";;
print_endline "";;



let symbolic_log = Equals(Output_variable("x", SAdd ("n", 1)), Sum[Output_variable("x", SSVar "n"); Log(Mpq.init_set_si 2 1, Symbolic_Constant "y")]);;
Ocrs.solve_rec symbolic_log true;;
print_endline "";; 


(*let lexbuf = Lexing.from_string "y_n = (n ^ 2) * 2^n, n" in
let result = Parser.main Lexer.token lexbuf in

let _ = print_endline (Expr_helpers.inequation_to_string_IR result) in

let result  = Expr_simplifications.automatic_simplify_inequation result in

print_endline (Expr_helpers.inequation_to_string_IR result);;
*)
(*let x10 = Equals(Output_variable("y", SAdd("n", 4)), Sum[Times (Output_variable("y", SAdd ("n", 3)), Rational (Mpq.init_set_si 2 1));Times (Output_variable("y", SAdd ("n", 2)), Rational (Mpq.init_set_si 1 1)); Times (Output_variable("y", SAdd ("n", 1)), Rational (snd(Mpfr.init_set_si (-5) Mpfr.Near))); Times (Output_variable("y", SSVar "n"), Rational (Mpq.init_set_si 3 1))]);;

let simplify_x10 = Expr_simplifications.automatic_simplify_inequation x10;;

print_endline (inequation_to_string simplify_x10);;

let op_x10 = Op_simplifications.op_automatic_simplify_inequation (inequation_to_opCalc simplify_x10);;
print_endline (op_inequation_to_string op_x10);;

let isolated_op_x10 = Isolate_Ovar.solve_for_Ovar op_x10 "y" "n";;
print_endline (op_inequation_to_string isolated_op_x10);;*)
