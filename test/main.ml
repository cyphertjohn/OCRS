open Type_def
open Expr_helpers
(*open Expr_simplifications*)
open Expr_to_opcalc
(*open Expr_opCalc_simp*)


let x = Sum [Product [Rational (snd (Mpfr.init_set_si 2 Mpfr.Near)); Pow(Symbolic_Constant "x", Rational (snd (Mpfr.init_set_si 3 Mpfr.Near)))]; Product [Pow(Symbolic_Constant "x", Rational (snd (Mpfr.init_set_si 2 Mpfr.Near))) ; Symbolic_Constant "x"]];;

let y = Product [Divide (Rational (snd(Mpfr.init_set_si 1 Mpfr.Near)), Symbolic_Constant "a"); Symbolic_Constant "b"; Symbolic_Constant "a"];;

let z = Minus (Symbolic_Constant "x", Symbolic_Constant "x");;

let x1 = Times (Divide (Symbolic_Constant "x", Symbolic_Constant "y"), Divide (Symbolic_Constant "y", Symbolic_Constant "x"));;

let x2 = Times (Rational (snd (Mpfr.init_set_si 2 Mpfr.Near)), Plus(Symbolic_Constant "x", Symbolic_Constant "y"));;

let x3 = Plus(Plus(Symbolic_Constant "a", Symbolic_Constant "b"), Times (Rational (snd(Mpfr.init_set_si (-1) Mpfr.Near)), Plus(Symbolic_Constant "a", Symbolic_Constant "b")));;

let x4 = Times( Rational (snd(Mpfr.init_set_si 3 Mpfr.Near)), Sum [Times (Rational (snd(Mpfr.init_set_si 2 Mpfr.Near)), Symbolic_Constant "x") ; Symbolic_Constant "y"]);;

let x5 = Times(Rational (snd(Mpfr.init_set_si 3 Mpfr.Near)), Times (Rational (snd(Mpfr.init_set_si 2 Mpfr.Near)), Sum [Symbolic_Constant "x" ; Symbolic_Constant "y"]));;

let x6 = Divide(Minus(Symbolic_Constant "y", Symbolic_Constant "y"), Sum [Pow (Symbolic_Constant "x", Rational (snd(Mpfr.init_set_si 2 Mpfr.Near))); Symbolic_Constant "x"; Product [Rational (snd(Mpfr.init_set_si (-1) Mpfr.Near)); Symbolic_Constant "x"; Sum [Symbolic_Constant "x"; Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))]]]);;

let x7 = Divide(Minus(Symbolic_Constant "y", Symbolic_Constant "y"), Minus (Symbolic_Constant "y", Symbolic_Constant "y"));;

let x9 = Sum [Symbolic_Constant "x"; Product [Rational (snd(Mpfr.init_set_si (-2) Mpfr.Near)); Symbolic_Constant "x"]];;

let lis = [x;y;z;x1; x2; x3; x4; x5; x6; x7; x9];;

List.iter (fun x -> begin print_endline (expr_to_string x); print_endline (expr_to_string (Expr_simplifications.automatic_simplify x)); print_endline "" end) lis;;


let testing = OpProduct [OpSum [OpSymbolic_Constant "x"; OpRational (snd(Mpfr.init_set_si (2) Mpfr.Near))]; OpSum [OpSymbolic_Constant "x"; OpRational (snd(Mpfr.init_set_si (1) Mpfr.Near))]];;


print_endline (op_expr_to_string (Op_simplifications.op_automatic_simplify testing));;
print_endline (op_expr_to_string (Op_transforms.algebraic_expand testing));;
print_endline ("");;


let y1 = Equals(Output_variable("y", SAdd("n", 1)), Times (Output_variable("y", SSVar "n"), Rational (snd(Mpfr.init_set_si (2) Mpfr.Near))));;

let simplify_y1 = Expr_simplifications.automatic_simplify_inequation y1;;

print_endline (inequation_to_string simplify_y1);;

let op_y1 = Op_simplifications.op_automatic_simplify_inequation (inequation_to_opCalc simplify_y1);;

print_endline (op_inequation_to_string op_y1);;

let isolated_op_y1 = Isolate_Ovar.solve_for_Ovar op_y1 "y" "n";;

print_endline (op_inequation_to_string isolated_op_y1);;

let temp1 = Op_simplifications.op_automatic_simplify_inequation isolated_op_y1;;

let answer1 = Tau_inverse.tau_inverse_inequation temp1 "n"

let simp_answer1 = Expr_simplifications.automatic_simplify_inequation answer1;;

print_endline (inequation_to_string simp_answer1);;

print_endline "";;




let x8 = Equals(Output_variable("y", SAdd("n", 1)), Plus (Output_variable("y", SSVar "n"), Plus(Pow (Input_variable "n", Rational (snd (Mpfr.init_set_si 4 Mpfr.Near))), Pow (Input_variable "n", Rational (snd (Mpfr.init_set_si 3 Mpfr.Near))))));;

let simplify_x8 = Expr_simplifications.automatic_simplify_inequation x8;;

print_endline (inequation_to_string simplify_x8);;

let op_x8 = Op_simplifications.op_automatic_simplify_inequation (inequation_to_opCalc simplify_x8);;

print_endline (op_inequation_to_string op_x8);;

let isolated_op_x8 = Isolate_Ovar.solve_for_Ovar op_x8 "y" "n";;

print_endline (op_inequation_to_string isolated_op_x8);;

let temp = Op_simplifications.op_automatic_simplify_inequation (Op_transforms.algebraic_expand_inequation isolated_op_x8);;
print_endline (op_inequation_to_string temp);;
let answer = Tau_inverse.tau_inverse_inequation temp "n"

let simp_answer = Expr_transforms.inverse_binomial_ineq (Expr_simplifications.automatic_simplify_inequation answer);;

print_endline (inequation_to_string simp_answer);;

print_endline "";;

print_endline "";;

let top = OpRational (snd(Mpfr.init_set_si 2 Mpfr.Near));;

let bot = OpProduct[OpPow(OpSum[Q; OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))], OpRational (snd(Mpfr.init_set_si 2 Mpfr.Near))); OpSum[Q; OpRational (snd(Mpfr.init_set_si (-2) Mpfr.Near))]];;

print_endline (op_expr_to_string (Op_transforms.partial_fraction_2 top bot))

let top = OpSum[Q; OpRational (snd(Mpfr.init_set_si (-1) Mpfr.Near))];;

let bot = OpSum[Q; OpRational (snd(Mpfr.init_set_si (-2) Mpfr.Near))];;

print_endline (op_expr_to_string (Op_transforms.partial_fraction_2 top bot));;


let test = OpSum[OpProduct[OpRational (snd(Mpfr.init_set_si (-2) Mpfr.Near)); Q]; OpRational (snd(Mpfr.init_set_si (-2) Mpfr.Near))];;
let testdenom = OpPow(Q, OpRational (snd(Mpfr.init_set_si (2) Mpfr.Near)));;

let resul = Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide(test, testdenom)));;
print_endline (op_expr_to_string (resul));;

(*let x10 = Equals(Output_variable("y", SAdd("n", 4)), Sum[Times (Output_variable("y", SAdd ("n", 3)), Rational (snd(Mpfr.init_set_si 2 Mpfr.Near)));Times (Output_variable("y", SAdd ("n", 2)), Rational (snd(Mpfr.init_set_si 1 Mpfr.Near))); Times (Output_variable("y", SAdd ("n", 1)), Rational (snd(Mpfr.init_set_si (-5) Mpfr.Near))); Times (Output_variable("y", SSVar "n"), Rational (snd(Mpfr.init_set_si 3 Mpfr.Near)))]);;

let simplify_x10 = Expr_simplifications.automatic_simplify_inequation x10;;

print_endline (inequation_to_string simplify_x10);;

let op_x10 = Op_simplifications.op_automatic_simplify_inequation (inequation_to_opCalc simplify_x10);;
print_endline (op_inequation_to_string op_x10);;

let isolated_op_x10 = Isolate_Ovar.solve_for_Ovar op_x10 "y" "n";;
print_endline (op_inequation_to_string isolated_op_x10);;*)
