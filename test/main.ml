open Subscript_def
open Expr_def
open Expr_helpers
(*open Expr_simplifications*)
open Expr_to_opcalc
(*open Expr_opCalc_simp*)

let print_expr e = 
  print_endline (inequation_to_string e);;

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

let lis = [x;y;z;x1; x2; x3; x4; x5; x6; x7];;

List.iter (fun x -> begin print_endline (expr_to_string x); print_endline (expr_to_string (Expr_simplifications.automatic_simplify x)) end) lis;;
