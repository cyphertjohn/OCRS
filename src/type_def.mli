type subscript = SAdd of string * int | SSVar of string

val subscript_order : subscript -> subscript -> int

type expr =
    Plus of expr * expr
  | Minus of expr * expr
  | Times of expr * expr
  | Divide of expr * expr
  | Product of expr list
  | Sum of expr list
  | Symbolic_Constant of string
  | Base_case of string * int
  | Output_variable of string * subscript
  | Input_variable of string
  | Rational of Mpfr.t
  | Log of expr
  | Pow of expr * expr
  | Binomial of expr * expr
  | Factorial of expr
  | Undefined

type inequation =
    Equals of expr * expr
  | LessEq of expr * expr
  | Less of expr * expr
  | GreaterEq of expr * expr
  | Greater of expr * expr

val expr_order : expr -> expr -> int

type op_expr =
    OpPlus of op_expr * op_expr
  | OpMinus of op_expr * op_expr
  | OpTimes of op_expr * op_expr
  | OpDivide of op_expr * op_expr
  | OpProduct of op_expr list
  | OpSum of op_expr list
  | OpSymbolic_Constant of string
  | OpBase_case of string * int
  | OpOutput_variable of string * subscript
  | OpInput_variable of string
  | OpRational of Mpfr.t
  | OpLog of op_expr
  | OpPow of op_expr * op_expr
  | Q
  | OpUndefined

type op_inequation =
    OpEquals of op_expr * op_expr
  | OpLessEq of op_expr * op_expr
  | OpLess of op_expr * op_expr
  | OpGreaterEq of op_expr * op_expr
  | OpGreater of op_expr * op_expr
