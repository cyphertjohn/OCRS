%{
open Type_def
%}
%token <int> INT
%token <float> FLOAT
%token <string> VAR
%token COMMA UNDERSCORE
%token PI
%token BINOMIAL MOD
%token FLOOR
%token SIN COS ARCTAN
%token EQUALS LESS LESSEQ GREATER GREATEREQ
%token PLUS MINUS TIMES DIV POW
%token LPAREN RPAREN LCURL RCURL
%token Q
%token EOL EOF
%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%left BINOMIAL MOD
%right POW		/* highest precedence */
%nonassoc UMINUS SIN COS ARCTAN FLOOR
%start main             /* the entry point */
%type <Type_def.op_expr> main
%%
main:
    expr EOL          { (Op_simplifications.op_automatic_simplify $1) }
  | expr EOF          { (Op_simplifications.op_automatic_simplify $1) }
;

expr:
    INT			    { OpRational(Mpq.init_set_si $1 1) }
  | FLOAT                   { OpRational(Mpq.init_set_d ($1)) }
  | LPAREN expr RPAREN      { $2 }
  | expr PLUS expr          { OpPlus($1, $3) }
  | expr MINUS expr         { OpMinus($1, $3) }
  | expr TIMES expr         { OpTimes($1, $3) }
  | expr DIV expr           { OpDivide($1, $3) }
  | expr POW expr	    { OpPow($1, $3) }
  | MINUS expr %prec UMINUS { OpTimes(OpRational (Mpq.init_set_si (-1) 1), $2) }
  | expr BINOMIAL expr	    { SymBinom($1, $3) }
  | VAR UNDERSCORE LCURL sub RCURL      { OpOutput_variable ($1, $4) }
  | VAR UNDERSCORE LPAREN sub RPAREN    { OpOutput_variable ($1, $4) }
  | VAR UNDERSCORE VAR      { OpOutput_variable ($1, SSVar $3) }
  | VAR UNDERSCORE INT	    { OpSymbolic_Constant ($1 ^ "_" ^ (string_of_int $3)) }
  | VAR			    { OpSymbolic_Constant ($1) }
  | FLOOR LPAREN expr DIV FLOAT RPAREN { SymIDivide($3, Mpq.init_set_d ($5)) }
  | FLOOR LPAREN expr DIV INT RPAREN { SymIDivide($3, Mpq.init_set_si $5 1) }
  | SIN expr		    { SymSin($2) }
  | COS expr		    { SymCos($2) }
  | ARCTAN FLOAT	    { OpArctan(Mpq.init_set_d $2) }
  | ARCTAN INT	  	    { OpArctan(Mpq.init_set_si $2 1) }
  | expr MOD expr	    { SymMod ($1, $3) }
  | PI			    { OpPi }
  | Q                       { Q }
;
sub:
    VAR PLUS INT	{ SAdd ($1, $3) }
  | VAR DIV INT		{ SSDiv ($1, $3) }
  | VAR PLUS FLOAT	{ SAdd ($1, int_of_float $3) }
  | VAR DIV FLOAT	{ SSDiv ($1, int_of_float $3) }
  | VAR			{ SSVar $1 }
;
