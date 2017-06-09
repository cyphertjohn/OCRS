type token =
  | INT of (int)
  | FLOAT of (float)
  | VAR of (string)
  | COMMA
  | UNDERSCORE
  | PI
  | BINOMIAL
  | MOD
  | FLOOR
  | SIN
  | COS
  | ARCTAN
  | EQUALS
  | LESS
  | LESSEQ
  | GREATER
  | GREATEREQ
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | POW
  | LPAREN
  | RPAREN
  | LCURL
  | RCURL
  | EOL
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Type_def.inequation
