
{open Parser        (* The type token is defined in parser.mli *)
        exception SyntaxError of string
        }
        let int = ['0'-'9']+
        let float = (['0'-'9']*['.'])?['0'-'9']+
        rule token = parse
            [' ' '\t']     { token lexbuf }     (* skip blanks *)
          | ['\n' ]        { EOL }
          | int            { INT (int_of_string (Lexing.lexeme lexbuf)) }
          | float	   { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
          | '+'            { PLUS }
          | '-'            { MINUS }
          | '*'            { TIMES }
          | '/'            { DIV }
          | '^'		   { POW }
          | "choose"	   { BINOMIAL }
          | '('            { LPAREN }
          | ')'            { RPAREN }
          | '{'		   { LCURL }
          | '}'		   { RCURL }
          | ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']* as lxm { VAR(lxm) }
          | '_'		   { UNDERSCORE }
          | ','		   { COMMA }
          | '='		   { EQUALS }
          | '<'		   { LESS }
          | "<="	   { LESSEQ }
          | '>'		   { GREATER }
          | ">="	   { GREATEREQ }
          | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
          | eof            { EOF }
