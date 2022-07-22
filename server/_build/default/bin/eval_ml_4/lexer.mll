{
let reservedWords = [
  (* Keywords *)
  ("evalto", Parser.EVALTO);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("else", Parser.ELSE);
  ("true", Parser.TRUE);
  ("false", Parser.FALSE);
  ("let", Parser.LET);
  ("in", Parser.IN);
  ("fun", Parser.FUN);
  ("rec", Parser.REC);
]
}

rule main = parse
| [' ' '\009' '\012' '\n']+ { main lexbuf }
| "-"? ['0'-'9']+ 
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }
| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| "+" { Parser.PLUS }
| "*" { Parser.MULT }
| "|-" { Parser.TURNSTILE }
| "-" { Parser.MINUS }
| "<" { Parser.LT }
| "=" { Parser.EQ }
| "->" { Parser.ARROW }
| "," { Parser.COMMA }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "[" { Parser.LBRACKET }
| "]" { Parser.RBRACKET }
| eof { exit 0 }
