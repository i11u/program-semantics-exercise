{
let reservedWords = [
  (* Keywords *)
]
}

rule main = parse
| [' ' '\009' '\012' '\n']+ { main lexbuf }
| "-"? ['0'-'9']+ 
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }
| "+" { Parser.PLUS }
| "*" { Parser.MULT }
| "evalto" { Parser.EVALTO }
| "if" { Parser.IF }
| "then" { Parser.THEN }
| "else" { Parser.ELSE }
| "true" { Parser.TRUE }
| "false" { Parser.FALSE }
| "-" { Parser.MINUS }
| "<" { Parser.LT }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| eof { exit 0 }
