{
  let reservedWords = [
    (* Keywords *)
  ]
}

rule main = parse
| [' ' '\009' '\012' '\n']+ { main lexbuf }
| "+" { Parser.PLUSOP }
| "*" { Parser.MULTOP }
| "evalto" { Parser.EVALTO }
| "plus" { Parser.PLUS }
| "times" { Parser.MULT }
| "is" { Parser.IS } 
| "Z" { Parser.INTV 0 }
| "S(" { let i = 1 in succ i lexbuf }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| eof { exit 0 }

and succ i = parse 
| "Z" { succ_rparen i lexbuf; Parser.INTV i }
| "S(" { succ (i+1) lexbuf }

and succ_rparen i = parse
| ")" { if i = 1 then () else succ_rparen (i-1) lexbuf }
