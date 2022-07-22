{
  let reservedWords = [
    (* Keywords *)
  ]
}

rule main = parse
| [' ' '\009' '\012' '\n']+ { main lexbuf }
| "plus" { Parser.PLUS }
| "times" { Parser.MULT }
| "is" { Parser.IS } 
| "Z" { Parser.INTV 0 }
| "S(" { let i = 1 in succ i lexbuf }
| ")" { main lexbuf }
| eof { exit 0 }

and succ i = parse 
| "Z" { Parser.INTV i }
| "S(" { succ (i+1) lexbuf }