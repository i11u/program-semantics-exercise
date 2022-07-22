
(* The type of tokens. *)

type token = 
  | TURNSTILE
  | TRUE
  | THEN
  | RPAREN
  | REC
  | RBRACKET
  | PLUS
  | MULT
  | MINUS
  | LT
  | LPAREN
  | LET
  | LBRACKET
  | INTV of (int)
  | IN
  | IF
  | ID of (Syntax.id)
  | FUN
  | FALSE
  | EVALTO
  | EQ
  | ELSE
  | COMMA
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
