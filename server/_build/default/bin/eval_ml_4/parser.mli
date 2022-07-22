
(* The type of tokens. *)

type token = 
  | WITH
  | TURNSTILE
  | TRUE
  | THEN
  | RPAREN
  | REC
  | RBRACKET
  | PLUS
  | NIL
  | MULT
  | MINUS
  | MATCH
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
  | CONS
  | COMMA
  | BAR
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
