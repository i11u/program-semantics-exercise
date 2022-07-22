
(* The type of tokens. *)

type token = 
  | TURNSTILE
  | TRUE
  | THEN
  | RPAREN
  | PLUSC
  | PLUS
  | MULTC
  | MULT
  | MINUSC
  | MINUS
  | LTC
  | LT
  | LPAREN
  | LET
  | IS
  | INTV of (int)
  | IN
  | IF
  | ID of (Syntax.id)
  | FALSE
  | EVALTO
  | EQ
  | ELSE
  | COMMA

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
