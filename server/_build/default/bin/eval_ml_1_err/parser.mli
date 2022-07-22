
(* The type of tokens. *)

type token = 
  | TRUE
  | THEN
  | RPAREN
  | PLUS
  | MULT
  | MINUS
  | LT
  | LPAREN
  | INTV of (int)
  | IF
  | FALSE
  | EVALTO
  | ERROR
  | ELSE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
