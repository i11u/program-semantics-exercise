
(* The type of tokens. *)

type token = 
  | RPAREN
  | PLUSOP
  | PLUS
  | MULTOP
  | MULT
  | LPAREN
  | IS
  | INTV of (int)
  | EVALTO

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
