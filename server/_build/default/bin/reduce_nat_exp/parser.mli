
(* The type of tokens. *)

type token = 
  | RPAREN
  | REDUCE
  | PLUSOP
  | PLUS
  | MULTOP
  | MULT
  | MREDUCE
  | LPAREN
  | IS
  | INTV of (int)
  | DREDUCE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
