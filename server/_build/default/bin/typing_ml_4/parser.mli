
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
  | MULT
  | MINUS
  | MATCH
  | LT
  | LPAREN
  | LET
  | LBRACKET_RBRACKET
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
  | CONSTRUCT
  | COMMA
  | COLON
  | BAR
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
