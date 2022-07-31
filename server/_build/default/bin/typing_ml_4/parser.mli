
(* The type of tokens. *)

type token = 
  | WITH
  | TURNSTILE
  | TRUE
  | THEN
  | RPAREN
  | REC
  | PLUS
  | MULT
  | MINUS
  | MATCH
  | LT
  | LPAREN
  | LIST
  | LET
  | LBRACKET_RBRACKET
  | INTV of (int)
  | INT
  | IN
  | IF
  | ID of (Syntax.id)
  | FUN
  | FALSE
  | EQ
  | ELSE
  | CONSTRUCT
  | COMMA
  | COLON
  | BOOL
  | BAR
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.judgement)
