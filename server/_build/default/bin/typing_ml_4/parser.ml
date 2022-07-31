
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
    | INTV of (
# 17 "bin/typing_ml_4/parser.mly"
       (int)
# 30 "bin/typing_ml_4/parser.ml"
  )
    | INT
    | IN
    | IF
    | ID of (
# 16 "bin/typing_ml_4/parser.mly"
       (Syntax.id)
# 38 "bin/typing_ml_4/parser.ml"
  )
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
  
end

include MenhirBasics

# 1 "bin/typing_ml_4/parser.mly"
  
open Syntax

# 59 "bin/typing_ml_4/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_toplevel) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: toplevel. *)

  | MenhirState02 : (('s, _menhir_box_toplevel) _menhir_cell1_ID, _menhir_box_toplevel) _menhir_state
    (** State 02.
        Stack shape : ID.
        Start symbol: toplevel. *)

  | MenhirState07 : (('s, _menhir_box_toplevel) _menhir_cell1_TyVarList, _menhir_box_toplevel) _menhir_state
    (** State 07.
        Stack shape : TyVarList.
        Start symbol: toplevel. *)

  | MenhirState09 : (('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_state
    (** State 09.
        Stack shape : MATCH.
        Start symbol: toplevel. *)

  | MenhirState10 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 10.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState17 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 17.
        Stack shape : LET ID ID.
        Start symbol: toplevel. *)

  | MenhirState20 : (('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_state
    (** State 20.
        Stack shape : IF.
        Start symbol: toplevel. *)

  | MenhirState24 : (('s, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 24.
        Stack shape : FUN ID.
        Start symbol: toplevel. *)

  | MenhirState27 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 27.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState29 : (('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_state
    (** State 29.
        Stack shape : MExpr.
        Start symbol: toplevel. *)

  | MenhirState30 : ((('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 30.
        Stack shape : MExpr AppExpr.
        Start symbol: toplevel. *)

  | MenhirState33 : (('s, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 33.
        Stack shape : AppExpr.
        Start symbol: toplevel. *)

  | MenhirState34 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 34.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState40 : (('s, _menhir_box_toplevel) _menhir_cell1_LTExpr, _menhir_box_toplevel) _menhir_state
    (** State 40.
        Stack shape : LTExpr.
        Start symbol: toplevel. *)

  | MenhirState45 : (('s, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 45.
        Stack shape : Expr.
        Start symbol: toplevel. *)

  | MenhirState49 : ((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 49.
        Stack shape : IF Expr.
        Start symbol: toplevel. *)

  | MenhirState51 : (((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 51.
        Stack shape : IF Expr Expr.
        Start symbol: toplevel. *)

  | MenhirState54 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 54.
        Stack shape : LET ID ID Expr.
        Start symbol: toplevel. *)

  | MenhirState57 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 57.
        Stack shape : LET ID.
        Start symbol: toplevel. *)

  | MenhirState59 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 59.
        Stack shape : LET ID Expr.
        Start symbol: toplevel. *)

  | MenhirState66 : ((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 66.
        Stack shape : MATCH Expr.
        Start symbol: toplevel. *)

  | MenhirState72 : (((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 72.
        Stack shape : MATCH Expr Expr ID ID.
        Start symbol: toplevel. *)

  | MenhirState75 : ((('s, _menhir_box_toplevel) _menhir_cell1_TyVarList, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 75.
        Stack shape : TyVarList Expr.
        Start symbol: toplevel. *)

  | MenhirState79 : (('s, _menhir_box_toplevel) _menhir_cell1_SingleVar, _menhir_box_toplevel) _menhir_state
    (** State 79.
        Stack shape : SingleVar.
        Start symbol: toplevel. *)


and ('s, 'r) _menhir_cell1_AppExpr = 
  | MenhirCell1_AppExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_Expr = 
  | MenhirCell1_Expr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_LTExpr = 
  | MenhirCell1_LTExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_MExpr = 
  | MenhirCell1_MExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_PMExpr = 
  | MenhirCell1_PMExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_SingleVar = 
  | MenhirCell1_SingleVar of 's * ('s, 'r) _menhir_state * (string * Syntax.ty)

and ('s, 'r) _menhir_cell1_TyVarList = 
  | MenhirCell1_TyVarList of 's * ('s, 'r) _menhir_state * ((string * Syntax.ty) list)

and ('s, 'r) _menhir_cell1_FUN = 
  | MenhirCell1_FUN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 16 "bin/typing_ml_4/parser.mly"
       (Syntax.id)
# 211 "bin/typing_ml_4/parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 16 "bin/typing_ml_4/parser.mly"
       (Syntax.id)
# 218 "bin/typing_ml_4/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MATCH = 
  | MenhirCell1_MATCH of 's * ('s, 'r) _menhir_state

and _menhir_box_toplevel = 
  | MenhirBox_toplevel of (Syntax.judgement) [@@unboxed]

let _menhir_action_01 =
  fun i ->
    (
# 112 "bin/typing_ml_4/parser.mly"
         ( ILit i )
# 241 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_02 =
  fun i ->
    (
# 113 "bin/typing_ml_4/parser.mly"
       ( Var i )
# 249 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_03 =
  fun () ->
    (
# 114 "bin/typing_ml_4/parser.mly"
       ( BLit true )
# 257 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_04 =
  fun () ->
    (
# 115 "bin/typing_ml_4/parser.mly"
        ( BLit false )
# 265 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_05 =
  fun e ->
    (
# 116 "bin/typing_ml_4/parser.mly"
                       ( e )
# 273 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_06 =
  fun () ->
    (
# 117 "bin/typing_ml_4/parser.mly"
                    ( NilExp )
# 281 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_07 =
  fun e1 e2 ->
    (
# 108 "bin/typing_ml_4/parser.mly"
                      ( AppExp (e1, e2) )
# 289 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_08 =
  fun e ->
    (
# 109 "bin/typing_ml_4/parser.mly"
          ( e )
# 297 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_09 =
  fun e1 e2 ->
    (
# 79 "bin/typing_ml_4/parser.mly"
                            ( ConsExp (e1, e2) )
# 305 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_10 =
  fun e ->
    (
# 71 "bin/typing_ml_4/parser.mly"
            ( e )
# 313 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_11 =
  fun e ->
    (
# 72 "bin/typing_ml_4/parser.mly"
             ( e )
# 321 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_12 =
  fun e ->
    (
# 73 "bin/typing_ml_4/parser.mly"
            ( e )
# 329 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_13 =
  fun e ->
    (
# 74 "bin/typing_ml_4/parser.mly"
           ( e )
# 337 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_14 =
  fun e ->
    (
# 75 "bin/typing_ml_4/parser.mly"
           ( e )
# 345 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_15 =
  fun e ->
    (
# 76 "bin/typing_ml_4/parser.mly"
              ( e )
# 353 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_16 =
  fun e x ->
    (
# 82 "bin/typing_ml_4/parser.mly"
                        ( FunExp (x, e) )
# 361 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_17 =
  fun c e t ->
    (
# 85 "bin/typing_ml_4/parser.mly"
                                    ( IfExp (c, t, e) )
# 369 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_18 =
  fun l r ->
    (
# 95 "bin/typing_ml_4/parser.mly"
                       ( BinOp (Lt, l, r) )
# 377 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_19 =
  fun e ->
    (
# 96 "bin/typing_ml_4/parser.mly"
           ( e )
# 385 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_20 =
  fun e1 e2 x ->
    (
# 91 "bin/typing_ml_4/parser.mly"
                                 ( LetExp (x, e1, e2) )
# 393 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_21 =
  fun e1 e2 x y ->
    (
# 92 "bin/typing_ml_4/parser.mly"
                                                    ( LetRecExp (x, y, e1, e2) )
# 401 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_22 =
  fun l r ->
    (
# 104 "bin/typing_ml_4/parser.mly"
                         ( BinOp (Mult, l, r) )
# 409 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_23 =
  fun e ->
    (
# 105 "bin/typing_ml_4/parser.mly"
            ( e )
# 417 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_24 =
  fun e1 e2 e3 x y ->
    (
# 88 "bin/typing_ml_4/parser.mly"
                                                                                           ( MatchExp (e1, e2, x, y, e3) )
# 425 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_25 =
  fun l r ->
    (
# 99 "bin/typing_ml_4/parser.mly"
                        ( BinOp (Plus, l, r) )
# 433 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_26 =
  fun l r ->
    (
# 100 "bin/typing_ml_4/parser.mly"
                         ( BinOp (Minus, l, r) )
# 441 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_27 =
  fun e ->
    (
# 101 "bin/typing_ml_4/parser.mly"
          ( e )
# 449 "bin/typing_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_28 =
  fun v x ->
    (
# 66 "bin/typing_ml_4/parser.mly"
                    ( (x, v) )
# 457 "bin/typing_ml_4/parser.ml"
     : (string * Syntax.ty))

let _menhir_action_29 =
  fun hd tl ->
    (
# 61 "bin/typing_ml_4/parser.mly"
                                  ( hd::tl )
# 465 "bin/typing_ml_4/parser.ml"
     : ((string * Syntax.ty) list))

let _menhir_action_30 =
  fun v ->
    (
# 62 "bin/typing_ml_4/parser.mly"
              ( v::[] )
# 473 "bin/typing_ml_4/parser.ml"
     : ((string * Syntax.ty) list))

let _menhir_action_31 =
  fun () ->
    (
# 63 "bin/typing_ml_4/parser.mly"
  ( [] )
# 481 "bin/typing_ml_4/parser.ml"
     : ((string * Syntax.ty) list))

let _menhir_action_32 =
  fun () ->
    (
# 47 "bin/typing_ml_4/parser.mly"
      ( TyInt )
# 489 "bin/typing_ml_4/parser.ml"
     : (Syntax.ty))

let _menhir_action_33 =
  fun e t tl ->
    (
# 26 "bin/typing_ml_4/parser.mly"
                                             ( TyExp (tl, e, t) )
# 497 "bin/typing_ml_4/parser.ml"
     : (Syntax.judgement))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ARROW ->
        "ARROW"
    | BAR ->
        "BAR"
    | BOOL ->
        "BOOL"
    | COLON ->
        "COLON"
    | COMMA ->
        "COMMA"
    | CONSTRUCT ->
        "CONSTRUCT"
    | ELSE ->
        "ELSE"
    | EQ ->
        "EQ"
    | FALSE ->
        "FALSE"
    | FUN ->
        "FUN"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | INT ->
        "INT"
    | INTV _ ->
        "INTV"
    | LBRACKET_RBRACKET ->
        "LBRACKET_RBRACKET"
    | LET ->
        "LET"
    | LIST ->
        "LIST"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MATCH ->
        "MATCH"
    | MINUS ->
        "MINUS"
    | MULT ->
        "MULT"
    | PLUS ->
        "PLUS"
    | REC ->
        "REC"
    | RPAREN ->
        "RPAREN"
    | THEN ->
        "THEN"
    | TRUE ->
        "TRUE"
    | TURNSTILE ->
        "TURNSTILE"
    | WITH ->
        "WITH"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_32_spec_07 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_TyVarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState07 _tok
  
  and _menhir_run_33 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState33
      | LBRACKET_RBRACKET ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v_2 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_2 in
          let _v = _menhir_action_01 i in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v_4 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_4 in
          let _v = _menhir_action_02 i in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | MINUS | MULT | PLUS | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_23 e in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_31 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_AppExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AppExpr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_07 e1 e2 in
      _menhir_goto_AppExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_AppExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState66 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState20 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState49 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState51 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState27 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState29 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_30 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | LBRACKET_RBRACKET ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v_2 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_2 in
          let _v = _menhir_action_01 i in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v_4 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_4 in
          let _v = _menhir_action_02 i in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | MINUS | MULT | PLUS | RPAREN | THEN | WITH ->
          let MenhirCell1_MExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_22 l r in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_10 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState10 _tok
  
  and _menhir_run_09 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_09 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
  
  and _menhir_run_11 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | REC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ID _v ->
              let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | EQ ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | FUN ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ID _v_0 ->
                          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | ARROW ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              (match (_tok : MenhirBasics.token) with
                              | TRUE ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_03 () in
                                  _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | MATCH ->
                                  _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
                              | LPAREN ->
                                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
                              | LET ->
                                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
                              | LBRACKET_RBRACKET ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_06 () in
                                  _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | INTV _v_3 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_3 in
                                  let _v = _menhir_action_01 i in
                                  _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | IF ->
                                  _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
                              | ID _v_5 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_5 in
                                  let _v = _menhir_action_02 i in
                                  _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | FUN ->
                                  _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
                              | FALSE ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_04 () in
                                  _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | _ ->
                                  _eRR ())
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EQ ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_03 () in
                  _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | MATCH ->
                  _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
              | LPAREN ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
              | LET ->
                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
              | LBRACKET_RBRACKET ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_06 () in
                  _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | INTV _v_10 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_10 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
              | ID _v_12 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_12 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_17 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_20 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState20 _tok
  
  and _menhir_run_22 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_03 () in
                  _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | MATCH ->
                  _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
              | LPAREN ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
              | LET ->
                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
              | LBRACKET_RBRACKET ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_06 () in
                  _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | INTV _v_2 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_2 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
              | ID _v_4 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_4 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_24 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState24 _tok
  
  and _menhir_run_32_spec_57 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState57 _tok
  
  and _menhir_goto_MExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState66 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState51 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState49 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState20 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState27 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_37 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | MINUS | PLUS | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_27 e in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_29 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState29
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_29 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState29 _tok
  
  and _menhir_goto_PMExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState40 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState07 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState66 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState51 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState49 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState20 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_41 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | RPAREN | THEN | WITH ->
          let MenhirCell1_LTExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_18 l r in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_27 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState27
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_27 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState27 _tok
  
  and _menhir_run_34 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_34 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
  
  and _menhir_goto_LTExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LT ->
          let _menhir_stack = MenhirCell1_LTExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | BAR | COLON | CONSTRUCT | ELSE | IN | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_13 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_32_spec_40 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
  
  and _menhir_goto_Expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_73 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState66 ->
          _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_61 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_60 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_55 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState51 ->
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState49 ->
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState20 ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_74 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_TyVarList as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              let _v_0 = _menhir_action_32 () in
              let MenhirCell1_TyVarList (_menhir_stack, _, tl) = _menhir_stack in
              let (t, e) = (_v_0, _v) in
              let _v = _menhir_action_33 e t tl in
              MenhirBox_toplevel _v
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_45 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_45 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState45 _tok
  
  and _menhir_run_73 : type  ttv_stack. ((((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_Expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_24 e1 e2 e3 x y in
          let e = _v in
          let _v = _menhir_action_15 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_67 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ID _v_0 ->
              let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | CONSTRUCT ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | ID _v_1 ->
                      let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_1) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ARROW ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | TRUE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_03 () in
                              _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState72
                          | LPAREN ->
                              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState72
                          | LET ->
                              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState72
                          | LBRACKET_RBRACKET ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_06 () in
                              _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | INTV _v_4 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_4 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState72
                          | ID _v_6 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_6 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState72
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_72 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState72 _tok
  
  and _menhir_run_63 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ARROW ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | TRUE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_03 () in
                      _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | MATCH ->
                      _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState66
                  | LPAREN ->
                      _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState66
                  | LET ->
                      _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState66
                  | LBRACKET_RBRACKET ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_06 () in
                      _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | INTV _v_2 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_2 in
                      let _v = _menhir_action_01 i in
                      _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | IF ->
                      _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState66
                  | ID _v_4 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_4 in
                      let _v = _menhir_action_02 i in
                      _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | FUN ->
                      _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState66
                  | FALSE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_04 () in
                      _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_32_spec_66 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState66 _tok
  
  and _menhir_run_61 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_05 e in
          _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_AExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState09 ->
          _menhir_run_32_spec_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState66 ->
          _menhir_run_32_spec_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState72 ->
          _menhir_run_32_spec_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState10 ->
          _menhir_run_32_spec_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState57 ->
          _menhir_run_32_spec_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState59 ->
          _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState17 ->
          _menhir_run_32_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState54 ->
          _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState20 ->
          _menhir_run_32_spec_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState49 ->
          _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState51 ->
          _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState24 ->
          _menhir_run_32_spec_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState45 ->
          _menhir_run_32_spec_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState40 ->
          _menhir_run_32_spec_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState34 ->
          _menhir_run_32_spec_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState27 ->
          _menhir_run_32_spec_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState29 ->
          _menhir_run_32_spec_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState33 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState30 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_32_spec_59 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
  
  and _menhir_run_32_spec_54 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
  
  and _menhir_run_32_spec_49 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState49 _tok
  
  and _menhir_run_32_spec_51 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState51 _tok
  
  and _menhir_run_60 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_20 e1 e2 x in
          _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_LetExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_12 e in
      _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_58 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LPAREN ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_32_spec_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_55 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_21 e1 e2 x y in
          _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_53 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
          | LPAREN ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_32_spec_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_52 : type  ttv_stack. ((((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell1_Expr (_menhir_stack, _, c) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_17 c e t in
          let e = _v in
          let _v = _menhir_action_14 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_50 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState51
          | LPAREN ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState51
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState51
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState51
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState51
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_32_spec_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_48 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState49
          | LPAREN ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState49
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState49
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState49
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState49
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_32_spec_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_46 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_09 e1 e2 in
          let e = _v in
          let _v = _menhir_action_11 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_44 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | ELSE | IN | RPAREN | THEN | WITH ->
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_16 e x in
          let e = _v in
          let _v = _menhir_action_10 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_26 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_19 e in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_35 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | MINUS | PLUS | RPAREN | THEN | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_26 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_28 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COLON | CONSTRUCT | ELSE | IN | LT | MINUS | PLUS | RPAREN | THEN | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_25 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_TyVarList (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | LPAREN ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v_2 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_2 in
          let _v = _menhir_action_01 i in
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | ID _v_4 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_4 in
          let _v = _menhir_action_02 i in
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_32_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  let rec _menhir_run_80 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleVar -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_SingleVar (_menhir_stack, _menhir_s, hd) = _menhir_stack in
      let tl = _v in
      let _v = _menhir_action_29 hd tl in
      _menhir_goto_TyVarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_TyVarList : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState79 ->
          _menhir_run_80 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState00 ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v_0 = _menhir_action_32 () in
              let (v, x) = (_v_0, _v) in
              let _v = _menhir_action_28 v x in
              (match (_tok : MenhirBasics.token) with
              | COMMA ->
                  let _menhir_stack = MenhirCell1_SingleVar (_menhir_stack, _menhir_s, _v) in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | ID _v ->
                      _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState79
                  | TURNSTILE ->
                      let _v = _menhir_action_31 () in
                      _menhir_run_80 _menhir_stack _menhir_lexbuf _menhir_lexer _v
                  | _ ->
                      _eRR ())
              | TURNSTILE ->
                  let v = _v in
                  let _v = _menhir_action_30 v in
                  _menhir_goto_TyVarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00
      | TURNSTILE ->
          let _v = _menhir_action_31 () in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00
      | _ ->
          _eRR ()
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
