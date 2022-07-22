
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
    | INTV of (
# 15 "bin/eval_ml_4/parser.mly"
       (int)
# 31 "bin/eval_ml_4/parser.ml"
  )
    | IN
    | IF
    | ID of (
# 14 "bin/eval_ml_4/parser.mly"
       (Syntax.id)
# 38 "bin/eval_ml_4/parser.ml"
  )
    | FUN
    | FALSE
    | EVALTO
    | EQ
    | ELSE
    | CONS
    | COMMA
    | BAR
    | ARROW
  
end

include MenhirBasics

# 1 "bin/eval_ml_4/parser.mly"
  
open Syntax

# 58 "bin/eval_ml_4/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_toplevel) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: toplevel. *)

  | MenhirState002 : (('s, _menhir_box_toplevel) _menhir_cell1_ID, _menhir_box_toplevel) _menhir_state
    (** State 002.
        Stack shape : ID.
        Start symbol: toplevel. *)

  | MenhirState004 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 004.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState013 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 013.
        Stack shape : LPAREN VarList ID ID.
        Start symbol: toplevel. *)

  | MenhirState016 : (('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_state
    (** State 016.
        Stack shape : MATCH.
        Start symbol: toplevel. *)

  | MenhirState017 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 017.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState024 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 024.
        Stack shape : LET ID ID.
        Start symbol: toplevel. *)

  | MenhirState026 : (('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_state
    (** State 026.
        Stack shape : IF.
        Start symbol: toplevel. *)

  | MenhirState030 : (('s, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 030.
        Stack shape : FUN ID.
        Start symbol: toplevel. *)

  | MenhirState033 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 033.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState035 : (('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_state
    (** State 035.
        Stack shape : MExpr.
        Start symbol: toplevel. *)

  | MenhirState036 : ((('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 036.
        Stack shape : MExpr AppExpr.
        Start symbol: toplevel. *)

  | MenhirState039 : (('s, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 039.
        Stack shape : AppExpr.
        Start symbol: toplevel. *)

  | MenhirState040 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 040.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState045 : (('s, _menhir_box_toplevel) _menhir_cell1_LTExpr, _menhir_box_toplevel) _menhir_state
    (** State 045.
        Stack shape : LTExpr.
        Start symbol: toplevel. *)

  | MenhirState049 : (('s, _menhir_box_toplevel) _menhir_cell1_FunExpr, _menhir_box_toplevel) _menhir_state
    (** State 049.
        Stack shape : FunExpr.
        Start symbol: toplevel. *)

  | MenhirState053 : ((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 053.
        Stack shape : IF Expr.
        Start symbol: toplevel. *)

  | MenhirState055 : (((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 055.
        Stack shape : IF Expr Expr.
        Start symbol: toplevel. *)

  | MenhirState059 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 059.
        Stack shape : LET ID ID Expr.
        Start symbol: toplevel. *)

  | MenhirState062 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 062.
        Stack shape : LET ID.
        Start symbol: toplevel. *)

  | MenhirState064 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 064.
        Stack shape : LET ID Expr.
        Start symbol: toplevel. *)

  | MenhirState071 : ((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 071.
        Stack shape : MATCH Expr.
        Start symbol: toplevel. *)

  | MenhirState077 : (((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 077.
        Stack shape : MATCH Expr Expr ID ID.
        Start symbol: toplevel. *)

  | MenhirState083 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 083.
        Stack shape : LPAREN VarList ID.
        Start symbol: toplevel. *)

  | MenhirState087 : (('s, _menhir_box_toplevel) _menhir_cell1_SingleVar, _menhir_box_toplevel) _menhir_state
    (** State 087.
        Stack shape : SingleVar.
        Start symbol: toplevel. *)

  | MenhirState095 : (('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_state
    (** State 095.
        Stack shape : VarList.
        Start symbol: toplevel. *)

  | MenhirState097 : ((('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 097.
        Stack shape : VarList Expr.
        Start symbol: toplevel. *)

  | MenhirState103 : (('s, _menhir_box_toplevel) _menhir_cell1_SingleValue, _menhir_box_toplevel) _menhir_state
    (** State 103.
        Stack shape : SingleValue.
        Start symbol: toplevel. *)


and ('s, 'r) _menhir_cell1_AppExpr = 
  | MenhirCell1_AppExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_Expr = 
  | MenhirCell1_Expr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_FunExpr = 
  | MenhirCell1_FunExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_LTExpr = 
  | MenhirCell1_LTExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_MExpr = 
  | MenhirCell1_MExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_PMExpr = 
  | MenhirCell1_PMExpr of 's * ('s, 'r) _menhir_state * (Syntax.exp)

and ('s, 'r) _menhir_cell1_SingleValue = 
  | MenhirCell1_SingleValue of 's * ('s, 'r) _menhir_state * (Syntax.exval)

and ('s, 'r) _menhir_cell1_SingleVar = 
  | MenhirCell1_SingleVar of 's * ('s, 'r) _menhir_state * (string * Syntax.exval)

and ('s, 'r) _menhir_cell1_VarList = 
  | MenhirCell1_VarList of 's * ('s, 'r) _menhir_state * ((string * Syntax.exval) list)

and ('s, 'r) _menhir_cell1_FUN = 
  | MenhirCell1_FUN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 14 "bin/eval_ml_4/parser.mly"
       (Syntax.id)
# 236 "bin/eval_ml_4/parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 14 "bin/eval_ml_4/parser.mly"
       (Syntax.id)
# 243 "bin/eval_ml_4/parser.ml"
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
# 110 "bin/eval_ml_4/parser.mly"
         ( ILit i )
# 266 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_02 =
  fun i ->
    (
# 111 "bin/eval_ml_4/parser.mly"
       ( Var i )
# 274 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_03 =
  fun () ->
    (
# 112 "bin/eval_ml_4/parser.mly"
       ( BLit true )
# 282 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_04 =
  fun () ->
    (
# 113 "bin/eval_ml_4/parser.mly"
        ( BLit false )
# 290 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_05 =
  fun e ->
    (
# 114 "bin/eval_ml_4/parser.mly"
                       ( e )
# 298 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_06 =
  fun c e t ->
    (
# 115 "bin/eval_ml_4/parser.mly"
                                    ( IfExp (c, t, e) )
# 306 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_07 =
  fun e1 e2 e3 x y ->
    (
# 116 "bin/eval_ml_4/parser.mly"
                                                                        ( MatchExp (e1, e2, x, y, e3) )
# 314 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_08 =
  fun e1 e2 ->
    (
# 106 "bin/eval_ml_4/parser.mly"
                      ( AppExp (e1, e2) )
# 322 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_09 =
  fun e ->
    (
# 107 "bin/eval_ml_4/parser.mly"
          ( e )
# 330 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_10 =
  fun e1 e2 ->
    (
# 80 "bin/eval_ml_4/parser.mly"
                              ( ConsExp (e1, e2) )
# 338 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_11 =
  fun () ->
    (
# 81 "bin/eval_ml_4/parser.mly"
      ( NilExp )
# 346 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_12 =
  fun v1 v2 ->
    (
# 43 "bin/eval_ml_4/parser.mly"
                                   ( ConsV (v1, v2) )
# 354 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_13 =
  fun v ->
    (
# 44 "bin/eval_ml_4/parser.mly"
                ( v )
# 362 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_14 =
  fun () ->
    (
# 45 "bin/eval_ml_4/parser.mly"
      ( NilV )
# 370 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_15 =
  fun e ->
    (
# 76 "bin/eval_ml_4/parser.mly"
            ( e )
# 378 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_16 =
  fun e ->
    (
# 77 "bin/eval_ml_4/parser.mly"
             ( e )
# 386 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_17 =
  fun e x ->
    (
# 84 "bin/eval_ml_4/parser.mly"
                           ( FunExp (x, e) )
# 394 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_18 =
  fun e ->
    (
# 85 "bin/eval_ml_4/parser.mly"
            ( e )
# 402 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_19 =
  fun l r ->
    (
# 93 "bin/eval_ml_4/parser.mly"
                       ( BinOp (Lt, l, r) )
# 410 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_20 =
  fun e ->
    (
# 94 "bin/eval_ml_4/parser.mly"
           ( e )
# 418 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_21 =
  fun e1 e2 x ->
    (
# 88 "bin/eval_ml_4/parser.mly"
                                 ( LetExp (x, e1, e2) )
# 426 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_22 =
  fun e1 e2 x y ->
    (
# 89 "bin/eval_ml_4/parser.mly"
                                                    ( LetRecExp (x, y, e1, e2) )
# 434 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_23 =
  fun e ->
    (
# 90 "bin/eval_ml_4/parser.mly"
           ( e )
# 442 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_24 =
  fun l r ->
    (
# 102 "bin/eval_ml_4/parser.mly"
                         ( BinOp (Mult, l, r) )
# 450 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_25 =
  fun e ->
    (
# 103 "bin/eval_ml_4/parser.mly"
            ( e )
# 458 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_26 =
  fun l r ->
    (
# 97 "bin/eval_ml_4/parser.mly"
                        ( BinOp (Plus, l, r) )
# 466 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_27 =
  fun l r ->
    (
# 98 "bin/eval_ml_4/parser.mly"
                         ( BinOp (Minus, l, r) )
# 474 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_28 =
  fun e ->
    (
# 99 "bin/eval_ml_4/parser.mly"
          ( e )
# 482 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_29 =
  fun e v x ->
    (
# 68 "bin/eval_ml_4/parser.mly"
                                                                  ( ProcV (x, e, v) )
# 490 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_30 =
  fun e v x y ->
    (
# 71 "bin/eval_ml_4/parser.mly"
                                                                              ( RecProcV (x, y, e, v) )
# 498 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_31 =
  fun i ->
    (
# 48 "bin/eval_ml_4/parser.mly"
         ( IntV i )
# 506 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_32 =
  fun () ->
    (
# 49 "bin/eval_ml_4/parser.mly"
       ( BoolV true )
# 514 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_33 =
  fun () ->
    (
# 50 "bin/eval_ml_4/parser.mly"
        ( BoolV false )
# 522 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_34 =
  fun v ->
    (
# 51 "bin/eval_ml_4/parser.mly"
              ( v )
# 530 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_35 =
  fun v ->
    (
# 52 "bin/eval_ml_4/parser.mly"
                 ( v )
# 538 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_36 =
  fun i x ->
    (
# 33 "bin/eval_ml_4/parser.mly"
                 ( (x, IntV i) )
# 546 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_37 =
  fun x ->
    (
# 34 "bin/eval_ml_4/parser.mly"
               ( (x, BoolV true) )
# 554 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_38 =
  fun x ->
    (
# 35 "bin/eval_ml_4/parser.mly"
                ( (x, BoolV false) )
# 562 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_39 =
  fun p x ->
    (
# 36 "bin/eval_ml_4/parser.mly"
                      ( (x, p) )
# 570 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_40 =
  fun r x ->
    (
# 37 "bin/eval_ml_4/parser.mly"
                         ( (x, r) )
# 578 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_41 =
  fun hd tl ->
    (
# 28 "bin/eval_ml_4/parser.mly"
                                ( hd::tl )
# 586 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_42 =
  fun v ->
    (
# 29 "bin/eval_ml_4/parser.mly"
              ( v::[] )
# 594 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_43 =
  fun () ->
    (
# 30 "bin/eval_ml_4/parser.mly"
  ( [] )
# 602 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_44 =
  fun e v vl ->
    (
# 22 "bin/eval_ml_4/parser.mly"
                                                   ( EvalExp (vl, e, v) )
# 610 "bin/eval_ml_4/parser.ml"
     : (Syntax.judgement))

let _menhir_action_45 =
  fun c e vl ->
    (
# 23 "bin/eval_ml_4/parser.mly"
                                                 ( EvalExp (vl, e, c) )
# 618 "bin/eval_ml_4/parser.ml"
     : (Syntax.judgement))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ARROW ->
        "ARROW"
    | BAR ->
        "BAR"
    | COMMA ->
        "COMMA"
    | CONS ->
        "CONS"
    | ELSE ->
        "ELSE"
    | EQ ->
        "EQ"
    | EVALTO ->
        "EVALTO"
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
    | INTV _ ->
        "INTV"
    | LBRACKET ->
        "LBRACKET"
    | LET ->
        "LET"
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
    | NIL ->
        "NIL"
    | PLUS ->
        "PLUS"
    | RBRACKET ->
        "RBRACKET"
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
  
  let rec _menhir_run_108 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let MenhirCell1_Expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_VarList (_menhir_stack, _, vl) = _menhir_stack in
      let c = _v in
      let _v = _menhir_action_45 c e vl in
      MenhirBox_toplevel _v
  
  let rec _menhir_run_107 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleValue -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let MenhirCell1_SingleValue (_menhir_stack, _menhir_s, v1) = _menhir_stack in
      let v2 = _v in
      let _v = _menhir_action_12 v1 v2 in
      _menhir_goto_ConsVExpr _menhir_stack _v _menhir_s
  
  and _menhir_goto_ConsVExpr : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState097 ->
          _menhir_run_108 _menhir_stack _v
      | MenhirState103 ->
          _menhir_run_107 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v in
              let _v = _menhir_action_37 x in
              _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | LPAREN ->
              let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState002
          | INTV _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (x, i) = (_v, _v_0) in
              let _v = _menhir_action_36 i x in
              _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v in
              let _v = _menhir_action_38 x in
              _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_SingleVar : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_SingleVar (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ID _v ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState087
          | RPAREN | TURNSTILE ->
              let _v = _menhir_action_43 () in
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | RPAREN | TURNSTILE ->
          let v = _v in
          let _v = _menhir_action_42 v in
          _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_088 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleVar -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SingleVar (_menhir_stack, _menhir_s, hd) = _menhir_stack in
      let tl = _v in
      let _v = _menhir_action_41 hd tl in
      _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_VarList : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState004 ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_094 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_VarList (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | TURNSTILE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_057_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState095
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState095
          | LET ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState095
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState095
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState095
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_095 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState095 _tok
  
  and _menhir_run_039 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState039
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState039
      | INTV _v_1 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_1 in
          let _v = _menhir_action_01 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState039
      | ID _v_3 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_3 in
          let _v = _menhir_action_02 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | CONS | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_25 e in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_037 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_AppExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AppExpr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_08 e1 e2 in
      _menhir_goto_AppExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_AppExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState077 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState049 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState045 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState040 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState033 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState035 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_036 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | INTV _v_1 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_1 in
          let _v = _menhir_action_01 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | ID _v_3 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_3 in
          let _v = _menhir_action_02 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | CONS | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_MExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_24 l r in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NIL ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_057_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | LET ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_016 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState016 _tok
  
  and _menhir_run_057_spec_016 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState016 _tok
  
  and _menhir_run_068 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ARROW ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | TRUE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_03 () in
                      _menhir_run_038_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | NIL ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_11 () in
                      _menhir_run_057_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | MATCH ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
                  | LPAREN ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
                  | LET ->
                      _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
                  | INTV _v_2 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_2 in
                      let _v = _menhir_action_01 i in
                      _menhir_run_038_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | IF ->
                      _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
                  | ID _v_4 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_4 in
                      let _v = _menhir_action_02 i in
                      _menhir_run_038_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | FUN ->
                      _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
                  | FALSE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_04 () in
                      _menhir_run_038_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_071 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState071 _tok
  
  and _menhir_run_057_spec_071 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState071 _tok
  
  and _menhir_run_072 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | BAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ID _v_0 ->
              let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | CONS ->
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
                              _menhir_run_038_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | NIL ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_11 () in
                              _menhir_run_057_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
                          | LPAREN ->
                              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
                          | LET ->
                              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
                          | INTV _v_4 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_4 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_038_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
                          | ID _v_6 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_6 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_038_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_038_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_077 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState077 _tok
  
  and _menhir_run_057_spec_077 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_078 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_Expr (_menhir_stack, _, e2) = _menhir_stack in
      let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let e3 = _v in
      let _v = _menhir_action_07 e1 e2 e3 x y in
      _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_AExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_038_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState083 ->
          _menhir_run_038_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState016 ->
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState071 ->
          _menhir_run_038_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState077 ->
          _menhir_run_038_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState017 ->
          _menhir_run_038_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState062 ->
          _menhir_run_038_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState064 ->
          _menhir_run_038_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState024 ->
          _menhir_run_038_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState059 ->
          _menhir_run_038_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState026 ->
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_038_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState055 ->
          _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState049 ->
          _menhir_run_038_spec_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState030 ->
          _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState045 ->
          _menhir_run_038_spec_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState040 ->
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState033 ->
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState035 ->
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState039 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState036 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_038_spec_083 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState083 _tok
  
  and _menhir_run_038_spec_013 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState013 _tok
  
  and _menhir_run_038_spec_017 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState017 _tok
  
  and _menhir_run_038_spec_062 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState062 _tok
  
  and _menhir_run_038_spec_064 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState064 _tok
  
  and _menhir_run_038_spec_024 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState024 _tok
  
  and _menhir_run_038_spec_059 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState059 _tok
  
  and _menhir_run_038_spec_026 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState026 _tok
  
  and _menhir_run_038_spec_053 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState053 _tok
  
  and _menhir_run_038_spec_055 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState055 _tok
  
  and _menhir_run_038_spec_049 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FunExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState049 _tok
  
  and _menhir_run_038_spec_030 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState030 _tok
  
  and _menhir_run_038_spec_045 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState045 _tok
  
  and _menhir_run_038_spec_040 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState040 _tok
  
  and _menhir_run_038_spec_033 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState033 _tok
  
  and _menhir_run_038_spec_035 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState035 _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NIL ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_057_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState017
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState017
      | LET ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState017
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState017
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState017
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_017 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_066 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_05 e in
          _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
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
                                  _menhir_run_038_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | NIL ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_11 () in
                                  _menhir_run_057_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | MATCH ->
                                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
                              | LPAREN ->
                                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
                              | LET ->
                                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
                              | INTV _v_3 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_3 in
                                  let _v = _menhir_action_01 i in
                                  _menhir_run_038_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | IF ->
                                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
                              | ID _v_5 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_5 in
                                  let _v = _menhir_action_02 i in
                                  _menhir_run_038_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | FUN ->
                                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
                              | FALSE ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_04 () in
                                  _menhir_run_038_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                  _menhir_run_038_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | NIL ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_11 () in
                  _menhir_run_057_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | MATCH ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState062
              | LPAREN ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState062
              | LET ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState062
              | INTV _v_10 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_10 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_038_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState062
              | ID _v_12 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_12 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_038_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState062
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_038_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_024 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState024 _tok
  
  and _menhir_run_058 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_057_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState059
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState059
          | LET ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState059
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState059
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState059
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_059 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_060 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_22 e1 e2 x y in
      _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_LetExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_18 e in
      _menhir_goto_FunExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_FunExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState049 ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState095 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState077 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_050 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_FunExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_FunExpr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | CONS ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_049 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FunExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NIL ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LET ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_051 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FunExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_FunExpr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_10 e1 e2 in
      _menhir_goto_ConsExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_ConsExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_057_spec_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState083 ->
          _menhir_run_057_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_057_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState016 ->
          _menhir_run_057_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState071 ->
          _menhir_run_057_spec_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState077 ->
          _menhir_run_057_spec_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState017 ->
          _menhir_run_057_spec_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState062 ->
          _menhir_run_057_spec_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState064 ->
          _menhir_run_057_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState024 ->
          _menhir_run_057_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState059 ->
          _menhir_run_057_spec_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState026 ->
          _menhir_run_057_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_057_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState055 ->
          _menhir_run_057_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState049 ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_057_spec_095 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState095 _tok
  
  and _menhir_run_096 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | EVALTO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_32 () in
              _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState097 _tok
          | NIL ->
              let _v = _menhir_action_14 () in
              _menhir_run_108 _menhir_stack _v
          | LPAREN ->
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState097
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_31 i in
              _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState097 _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_33 () in
              _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState097 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_102 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_SingleValue (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | CONS ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_103 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleValue -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_32 () in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState103 _tok
      | NIL ->
          let _v = _menhir_action_14 () in
          _menhir_run_107 _menhir_stack _v
      | LPAREN ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_31 i in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState103 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_33 () in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState103 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_104 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleValue as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_SingleValue (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | CONS ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004
      | RPAREN ->
          let _v = _menhir_action_43 () in
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_005 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_VarList (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | REC ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | ID _v_0 ->
                      let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | EQ ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | FUN ->
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
                                          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | NIL ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_11 () in
                                          _menhir_run_057_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | MATCH ->
                                          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LPAREN ->
                                          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LET ->
                                          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | INTV _v_4 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_4 in
                                          let _v = _menhir_action_01 i in
                                          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | IF ->
                                          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | ID _v_6 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_6 in
                                          let _v = _menhir_action_02 i in
                                          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | FUN ->
                                          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | FALSE ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_04 () in
                                          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
              | FUN ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | ID _v_9 ->
                      let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_9) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ARROW ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | TRUE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_03 () in
                              _menhir_run_038_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | NIL ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_11 () in
                              _menhir_run_057_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
                          | LPAREN ->
                              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
                          | LET ->
                              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
                          | INTV _v_12 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_12 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_038_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
                          | ID _v_14 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_14 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_038_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_038_spec_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_057_spec_013 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_079 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_30 e v x y in
          _menhir_goto_RecProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_RecProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState097 ->
          _menhir_run_105_spec_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState103 ->
          _menhir_run_105_spec_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState002 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_105_spec_097 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_35 v in
      _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState097 _tok
  
  and _menhir_run_105_spec_103 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleValue -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_35 v in
      _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState103 _tok
  
  and _menhir_run_091 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let r = _v in
      let _v = _menhir_action_40 r x in
      _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_026 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NIL ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_057_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | LET ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_026 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState026 _tok
  
  and _menhir_run_052 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_057_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | LET ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_053 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState053 _tok
  
  and _menhir_run_054 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_057_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | LET ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_055 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_056 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_Expr (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_Expr (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_06 c e t in
      _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_028 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
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
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | MATCH ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | LPAREN ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | LET ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | INTV _v_1 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_1 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | ID _v_3 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_3 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_083 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_084 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_29 e v x in
          _menhir_goto_ProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_ProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState097 ->
          _menhir_run_106_spec_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState103 ->
          _menhir_run_106_spec_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState002 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_106_spec_097 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_34 v in
      _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState097 _tok
  
  and _menhir_run_106_spec_103 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleValue -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_34 v in
      _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState103 _tok
  
  and _menhir_run_092 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let p = _v in
      let _v = _menhir_action_39 p x in
      _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_057_spec_062 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState062 _tok
  
  and _menhir_run_063 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NIL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_057_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState064
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState064
          | LET ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState064
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState064
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState064
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_057_spec_064 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_065 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_21 e1 e2 x in
      _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_048 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONS ->
          let _menhir_stack = MenhirCell1_FunExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let e = _v in
          let _v = _menhir_action_15 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_Expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState077 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState071 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState064 ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState062 ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState024 ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_047 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_17 e x in
      _menhir_goto_FunExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_MExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState077 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState049 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState045 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState040 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState033 ->
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_042 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let e = _v in
          let _v = _menhir_action_28 e in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_035 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState035
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState035
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState035
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_PMExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState045 ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState095 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState077 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState049 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_046 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MULT | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let MenhirCell1_LTExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_19 l r in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_033 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_040 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState040
      | LPAREN ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState040
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState040
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
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
              _menhir_run_038_spec_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState045
          | LPAREN ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState045
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState045
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | MATCH | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let e = _v in
          let _v = _menhir_action_23 e in
          _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_032 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MULT | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let e = _v in
          let _v = _menhir_action_20 e in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_041 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_27 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_034 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONS | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MATCH | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_26 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | TURNSTILE ->
          let _v = _menhir_action_43 () in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
