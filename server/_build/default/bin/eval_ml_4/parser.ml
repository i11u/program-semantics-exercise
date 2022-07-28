
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
    | MULT
    | MINUS
    | MATCH
    | LT
    | LPAREN
    | LET
    | LBRACKET_RBRACKET
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
    | CONSTRUCT
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

  | MenhirState015 : (('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_state
    (** State 015.
        Stack shape : MATCH.
        Start symbol: toplevel. *)

  | MenhirState016 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 016.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState023 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 023.
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

  | MenhirState046 : (('s, _menhir_box_toplevel) _menhir_cell1_LTExpr, _menhir_box_toplevel) _menhir_state
    (** State 046.
        Stack shape : LTExpr.
        Start symbol: toplevel. *)

  | MenhirState051 : (('s, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 051.
        Stack shape : Expr.
        Start symbol: toplevel. *)

  | MenhirState055 : ((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 055.
        Stack shape : IF Expr.
        Start symbol: toplevel. *)

  | MenhirState057 : (((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 057.
        Stack shape : IF Expr Expr.
        Start symbol: toplevel. *)

  | MenhirState060 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 060.
        Stack shape : LET ID ID Expr.
        Start symbol: toplevel. *)

  | MenhirState063 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 063.
        Stack shape : LET ID.
        Start symbol: toplevel. *)

  | MenhirState065 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 065.
        Stack shape : LET ID Expr.
        Start symbol: toplevel. *)

  | MenhirState072 : ((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 072.
        Stack shape : MATCH Expr.
        Start symbol: toplevel. *)

  | MenhirState078 : (((('s, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 078.
        Stack shape : MATCH Expr Expr ID ID.
        Start symbol: toplevel. *)

  | MenhirState084 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 084.
        Stack shape : LPAREN VarList ID.
        Start symbol: toplevel. *)

  | MenhirState088 : (('s, _menhir_box_toplevel) _menhir_cell1_SingleVar, _menhir_box_toplevel) _menhir_state
    (** State 088.
        Stack shape : SingleVar.
        Start symbol: toplevel. *)

  | MenhirState098 : (('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_state
    (** State 098.
        Stack shape : VarList.
        Start symbol: toplevel. *)

  | MenhirState100 : ((('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 100.
        Stack shape : VarList Expr.
        Start symbol: toplevel. *)

  | MenhirState102 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 102.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState111 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 111.
        Stack shape : LPAREN VarList ID ID.
        Start symbol: toplevel. *)

  | MenhirState116 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 116.
        Stack shape : LPAREN VarList ID.
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
  | MenhirCell1_SingleVar of 's * ('s, 'r) _menhir_state * (string * Syntax.exval)

and ('s, 'r) _menhir_cell1_VarList = 
  | MenhirCell1_VarList of 's * ('s, 'r) _menhir_state * ((string * Syntax.exval) list)

and ('s, 'r) _menhir_cell1_FUN = 
  | MenhirCell1_FUN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 14 "bin/eval_ml_4/parser.mly"
       (Syntax.id)
# 240 "bin/eval_ml_4/parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 14 "bin/eval_ml_4/parser.mly"
       (Syntax.id)
# 247 "bin/eval_ml_4/parser.ml"
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
# 99 "bin/eval_ml_4/parser.mly"
         ( ILit i )
# 270 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_02 =
  fun i ->
    (
# 100 "bin/eval_ml_4/parser.mly"
       ( Var i )
# 278 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_03 =
  fun () ->
    (
# 101 "bin/eval_ml_4/parser.mly"
       ( BLit true )
# 286 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_04 =
  fun () ->
    (
# 102 "bin/eval_ml_4/parser.mly"
        ( BLit false )
# 294 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_05 =
  fun e ->
    (
# 103 "bin/eval_ml_4/parser.mly"
                       ( e )
# 302 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_06 =
  fun () ->
    (
# 104 "bin/eval_ml_4/parser.mly"
                    ( NilExp )
# 310 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_07 =
  fun e1 e2 ->
    (
# 95 "bin/eval_ml_4/parser.mly"
                      ( AppExp (e1, e2) )
# 318 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_08 =
  fun e ->
    (
# 96 "bin/eval_ml_4/parser.mly"
          ( e )
# 326 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_09 =
  fun e1 e2 ->
    (
# 66 "bin/eval_ml_4/parser.mly"
                            ( ConsExp (e1, e2) )
# 334 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_10 =
  fun e ->
    (
# 58 "bin/eval_ml_4/parser.mly"
            ( e )
# 342 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_11 =
  fun e ->
    (
# 59 "bin/eval_ml_4/parser.mly"
             ( e )
# 350 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_12 =
  fun e ->
    (
# 60 "bin/eval_ml_4/parser.mly"
            ( e )
# 358 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_13 =
  fun e ->
    (
# 61 "bin/eval_ml_4/parser.mly"
           ( e )
# 366 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_14 =
  fun e ->
    (
# 62 "bin/eval_ml_4/parser.mly"
           ( e )
# 374 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_15 =
  fun e ->
    (
# 63 "bin/eval_ml_4/parser.mly"
              ( e )
# 382 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_16 =
  fun e x ->
    (
# 69 "bin/eval_ml_4/parser.mly"
                        ( FunExp (x, e) )
# 390 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_17 =
  fun c e t ->
    (
# 72 "bin/eval_ml_4/parser.mly"
                                    ( IfExp (c, t, e) )
# 398 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_18 =
  fun l r ->
    (
# 82 "bin/eval_ml_4/parser.mly"
                       ( BinOp (Lt, l, r) )
# 406 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_19 =
  fun e ->
    (
# 83 "bin/eval_ml_4/parser.mly"
           ( e )
# 414 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_20 =
  fun e1 e2 x ->
    (
# 78 "bin/eval_ml_4/parser.mly"
                                 ( LetExp (x, e1, e2) )
# 422 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_21 =
  fun e1 e2 x y ->
    (
# 79 "bin/eval_ml_4/parser.mly"
                                                    ( LetRecExp (x, y, e1, e2) )
# 430 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_22 =
  fun l r ->
    (
# 91 "bin/eval_ml_4/parser.mly"
                         ( BinOp (Mult, l, r) )
# 438 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_23 =
  fun e ->
    (
# 92 "bin/eval_ml_4/parser.mly"
            ( e )
# 446 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_24 =
  fun e1 e2 e3 x y ->
    (
# 75 "bin/eval_ml_4/parser.mly"
                                                                                           ( MatchExp (e1, e2, x, y, e3) )
# 454 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_25 =
  fun l r ->
    (
# 86 "bin/eval_ml_4/parser.mly"
                        ( BinOp (Plus, l, r) )
# 462 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_26 =
  fun l r ->
    (
# 87 "bin/eval_ml_4/parser.mly"
                         ( BinOp (Minus, l, r) )
# 470 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_27 =
  fun e ->
    (
# 88 "bin/eval_ml_4/parser.mly"
          ( e )
# 478 "bin/eval_ml_4/parser.ml"
     : (Syntax.exp))

let _menhir_action_28 =
  fun e v x ->
    (
# 40 "bin/eval_ml_4/parser.mly"
                                                                  ( ProcV (x, e, v) )
# 486 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_29 =
  fun e v x y ->
    (
# 43 "bin/eval_ml_4/parser.mly"
                                                                              ( RecProcV (x, y, e, v) )
# 494 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_30 =
  fun v x ->
    (
# 53 "bin/eval_ml_4/parser.mly"
                  ( (x, v) )
# 502 "bin/eval_ml_4/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_31 =
  fun i ->
    (
# 29 "bin/eval_ml_4/parser.mly"
         ( IntV i )
# 510 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_32 =
  fun () ->
    (
# 30 "bin/eval_ml_4/parser.mly"
       ( BoolV true )
# 518 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_33 =
  fun () ->
    (
# 31 "bin/eval_ml_4/parser.mly"
        ( BoolV false )
# 526 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_34 =
  fun v ->
    (
# 32 "bin/eval_ml_4/parser.mly"
              ( v )
# 534 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_35 =
  fun v ->
    (
# 33 "bin/eval_ml_4/parser.mly"
                 ( v )
# 542 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_36 =
  fun () ->
    (
# 34 "bin/eval_ml_4/parser.mly"
                    ( NilV )
# 550 "bin/eval_ml_4/parser.ml"
     : (Syntax.exval))

let _menhir_action_37 =
  fun hd tl ->
    (
# 48 "bin/eval_ml_4/parser.mly"
                                ( hd::tl )
# 558 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_38 =
  fun v ->
    (
# 49 "bin/eval_ml_4/parser.mly"
              ( v::[] )
# 566 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_39 =
  fun () ->
    (
# 50 "bin/eval_ml_4/parser.mly"
  ( [] )
# 574 "bin/eval_ml_4/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_40 =
  fun e v vl ->
    (
# 24 "bin/eval_ml_4/parser.mly"
                                             ( EvalExp (vl, e, v) )
# 582 "bin/eval_ml_4/parser.ml"
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
    | CONSTRUCT ->
        "CONSTRUCT"
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
    | LBRACKET_RBRACKET ->
        "LBRACKET_RBRACKET"
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
  
  let rec _menhir_run_122 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let MenhirCell1_Expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_VarList (_menhir_stack, _, vl) = _menhir_stack in
      let v = _v in
      let _v = _menhir_action_40 e v vl in
      MenhirBox_toplevel _v
  
  let rec _menhir_run_124_spec_100 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let v = _v in
      let _v = _menhir_action_34 v in
      _menhir_run_122 _menhir_stack _v
  
  let rec _menhir_run_123_spec_100 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let v = _v in
      let _v = _menhir_action_35 v in
      _menhir_run_122 _menhir_stack _v
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_32 () in
              _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, MenhirState002) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ID _v ->
                  _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004
              | RPAREN ->
                  let _v = _menhir_action_39 () in
                  _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004 _tok
              | _ ->
                  _eRR ())
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_36 () in
              _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_31 i in
              _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_33 () in
              _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_093 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let v = _v in
      let _v = _menhir_action_30 v x in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_SingleVar (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ID _v ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState088
          | RPAREN | TURNSTILE ->
              let _v = _menhir_action_39 () in
              _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | RPAREN | TURNSTILE ->
          let v = _v in
          let _v = _menhir_action_38 v in
          _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_089 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleVar -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SingleVar (_menhir_stack, _menhir_s, hd) = _menhir_stack in
      let tl = _v in
      let _v = _menhir_action_37 hd tl in
      _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_VarList : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState102 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState088 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState004 ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_103 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
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
                                          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | MATCH ->
                                          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState111
                                      | LPAREN ->
                                          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState111
                                      | LET ->
                                          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState111
                                      | LBRACKET_RBRACKET ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_06 () in
                                          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | INTV _v_4 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_4 in
                                          let _v = _menhir_action_01 i in
                                          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | IF ->
                                          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState111
                                      | ID _v_6 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_6 in
                                          let _v = _menhir_action_02 i in
                                          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | FUN ->
                                          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState111
                                      | FALSE ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_04 () in
                                          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                              _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
                          | LPAREN ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
                          | LET ->
                              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
                          | LBRACKET_RBRACKET ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_06 () in
                              _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | INTV _v_12 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_12 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
                          | ID _v_14 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_14 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_111 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState111 _tok
  
  and _menhir_run_039 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState039
      | LBRACKET_RBRACKET ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v_2 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_2 in
          let _v = _menhir_action_01 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v_4 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_4 in
          let _v = _menhir_action_02 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_23 e in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_037 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_AppExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AppExpr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_07 e1 e2 in
      _menhir_goto_AppExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_AppExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState098 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState063 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState065 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState046 ->
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
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | LBRACKET_RBRACKET ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v_2 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_2 in
          let _v = _menhir_action_01 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ID _v_4 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_4 in
          let _v = _menhir_action_02 i in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_MExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_22 l r in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | LET ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState016
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_016 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState016 _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | LET ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_015 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState015 _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
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
                                  _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | MATCH ->
                                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState023
                              | LPAREN ->
                                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState023
                              | LET ->
                                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState023
                              | LBRACKET_RBRACKET ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_06 () in
                                  _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | INTV _v_3 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_3 in
                                  let _v = _menhir_action_01 i in
                                  _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | IF ->
                                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState023
                              | ID _v_5 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_5 in
                                  let _v = _menhir_action_02 i in
                                  _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | FUN ->
                                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState023
                              | FALSE ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_04 () in
                                  _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                  _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | MATCH ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState063
              | LPAREN ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState063
              | LET ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState063
              | LBRACKET_RBRACKET ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_06 () in
                  _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | INTV _v_10 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_10 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState063
              | ID _v_12 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_12 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState063
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_023 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState023 _tok
  
  and _menhir_run_026 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | LET ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_026 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState026 _tok
  
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
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | LPAREN ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | LET ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | LBRACKET_RBRACKET ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_06 () in
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | INTV _v_2 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_2 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState030
              | ID _v_4 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_4 in
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
  
  and _menhir_run_038_spec_030 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState030 _tok
  
  and _menhir_run_038_spec_063 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState063 _tok
  
  and _menhir_goto_MExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState116 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState065 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState063 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState040 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState033 ->
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_043 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_27 e in
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
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState035
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_035 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState035 _tok
  
  and _menhir_goto_PMExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState065 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState063 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_047 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_LTExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_18 l r in
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
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_033 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState033 _tok
  
  and _menhir_run_040 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState040
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_040 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState040 _tok
  
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
              _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_13 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_038_spec_046 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState046 _tok
  
  and _menhir_goto_Expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState116 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState065 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState063 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState026 ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_117 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_28 e v x in
          _menhir_goto_ProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_ProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState100 ->
          _menhir_run_124_spec_100 _menhir_stack _v
      | MenhirState002 ->
          _menhir_run_095_spec_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_095_spec_002 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_34 v in
      _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_051 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MATCH ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState051
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState051
      | LET ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState051
      | LBRACKET_RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_06 () in
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState051
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState051
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_051 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState051 _tok
  
  and _menhir_run_112 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_29 e v x y in
          _menhir_goto_RecProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_RecProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState100 ->
          _menhir_run_123_spec_100 _menhir_stack _v
      | MenhirState002 ->
          _menhir_run_094_spec_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_094_spec_002 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let v = _v in
      let _v = _menhir_action_35 v in
      _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_099 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | EVALTO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _v = _menhir_action_32 () in
              _menhir_run_122 _menhir_stack _v
          | LPAREN ->
              let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, MenhirState100) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ID _v ->
                  _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState102
              | RPAREN ->
                  let _v = _menhir_action_39 () in
                  _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState102 _tok
              | _ ->
                  _eRR ())
          | LBRACKET_RBRACKET ->
              let _v = _menhir_action_36 () in
              _menhir_run_122 _menhir_stack _v
          | INTV _v_4 ->
              let i = _v_4 in
              let _v = _menhir_action_31 i in
              _menhir_run_122 _menhir_stack _v
          | FALSE ->
              let _v = _menhir_action_33 () in
              _menhir_run_122 _menhir_stack _v
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_085 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_28 e v x in
          _menhir_goto_ProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_080 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_29 e v x y in
          _menhir_goto_RecProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_079 : type  ttv_stack. ((((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
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
  
  and _menhir_run_073 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
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
                              _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
                          | LPAREN ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
                          | LET ->
                              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
                          | LBRACKET_RBRACKET ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_06 () in
                              _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | INTV _v_4 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_4 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
                          | ID _v_6 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_6 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_078 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState078 _tok
  
  and _menhir_run_069 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
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
                      _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | MATCH ->
                      _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
                  | LPAREN ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
                  | LET ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
                  | LBRACKET_RBRACKET ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_06 () in
                      _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | INTV _v_2 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_2 in
                      let _v = _menhir_action_01 i in
                      _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | IF ->
                      _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
                  | ID _v_4 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let i = _v_4 in
                      let _v = _menhir_action_02 i in
                      _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | FUN ->
                      _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
                  | FALSE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_04 () in
                      _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_038_spec_072 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MATCH, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState072 _tok
  
  and _menhir_run_067 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
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
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_AExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState098 ->
          _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState116 ->
          _menhir_run_038_spec_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState111 ->
          _menhir_run_038_spec_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState084 ->
          _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState015 ->
          _menhir_run_038_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState072 ->
          _menhir_run_038_spec_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState078 ->
          _menhir_run_038_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState016 ->
          _menhir_run_038_spec_016 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState063 ->
          _menhir_run_038_spec_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState065 ->
          _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState023 ->
          _menhir_run_038_spec_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState060 ->
          _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState026 ->
          _menhir_run_038_spec_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState055 ->
          _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState057 ->
          _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState030 ->
          _menhir_run_038_spec_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState051 ->
          _menhir_run_038_spec_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState046 ->
          _menhir_run_038_spec_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_038_spec_098 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState098 _tok
  
  and _menhir_run_038_spec_116 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState116 _tok
  
  and _menhir_run_038_spec_084 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState084 _tok
  
  and _menhir_run_038_spec_013 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState013 _tok
  
  and _menhir_run_038_spec_065 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState065 _tok
  
  and _menhir_run_038_spec_060 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState060 _tok
  
  and _menhir_run_038_spec_055 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState055 _tok
  
  and _menhir_run_038_spec_057 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState057 _tok
  
  and _menhir_run_066 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
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
  
  and _menhir_run_064 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState065
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState065
          | LET ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState065
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState065
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState065
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_061 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_21 e1 e2 x y in
          _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_059 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
          | LET ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_058 : type  ttv_stack. ((((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
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
  
  and _menhir_run_056 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
          | LET ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_054 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | LET ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
      | CONSTRUCT ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_Expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_Expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_09 e1 e2 in
          let e = _v in
          let _v = _menhir_action_11 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_050 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CONSTRUCT ->
          let _menhir_stack = MenhirCell1_Expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | ELSE | EVALTO | IN | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_16 e x in
          let e = _v in
          let _v = _menhir_action_10 e in
          _menhir_goto_Expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
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
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | RBRACKET | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_19 e in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_041 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_26 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_034 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | CONSTRUCT | ELSE | EVALTO | IN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | WITH ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_25 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_097 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_VarList (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | TURNSTILE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | MATCH ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState098
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState098
          | LET ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState098
          | LBRACKET_RBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_06 () in
              _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_2 in
              let _v = _menhir_action_01 i in
              _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState098
          | ID _v_4 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_4 in
              let _v = _menhir_action_02 i in
              _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState098
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_038_spec_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
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
                                      | MATCH ->
                                          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LPAREN ->
                                          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LET ->
                                          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LBRACKET_RBRACKET ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_06 () in
                                          _menhir_run_038_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                              _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | MATCH ->
                              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
                          | LPAREN ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
                          | LET ->
                              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
                          | LBRACKET_RBRACKET ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_06 () in
                              _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | INTV _v_12 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_12 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
                          | ID _v_14 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_14 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_038_spec_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  let rec _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | TURNSTILE ->
          let _v = _menhir_action_39 () in
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
