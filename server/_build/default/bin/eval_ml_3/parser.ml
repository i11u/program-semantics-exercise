
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | TURNSTILE
    | TRUE
    | THEN
    | RPAREN
    | REC
    | RBRACKET
    | PLUS
    | MULT
    | MINUS
    | LT
    | LPAREN
    | LET
    | LBRACKET
    | INTV of (
# 13 "bin/eval_ml_3/parser.mly"
       (int)
# 28 "bin/eval_ml_3/parser.ml"
  )
    | IN
    | IF
    | ID of (
# 12 "bin/eval_ml_3/parser.mly"
       (Syntax.id)
# 35 "bin/eval_ml_3/parser.ml"
  )
    | FUN
    | FALSE
    | EVALTO
    | EQ
    | ELSE
    | COMMA
    | ARROW
  
end

include MenhirBasics

# 1 "bin/eval_ml_3/parser.mly"
  
open Syntax

# 53 "bin/eval_ml_3/parser.ml"

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

  | MenhirState015 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 015.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState022 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 022.
        Stack shape : LET ID ID.
        Start symbol: toplevel. *)

  | MenhirState024 : (('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_state
    (** State 024.
        Stack shape : IF.
        Start symbol: toplevel. *)

  | MenhirState028 : (('s, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 028.
        Stack shape : FUN ID.
        Start symbol: toplevel. *)

  | MenhirState031 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 031.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState033 : (('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_state
    (** State 033.
        Stack shape : MExpr.
        Start symbol: toplevel. *)

  | MenhirState034 : ((('s, _menhir_box_toplevel) _menhir_cell1_MExpr, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 034.
        Stack shape : MExpr AppExpr.
        Start symbol: toplevel. *)

  | MenhirState037 : (('s, _menhir_box_toplevel) _menhir_cell1_AppExpr, _menhir_box_toplevel) _menhir_state
    (** State 037.
        Stack shape : AppExpr.
        Start symbol: toplevel. *)

  | MenhirState038 : (('s, _menhir_box_toplevel) _menhir_cell1_PMExpr, _menhir_box_toplevel) _menhir_state
    (** State 038.
        Stack shape : PMExpr.
        Start symbol: toplevel. *)

  | MenhirState043 : (('s, _menhir_box_toplevel) _menhir_cell1_LTExpr, _menhir_box_toplevel) _menhir_state
    (** State 043.
        Stack shape : LTExpr.
        Start symbol: toplevel. *)

  | MenhirState048 : ((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 048.
        Stack shape : IF Expr.
        Start symbol: toplevel. *)

  | MenhirState050 : (((('s, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 050.
        Stack shape : IF Expr Expr.
        Start symbol: toplevel. *)

  | MenhirState053 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 053.
        Stack shape : LET ID ID Expr.
        Start symbol: toplevel. *)

  | MenhirState056 : (('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 056.
        Stack shape : LET ID.
        Start symbol: toplevel. *)

  | MenhirState058 : ((('s, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 058.
        Stack shape : LET ID Expr.
        Start symbol: toplevel. *)

  | MenhirState066 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 066.
        Stack shape : LPAREN VarList ID.
        Start symbol: toplevel. *)

  | MenhirState070 : (('s, _menhir_box_toplevel) _menhir_cell1_SingleVar, _menhir_box_toplevel) _menhir_state
    (** State 070.
        Stack shape : SingleVar.
        Start symbol: toplevel. *)

  | MenhirState078 : (('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_state
    (** State 078.
        Stack shape : VarList.
        Start symbol: toplevel. *)

  | MenhirState080 : ((('s, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_state
    (** State 080.
        Stack shape : VarList Expr.
        Start symbol: toplevel. *)

  | MenhirState082 : (('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_state
    (** State 082.
        Stack shape : LPAREN.
        Start symbol: toplevel. *)

  | MenhirState091 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 091.
        Stack shape : LPAREN VarList ID ID.
        Start symbol: toplevel. *)

  | MenhirState096 : ((('s, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID, _menhir_box_toplevel) _menhir_state
    (** State 096.
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
# 12 "bin/eval_ml_3/parser.mly"
       (Syntax.id)
# 215 "bin/eval_ml_3/parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 12 "bin/eval_ml_3/parser.mly"
       (Syntax.id)
# 222 "bin/eval_ml_3/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and _menhir_box_toplevel = 
  | MenhirBox_toplevel of (Syntax.judgement) [@@unboxed]

let _menhir_action_01 =
  fun i ->
    (
# 74 "bin/eval_ml_3/parser.mly"
         ( ILit i )
# 242 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_02 =
  fun i ->
    (
# 75 "bin/eval_ml_3/parser.mly"
       ( Var i )
# 250 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_03 =
  fun () ->
    (
# 76 "bin/eval_ml_3/parser.mly"
       ( BLit true )
# 258 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_04 =
  fun () ->
    (
# 77 "bin/eval_ml_3/parser.mly"
        ( BLit false )
# 266 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_05 =
  fun e ->
    (
# 78 "bin/eval_ml_3/parser.mly"
                       ( e )
# 274 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_06 =
  fun c e t ->
    (
# 79 "bin/eval_ml_3/parser.mly"
                                    ( IfExp (c, t, e) )
# 282 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_07 =
  fun e1 e2 ->
    (
# 70 "bin/eval_ml_3/parser.mly"
                      ( AppExp (e1, e2) )
# 290 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_08 =
  fun e ->
    (
# 71 "bin/eval_ml_3/parser.mly"
          ( e )
# 298 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_09 =
  fun e ->
    (
# 45 "bin/eval_ml_3/parser.mly"
            ( e )
# 306 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_10 =
  fun e x ->
    (
# 48 "bin/eval_ml_3/parser.mly"
                           ( FunExp (x, e) )
# 314 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_11 =
  fun e ->
    (
# 49 "bin/eval_ml_3/parser.mly"
            ( e )
# 322 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_12 =
  fun l r ->
    (
# 57 "bin/eval_ml_3/parser.mly"
                       ( BinOp (Lt, l, r) )
# 330 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_13 =
  fun e ->
    (
# 58 "bin/eval_ml_3/parser.mly"
           ( e )
# 338 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_14 =
  fun e1 e2 x ->
    (
# 52 "bin/eval_ml_3/parser.mly"
                                 ( LetExp (x, e1, e2) )
# 346 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_15 =
  fun e1 e2 x y ->
    (
# 53 "bin/eval_ml_3/parser.mly"
                                                    ( LetRecExp (x, y, e1, e2) )
# 354 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_16 =
  fun e ->
    (
# 54 "bin/eval_ml_3/parser.mly"
           ( e )
# 362 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_17 =
  fun l r ->
    (
# 66 "bin/eval_ml_3/parser.mly"
                         ( BinOp (Mult, l, r) )
# 370 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_18 =
  fun e ->
    (
# 67 "bin/eval_ml_3/parser.mly"
            ( e )
# 378 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_19 =
  fun l r ->
    (
# 61 "bin/eval_ml_3/parser.mly"
                        ( BinOp (Plus, l, r) )
# 386 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_20 =
  fun l r ->
    (
# 62 "bin/eval_ml_3/parser.mly"
                         ( BinOp (Minus, l, r) )
# 394 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_21 =
  fun e ->
    (
# 63 "bin/eval_ml_3/parser.mly"
          ( e )
# 402 "bin/eval_ml_3/parser.ml"
     : (Syntax.exp))

let _menhir_action_22 =
  fun e v x ->
    (
# 39 "bin/eval_ml_3/parser.mly"
                                                                  ( ProcV (x, e, v) )
# 410 "bin/eval_ml_3/parser.ml"
     : (Syntax.exval))

let _menhir_action_23 =
  fun e v x y ->
    (
# 42 "bin/eval_ml_3/parser.mly"
                                                                              ( RecProcV (x, y, e, v) )
# 418 "bin/eval_ml_3/parser.ml"
     : (Syntax.exval))

let _menhir_action_24 =
  fun i x ->
    (
# 32 "bin/eval_ml_3/parser.mly"
                 ( (x, IntV i) )
# 426 "bin/eval_ml_3/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_25 =
  fun x ->
    (
# 33 "bin/eval_ml_3/parser.mly"
               ( (x, BoolV true) )
# 434 "bin/eval_ml_3/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_26 =
  fun x ->
    (
# 34 "bin/eval_ml_3/parser.mly"
                ( (x, BoolV false) )
# 442 "bin/eval_ml_3/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_27 =
  fun p x ->
    (
# 35 "bin/eval_ml_3/parser.mly"
                      ( (x, p) )
# 450 "bin/eval_ml_3/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_28 =
  fun r x ->
    (
# 36 "bin/eval_ml_3/parser.mly"
                         ( (x, r) )
# 458 "bin/eval_ml_3/parser.ml"
     : (string * Syntax.exval))

let _menhir_action_29 =
  fun hd tl ->
    (
# 27 "bin/eval_ml_3/parser.mly"
                                ( hd::tl )
# 466 "bin/eval_ml_3/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_30 =
  fun v ->
    (
# 28 "bin/eval_ml_3/parser.mly"
              ( v::[] )
# 474 "bin/eval_ml_3/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_31 =
  fun () ->
    (
# 29 "bin/eval_ml_3/parser.mly"
  ( [] )
# 482 "bin/eval_ml_3/parser.ml"
     : ((string * Syntax.exval) list))

let _menhir_action_32 =
  fun e i v ->
    (
# 20 "bin/eval_ml_3/parser.mly"
                                           ( EvalExp (v, e, IntV i) )
# 490 "bin/eval_ml_3/parser.ml"
     : (Syntax.judgement))

let _menhir_action_33 =
  fun e v ->
    (
# 21 "bin/eval_ml_3/parser.mly"
                                         ( EvalExp (v, e, BoolV true) )
# 498 "bin/eval_ml_3/parser.ml"
     : (Syntax.judgement))

let _menhir_action_34 =
  fun e v ->
    (
# 22 "bin/eval_ml_3/parser.mly"
                                          ( EvalExp (v, e, BoolV false) )
# 506 "bin/eval_ml_3/parser.ml"
     : (Syntax.judgement))

let _menhir_action_35 =
  fun e p v ->
    (
# 23 "bin/eval_ml_3/parser.mly"
                                                ( EvalExp (v, e, p) )
# 514 "bin/eval_ml_3/parser.ml"
     : (Syntax.judgement))

let _menhir_action_36 =
  fun e r v ->
    (
# 24 "bin/eval_ml_3/parser.mly"
                                                   ( EvalExp (v, e, r) )
# 522 "bin/eval_ml_3/parser.ml"
     : (Syntax.judgement))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ARROW ->
        "ARROW"
    | COMMA ->
        "COMMA"
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

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_goto_toplevel : type  ttv_stack. ttv_stack -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      MenhirBox_toplevel _v
  
  let rec _menhir_run_102 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let MenhirCell1_Expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
      let p = _v in
      let _v = _menhir_action_35 e p v in
      _menhir_goto_toplevel _menhir_stack _v
  
  let rec _menhir_run_101 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      let MenhirCell1_Expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
      let r = _v in
      let _v = _menhir_action_36 e r v in
      _menhir_goto_toplevel _menhir_stack _v
  
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
              let _v = _menhir_action_25 x in
              _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | LPAREN ->
              let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
              let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, MenhirState002) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ID _v ->
                  _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004
              | RPAREN ->
                  let _v = _menhir_action_31 () in
                  _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004 _tok
              | _ ->
                  _eRR ())
          | INTV _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (x, i) = (_v, _v_2) in
              let _v = _menhir_action_24 i x in
              _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v in
              let _v = _menhir_action_26 x in
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
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState070
          | RPAREN | TURNSTILE ->
              let _v = _menhir_action_31 () in
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | RPAREN | TURNSTILE ->
          let v = _v in
          let _v = _menhir_action_30 v in
          _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_071 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_SingleVar -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SingleVar (_menhir_stack, _menhir_s, hd) = _menhir_stack in
      let tl = _v in
      let _v = _menhir_action_29 hd tl in
      _menhir_goto_VarList _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_VarList : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState082 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState004 ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_083 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
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
                                          _menhir_run_036_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | LPAREN ->
                                          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
                                      | LET ->
                                          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
                                      | INTV _v_3 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_3 in
                                          let _v = _menhir_action_01 i in
                                          _menhir_run_036_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | IF ->
                                          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
                                      | ID _v_5 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_5 in
                                          let _v = _menhir_action_02 i in
                                          _menhir_run_036_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | FUN ->
                                          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
                                      | FALSE ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_04 () in
                                          _menhir_run_036_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                  | ID _v_8 ->
                      let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_8) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ARROW ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | TRUE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_03 () in
                              _menhir_run_036_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | LPAREN ->
                              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
                          | LET ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
                          | INTV _v_10 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_10 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_036_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
                          | ID _v_12 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_12 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_036_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_036_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_036_spec_091 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState091 _tok
  
  and _menhir_run_037 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState037
      | INTV _v_1 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_1 in
          let _v = _menhir_action_01 i in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState037
      | ID _v_3 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_3 in
          let _v = _menhir_action_02 i in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN ->
          let e = _v in
          let _v = _menhir_action_18 e in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_035 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_AppExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AppExpr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_07 e1 e2 in
      _menhir_goto_AppExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_AppExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState078 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState022 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState048 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState028 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState043 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState038 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState031 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState033 ->
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_034 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState034
      | INTV _v_1 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_1 in
          let _v = _menhir_action_01 i in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState034
      | ID _v_3 ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v_3 in
          let _v = _menhir_action_02 i in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_AppExpr (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | ELSE | EVALTO | IN | LT | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN ->
          let MenhirCell1_MExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_17 l r in
          _menhir_goto_MExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_036_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | LET ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_036_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_036_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState015
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_036_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_015 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState015 _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
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
                                  _menhir_run_036_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | LPAREN ->
                                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState022
                              | LET ->
                                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState022
                              | INTV _v_2 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_2 in
                                  let _v = _menhir_action_01 i in
                                  _menhir_run_036_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | IF ->
                                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState022
                              | ID _v_4 ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let i = _v_4 in
                                  let _v = _menhir_action_02 i in
                                  _menhir_run_036_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                              | FUN ->
                                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState022
                              | FALSE ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  let _v = _menhir_action_04 () in
                                  _menhir_run_036_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                  _menhir_run_036_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | LPAREN ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState056
              | LET ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState056
              | INTV _v_8 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_8 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_036_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState056
              | ID _v_10 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_10 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_036_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState056
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_036_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_022 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState022 _tok
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_036_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
      | LET ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_036_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_036_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FUN ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_036_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_024 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState024 _tok
  
  and _menhir_run_026 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _menhir_box_toplevel =
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
                  _menhir_run_036_spec_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | LPAREN ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState028
              | LET ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState028
              | INTV _v_1 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_1 in
                  let _v = _menhir_action_01 i in
                  _menhir_run_036_spec_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | IF ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState028
              | ID _v_3 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let i = _v_3 in
                  let _v = _menhir_action_02 i in
                  _menhir_run_036_spec_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | FUN ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState028
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_04 () in
                  _menhir_run_036_spec_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_028 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState028 _tok
  
  and _menhir_run_036_spec_056 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState056 _tok
  
  and _menhir_goto_MExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState096 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState022 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState048 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState043 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState028 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState038 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState031 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_040 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE ->
          let e = _v in
          let _v = _menhir_action_21 e in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_033 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_036_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_036_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState033
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_036_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_036_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_033 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_MExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState033 _tok
  
  and _menhir_goto_PMExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState043 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState022 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState048 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState028 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_044 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MULT | RBRACKET | RPAREN | THEN | TRUE ->
          let MenhirCell1_LTExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_12 l r in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_031 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_036_spec_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_036_spec_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_036_spec_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_036_spec_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_031 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState031 _tok
  
  and _menhir_run_038 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_03 () in
          _menhir_run_036_spec_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState038
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_01 i in
          _menhir_run_036_spec_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | IF ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState038
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let i = _v in
          let _v = _menhir_action_02 i in
          _menhir_run_036_spec_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_04 () in
          _menhir_run_036_spec_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_036_spec_038 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState038 _tok
  
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
              _menhir_run_036_spec_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState043
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState043
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | MINUS | MULT | PLUS | RBRACKET | RPAREN | THEN | TRUE ->
          let e = _v in
          let _v = _menhir_action_16 e in
          _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_036_spec_043 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LTExpr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState043 _tok
  
  and _menhir_goto_LetExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_11 e in
      _menhir_goto_FunExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_FunExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState096 ->
          _menhir_run_046_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState091 ->
          _menhir_run_046_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState078 ->
          _menhir_run_046_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState066 ->
          _menhir_run_046_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_046_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState015 ->
          _menhir_run_046_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState058 ->
          _menhir_run_046_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState056 ->
          _menhir_run_046_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_046_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState022 ->
          _menhir_run_046_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState050 ->
          _menhir_run_046_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState048 ->
          _menhir_run_046_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState024 ->
          _menhir_run_046_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState028 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_046_spec_096 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_22 e v x in
          _menhir_goto_ProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_ProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState080 ->
          _menhir_run_102 _menhir_stack _v
      | MenhirState002 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_075 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let p = _v in
      let _v = _menhir_action_27 p x in
      _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046_spec_091 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_23 e v x y in
          _menhir_goto_RecProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_RecProcVExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState080 ->
          _menhir_run_101 _menhir_stack _v
      | MenhirState002 ->
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_074 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let r = _v in
      let _v = _menhir_action_28 r x in
      _menhir_goto_SingleVar _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046_spec_078 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | EVALTO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
              let e = _v in
              let _v = _menhir_action_33 e v in
              _menhir_goto_toplevel _menhir_stack _v
          | LPAREN ->
              let _menhir_stack = MenhirCell1_Expr (_menhir_stack, MenhirState078, _v) in
              let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, MenhirState080) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ID _v ->
                  _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState082
              | RPAREN ->
                  let _v = _menhir_action_31 () in
                  _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState082 _tok
              | _ ->
                  _eRR ())
          | INTV _v_2 ->
              let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
              let (i, e) = (_v_2, _v) in
              let _v = _menhir_action_32 e i v in
              _menhir_goto_toplevel _menhir_stack _v
          | FALSE ->
              let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
              let e = _v in
              let _v = _menhir_action_34 e v in
              _menhir_goto_toplevel _menhir_stack _v
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_066 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_22 e v x in
          _menhir_goto_ProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_013 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_VarList (_menhir_stack, _, v) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_23 e v x y in
          _menhir_goto_RecProcVExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_015 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_05 e in
          _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_AExpr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState078 ->
          _menhir_run_036_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState096 ->
          _menhir_run_036_spec_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState091 ->
          _menhir_run_036_spec_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState066 ->
          _menhir_run_036_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState013 ->
          _menhir_run_036_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState015 ->
          _menhir_run_036_spec_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState056 ->
          _menhir_run_036_spec_056 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState058 ->
          _menhir_run_036_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState022 ->
          _menhir_run_036_spec_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_036_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState024 ->
          _menhir_run_036_spec_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState048 ->
          _menhir_run_036_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState050 ->
          _menhir_run_036_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState028 ->
          _menhir_run_036_spec_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState043 ->
          _menhir_run_036_spec_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState038 ->
          _menhir_run_036_spec_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState031 ->
          _menhir_run_036_spec_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState033 ->
          _menhir_run_036_spec_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState037 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState034 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_036_spec_078 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_VarList -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState078 _tok
  
  and _menhir_run_036_spec_096 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState096 _tok
  
  and _menhir_run_036_spec_066 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState066 _tok
  
  and _menhir_run_036_spec_013 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LPAREN, _menhir_box_toplevel) _menhir_cell1_VarList _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState013 _tok
  
  and _menhir_run_036_spec_058 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState058 _tok
  
  and _menhir_run_036_spec_053 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState053 _tok
  
  and _menhir_run_036_spec_048 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState048 _tok
  
  and _menhir_run_036_spec_050 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState050 _tok
  
  and _menhir_run_046_spec_058 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_14 e1 e2 x in
      _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046_spec_056 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, MenhirState056, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_036_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState058
          | LET ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState058
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState058
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState058
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_053 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let MenhirCell1_Expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, y) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_15 e1 e2 x y in
      _menhir_goto_LetExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046_spec_022 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_LET _menhir_cell0_ID _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, MenhirState022, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_036_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | LET ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState053
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_050 : type  ttv_stack. (((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let MenhirCell1_Expr (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_Expr (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_06 c e t in
      _menhir_goto_AExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046_spec_048 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF, _menhir_box_toplevel) _menhir_cell1_Expr -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, MenhirState048, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_036_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState050
          | LET ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState050
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState050
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState050
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_050 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_046_spec_024 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_IF -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _v =
        let e = _v in
        _menhir_action_09 e
      in
      let _menhir_stack = MenhirCell1_Expr (_menhir_stack, MenhirState024, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_036_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
          | LET ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_045 : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_FUN _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_10 e x in
      _menhir_goto_FunExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_030 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_PMExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MULT | RBRACKET | RPAREN | THEN | TRUE ->
          let e = _v in
          let _v = _menhir_action_13 e in
          _menhir_goto_LTExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_039 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_20 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_032 : type  ttv_stack. ((ttv_stack, _menhir_box_toplevel) _menhir_cell1_PMExpr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MULT ->
          let _menhir_stack = MenhirCell1_MExpr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EVALTO | FALSE | ID _ | IF | IN | INTV _ | LPAREN | LT | MINUS | PLUS | RBRACKET | RPAREN | THEN | TRUE ->
          let MenhirCell1_PMExpr (_menhir_stack, _menhir_s, l) = _menhir_stack in
          let r = _v in
          let _v = _menhir_action_19 l r in
          _menhir_goto_PMExpr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_077 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_VarList (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | TURNSTILE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_03 () in
              _menhir_run_036_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
          | LET ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
          | INTV _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_1 in
              let _v = _menhir_action_01 i in
              _menhir_run_036_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | IF ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
          | ID _v_3 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let i = _v_3 in
              let _v = _menhir_action_02 i in
              _menhir_run_036_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | FUN ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState078
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_04 () in
              _menhir_run_036_spec_078 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                                          _menhir_run_036_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | LPAREN ->
                                          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | LET ->
                                          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | INTV _v_3 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_3 in
                                          let _v = _menhir_action_01 i in
                                          _menhir_run_036_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | IF ->
                                          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | ID _v_5 ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let i = _v_5 in
                                          let _v = _menhir_action_02 i in
                                          _menhir_run_036_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                                      | FUN ->
                                          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
                                      | FALSE ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          let _v = _menhir_action_04 () in
                                          _menhir_run_036_spec_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
                  | ID _v_8 ->
                      let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_8) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ARROW ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | TRUE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_03 () in
                              _menhir_run_036_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | LPAREN ->
                              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
                          | LET ->
                              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
                          | INTV _v_10 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_10 in
                              let _v = _menhir_action_01 i in
                              _menhir_run_036_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | IF ->
                              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
                          | ID _v_12 ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let i = _v_12 in
                              let _v = _menhir_action_02 i in
                              _menhir_run_036_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                          | FUN ->
                              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
                          | FALSE ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              let _v = _menhir_action_04 () in
                              _menhir_run_036_spec_066 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
          let _v = _menhir_action_31 () in
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
