
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | PLUS
    | MULT
    | IS
    | INTV of (
# 7 "bin/nat/parser.mly"
       (int)
# 18 "bin/nat/parser.ml"
  )
  
end

include MenhirBasics

# 1 "bin/nat/parser.mly"
  
  open Syntax

# 29 "bin/nat/parser.ml"

type ('s, 'r) _menhir_state

and _menhir_box_toplevel = 
  | MenhirBox_toplevel of (Syntax.judgement) [@@unboxed]

let _menhir_action_1 =
  fun n1 n2 n3 ->
    (
# 14 "bin/nat/parser.mly"
                                  ( PlusExp (n1, n2, n3) )
# 41 "bin/nat/parser.ml"
     : (Syntax.judgement))

let _menhir_action_2 =
  fun n1 n2 n3 ->
    (
# 15 "bin/nat/parser.mly"
                                  ( MultExp (n1, n2, n3) )
# 49 "bin/nat/parser.ml"
     : (Syntax.judgement))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | INTV _ ->
        "INTV"
    | IS ->
        "IS"
    | MULT ->
        "MULT"
    | PLUS ->
        "PLUS"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_goto_toplevel : type  ttv_stack. ttv_stack -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _v ->
      MenhirBox_toplevel _v
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INTV _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | IS ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | INTV _v_1 ->
                          let (n3, n2, n1) = (_v_1, _v_0, _v) in
                          let _v = _menhir_action_1 n1 n2 n3 in
                          _menhir_goto_toplevel _menhir_stack _v
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | MULT ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INTV _v_2 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | IS ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | INTV _v_3 ->
                          let (n3, n2, n1) = (_v_3, _v_2, _v) in
                          let _v = _menhir_action_2 n1 n2 n3 in
                          _menhir_goto_toplevel _menhir_stack _v
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
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
