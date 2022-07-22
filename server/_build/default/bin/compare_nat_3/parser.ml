
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | LT
    | INTV of (
# 6 "bin/compare_nat_3/parser.mly"
       (int)
# 16 "bin/compare_nat_3/parser.ml"
  )
  
end

include MenhirBasics

# 1 "bin/compare_nat_3/parser.mly"
  
  open Syntax

# 27 "bin/compare_nat_3/parser.ml"

type ('s, 'r) _menhir_state

and _menhir_box_toplevel = 
  | MenhirBox_toplevel of (Syntax.judgement) [@@unboxed]

let _menhir_action_1 =
  fun n1 n2 ->
    (
# 14 "bin/compare_nat_3/parser.mly"
                     ( LessThanExp (n1, n2) )
# 39 "bin/compare_nat_3/parser.ml"
     : (Syntax.judgement))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | INTV _ ->
        "INTV"
    | LT ->
        "LT"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_0 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INTV _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LT ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INTV _v_0 ->
                  let (n2, n1) = (_v_0, _v) in
                  let _v = _menhir_action_1 n1 n2 in
                  MenhirBox_toplevel _v
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
    let MenhirBox_toplevel v = _menhir_run_0 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
